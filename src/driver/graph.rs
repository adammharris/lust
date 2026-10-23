// Dependency graph nodes, read recording, and slot identity (docs/ARCH.md
// sections 4.2, 8.1, and 8.2; serial refactor S7).
//
// This file owns the frozen query surface of section 8.2: the `Reads` sink, its
// keys (`Binding`, `MethodSet`, `ImplSet`, `Sig`, `Layout`, `Checked`,
// `TraitInScope`), and the
// query functions on `Program` that log to it. Wave A packages (W-CORELANG,
// W-TRAITS-CORE, W-MACRO) code against these functions. Today's single-file,
// single-module resolver sits behind them; W-RESOLVE replaces that resolver
// with the module tree and import worklist of section 1.3 without changing any
// caller. S7 was record-only. W-DRIVER (wave A) turned reads into reuse
// for signature-only edits first; phase 2 extends the same walk to full
// mode: `Program::reads_dirty` below recomputes each recorded node's
// fingerprint in the new program, and compile.rs drops a recheck
// candidate only when its body is unchanged and every recorded read
// still matches. `Sig` fingerprints hash the layouts of named Adts
// deeply, and `Layout` has its own fingerprint, so type and impl edits
// dirty exactly the bodies that read through them.
//
// Fingerprints here hash normalized content only: name strings, stable def
// path hashes, and type structure. They never hash a `Sym`, a `Ty`, an
// `ArgsId`, or any other session-local id (section 8.1).
use crate::ast::SelfKind;
use crate::check::collect::{AdtDef, FnInfo, Program, VariantShape};
use crate::def::{DefId, DiskDefId, LocalDefId, StableCrateHash};
use crate::intern::{FxHasher, FxMap, Sym};
use crate::resolve::imports::{ResolvedTables, VisKind};
use crate::ty::defs::{DefData, DefKind as DefsKind, ModuleId, ROOT_MODULE};
use crate::ty::*;
use std::hash::{Hash, Hasher};

/// A node's 64-bit fingerprint over normalized content (section 8.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Fingerprint(pub u64);

/// One of Rust's three item namespaces (section 1.3). Modules live in `Type`.
/// Variant order is frozen; add nothing here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Namespace {
    Type,
    Value,
    Macro,
}

/// A module as a read key names it: by `ResolvedTables::module_key` (crate
/// root and name path), which stands across the resolves of a session. A
/// `ModuleId` does not: ids follow insertion order, so a module inserted
/// before another takes the other's old id, and a stored key would ask that
/// module (Sol's const-body review, blocker 2). Without resolver tables, the
/// id itself (`bare`, top bit set).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModKey(pub u64);

impl ModKey {
    /// The key of module `m` of a program with no resolver tables.
    pub fn bare(m: ModuleId) -> ModKey {
        ModKey(1 << 63 | m.0 as u64)
    }
}

/// The key of one `Binding` node: one name in one module and namespace.
/// Reads are per name, never per scope (section 8.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BindingKey {
    pub module: ModKey,
    pub ns: Namespace,
    pub name: Sym,
}

/// The answer of a binding query. A tuple or unit struct answers in both the
/// type and the value namespace, with the Adt's own def: the constructor is not
/// a separate def (section 1.3). Local variables, primitives, and `Self` are
/// not module bindings and never appear here; callers resolve those scope
/// layers before they ask for a binding.
#[allow(dead_code)] // `Ambiguous` is produced by the glob worklist (W-RESOLVE).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingRes {
    Def(DefId),
    /// Two glob imports bring different defs under this name. An error only if
    /// code uses the name (section 1.3). Never produced by today's resolver.
    Ambiguous,
    Absent,
}

/// A receiver form probed by method resolution, in Rust's probe order
/// (section 2.10 step 2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ReceiverForm {
    Value,
    Ref,
    RefMut,
}

impl ReceiverForm {
    /// The probe order of section 2.10 step 2.
    pub const PROBE_ORDER: [ReceiverForm; 3] = [ReceiverForm::Value, ReceiverForm::Ref, ReceiverForm::RefMut];
}

/// The head of a receiver type: the part a method or impl bucket keys on.
/// References name their pointee head; the reference distinction rides in
/// `ReceiverForm`. `Unknown` is the head of a type with no bucket yet (an
/// unbound inference variable, a generic parameter): probes against it still
/// record a read, so a later impl or method rechecks the body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Head {
    Adt(DefId),
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Str,
    Slice,
    Array,
    Tuple,
    Never,
    Unit,
    Unknown,
}

impl Head {
    /// The head of a type, through references and raw pointers.
    pub fn of(tys: &impl TyIntern, t: Ty) -> Head {
        match tys.kind(t) {
            TyKind::Adt(def, _) => Head::Adt(def),
            TyKind::Int(i) => Head::Int(i),
            TyKind::Float(f) => Head::Float(f),
            TyKind::Bool => Head::Bool,
            TyKind::Char => Head::Char,
            TyKind::Str => Head::Str,
            TyKind::Slice(_) => Head::Slice,
            TyKind::Array(..) => Head::Array,
            TyKind::Tuple(_) => Head::Tuple,
            TyKind::Never => Head::Never,
            TyKind::Unit => Head::Unit,
            TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) => Head::of(tys, inner),
            _ => Head::Unknown,
        }
    }
}

/// The key of one `MethodSet` node: the candidate set for one probe.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MethodSetKey {
    pub head: Head,
    pub name: Sym,
    pub form: ReceiverForm,
}

/// One method candidate. `trait_` is `None` for an inherent method.
/// `receiver` is `None` for an associated function without `self`: such a
/// candidate surfaces only in the `Value` probe, so the caller can report it
/// as "not a method" instead of "no such method". It is never callable as a
/// method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MethodCandidate {
    pub def: DefId,
    pub receiver: Option<ReceiverForm>,
    pub trait_: Option<DefId>,
}

/// The candidate list of one method probe, in probe order (inherent first).
#[derive(Clone, Debug, Default)]
pub struct MethodSet {
    pub candidates: Vec<MethodCandidate>,
}

impl MethodSet {
    /// The first candidate. Method resolution iterates every
    /// candidate and unifies the receiver (section 2.10); this
    /// is for tests that inspect a set.
    #[cfg(test)]
    pub fn first(&self) -> Option<MethodCandidate> {
        self.candidates.first().copied()
    }
}

/// The key of one `ImplSet` node: the impl bucket for one trait and Self head.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ImplSetKey {
    pub trait_: DefId,
    pub head: Head,
}

/// The impl defs in one bucket, in no promised order. Only the impls of a
/// user trait (one written in this crate, with no associated const) fill
/// buckets: those impls are outside the trait-system key (driver/
/// gen_reuse.rs `trait_key`), so these reads are what rechecks a body when
/// one is added, removed, or edited. Any other trait's bucket reads as
/// empty; its impls stay under the trait-system key.
#[derive(Clone, Debug, Default)]
pub struct ImplSet {
    pub impls: Vec<DefId>,
}

/// One recorded read's key. Frozen (section 9.2): new node kinds go at the
/// end only.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ReadKey {
    Binding(BindingKey),
    MethodSet(MethodSetKey),
    ImplSet(ImplSetKey),
    Sig(DefId),
    Layout(DefId),
    /// The drop-check constraint of one Adt template, in its own params
    /// (check/dropck.rs: rustc's `adt_dtorck_constraint`): the drop check of
    /// a body local follows each Adt's fields, behind pointers too. The
    /// fingerprint is the constraint, so a field edit that adds no
    /// constraint (a `u32`) moves nothing.
    DropCk(DefId),
    /// A mono call edge to the checked body of a def (section 8.2).
    Checked(DefId),
    /// Whether a user trait is defined in or imported into one module,
    /// under any name (`as _` included): method probes ask it for each
    /// candidate trait. A `use` edit flips it without touching any
    /// binding the body names. The fingerprint is the answer.
    TraitInScope(ModKey, DefId),
    /// Whether one module imports the std item `<std|core|alloc>::<module>::<name>` at
    /// module level (any rename, `as _`), or with `name` the glob marker `*`, a glob of
    /// that std module. Method probes ask it for the std traits a call by name needs in
    /// scope (`std::ops::Add`, `fmt::Display`, `hash::Hash`): removing the import flips
    /// the answer and no binding the body names (Sol's read-gap review r06).
    StdImport(ModKey, Sym, Sym),
    /// The derive list of one local Adt template (PLAN R12): every
    /// `Program::derives_of` call inside a body check, and every selection
    /// of a derivable trait whose Self head is the Adt (a derived impl is a
    /// synthetic record, which no `ImplSet` read covers). The
    /// fingerprint is the list itself (`derives_fingerprint`).
    Derives(DefId),
    /// Some traits of the derive list of one local Adt template (sigedit
    /// P3.2): a reader that asked only those (`Program::derive_has`, a
    /// derivable trait's selection) records their bits
    /// (check/derive_delta.rs `bit`). The fingerprint is those flags.
    DeriveBits(DefId, u16),
    /// The written impls of std and lang traits (traits outside `ImplSet`
    /// reads) whose trait refs name one user Adt template
    /// (`ImplIndex::impls_naming`). Format glue, `?`, `for` loops,
    /// operators, conversions, `Deref`, and drop glue look these impls up
    /// with no `ImplSet` read, always for a type the body names; so a body
    /// records this read for each Adt its types name
    /// (`record_type_lang_reads`), and for each Adt of such an impl the
    /// index hands out (traits/index.rs `get`). The fingerprint is the
    /// impls' content (`lang_impls_fingerprint`).
    LangImpls(DefId),
    /// The deep structure of one Adt template, through pointers and
    /// collections: what auto traits (`Send`, `Sync`, `Unpin`) and derive
    /// glue answers (`Clone`, `PartialEq`, ...) read, recorded by those
    /// structural walks (`Program::record_structure_reads`). `Layout` is
    /// the by-value part. The fingerprint is the full deep content
    /// (`structure_fingerprint`).
    Structure(DefId),
    /// One structural answer about a user Adt with no generic params
    /// (`answer::AUTO`: its `Send`, `Sync`, and `Unpin`; or one derive glue
    /// answer, `answer::CLONE`...), which an auto trait or glue walk over a
    /// type that holds the Adt reads in place of its `Structure`. The
    /// fingerprint is the answer (`answer_fingerprint`), so an edit deep
    /// inside the Adt that keeps the answer dirties no reader.
    Answer(DefId, u8),
    /// The visibility of the inherent associated item `name` of one Adt
    /// (`ResolvedTables::assoc_vis`: written visibility and module), which
    /// a method call or a `Type::item` path checks (`Ctx::check_assoc_vis`).
    /// The Adt's `Sig` leaves these entries out, so a method added to a
    /// type does not dirty the callers of its other methods. The
    /// fingerprint is the entry; no entry is a failed read.
    AssocVis(DefId, Sym),
}

/// One recorded read: the fingerprint the node had when it was read, and
/// whether the answer was "no such thing" (a failed lookup, a first-class
/// read per section 8.2 rule 3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Read {
    pub fingerprint: Fingerprint,
    pub failed: bool,
}

/// Every read key one owner's stored read sets name, each once: a frozen
/// set (`Reads::freeze`) names its keys by index here, 4 bytes for a
/// 48-byte key. Keys are never removed, so a table lives as long as the
/// sets that name it: `Caches::read_keys` (the slot read sets) and
/// `GenReuse`'s own (its entries).
#[derive(Debug)]
pub(crate) struct ReadKeys {
    /// This table's identity: a frozen set keeps it, and a read with
    /// another table fails closed (see `Reads::check_table`).
    id: u64,
    keys: Vec<ReadKey>,
    ids: FxMap<ReadKey, u32>,
}

impl Default for ReadKeys {
    fn default() -> ReadKeys {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        // Unique across processes too: a front image restores tables made
        // by earlier processes beside new ones.
        let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_nanos() as u64);
        let id = t ^ (std::process::id() as u64).rotate_left(40) ^ NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed).rotate_left(20);
        ReadKeys { id: id | 1, keys: Vec::new(), ids: FxMap::default() }
    }
}

impl ReadKeys {
    /// The index of `key`, added when new.
    fn index(&mut self, key: ReadKey) -> u32 {
        match self.ids.entry(key) {
            std::collections::hash_map::Entry::Occupied(e) => *e.get(),
            std::collections::hash_map::Entry::Vacant(v) => {
                let i = self.keys.len() as u32;
                self.keys.push(key);
                *v.insert(i)
            }
        }
    }

    /// How many keys the table holds.
    pub(crate) fn len(&self) -> usize {
        self.keys.len()
    }

    /// The table for a set that is never frozen (a sink, or a set stored
    /// outside the tables: `Program::const_body_reads`): it holds no keys,
    /// so a frozen set read with it fails closed.
    pub(crate) fn none() -> &'static ReadKeys {
        static NONE: std::sync::OnceLock<ReadKeys> = std::sync::OnceLock::new();
        NONE.get_or_init(ReadKeys::default)
    }
}

/// One read of a frozen set: its key's index in the set's `ReadKeys`, and
/// the read (16 bytes, where a hash table entry took ~100).
#[derive(Clone, Copy, Debug)]
struct FrozenRead {
    key: u32,
    failed: bool,
    fingerprint: Fingerprint,
}

/// The read sink one stage run collects into (section 8.2). One sink per
/// checked body today; collect and mono get their own when their queries
/// land. Recording the same key twice in one run is a no-op: query answers
/// cannot change while the program tables are frozen for body checking.
#[derive(Clone, Debug, Default)]
pub struct Reads {
    map: FxMap<ReadKey, Read>,
    /// A stored set's reads (`freeze`), sorted by key index, with `map`
    /// empty: a set that is done recording keeps no hash table and no keys
    /// of its own (the image keeps ~1 GB of read sets).
    frozen: Box<[FrozenRead]>,
    /// The `ReadKeys::id` of the table `frozen` indexes, or 0.
    table: u64,
    /// Set for a sink whose reads nobody will replay (a one-shot process
    /// exits after this compile): it records nothing and computes no
    /// fingerprints.
    off: bool,
    /// By mode (check, build), the generation of the kept program these
    /// reads last held against (`Program::verified`), or 0: the driver's
    /// keyed walk trusts a key a delta did not move only for a set of the
    /// delta's base program. A new set has none.
    pub(crate) verified: [u64; 2],
}

impl Reads {
    /// An empty sink.
    pub fn new() -> Reads {
        Reads::default()
    }

    /// A sink that records nothing (see `off`).
    pub fn off() -> Reads {
        Reads { off: true, ..Reads::default() }
    }

    /// Records one read. The first record of a key wins.
    pub fn record(&mut self, key: ReadKey, fingerprint: Fingerprint, failed: bool) {
        self.record_with(key, failed, || fingerprint);
    }

    /// Records one read, computing the fingerprint only if the key is new:
    /// a body that asks the same question a hundred times pays for the
    /// fingerprint once. Into a frozen set (with no table here to look up
    /// its keys) the read joins `map` even when the frozen part holds the
    /// key: readers then see that key twice, and a walk that compares both
    /// rechecks at worst. The driver thaws a stored set before it records
    /// into it (`thaw`).
    pub fn record_with(&mut self, key: ReadKey, failed: bool, fingerprint: impl FnOnce() -> Fingerprint) {
        if self.off {
            return;
        }
        if let std::collections::hash_map::Entry::Vacant(v) = self.map.entry(key) {
            v.insert(Read { fingerprint: fingerprint(), failed });
        }
    }

    /// Ends recording for a set that is stored: its reads move into
    /// `frozen`, their keys into `keys`. Every reader sees the same reads.
    pub(crate) fn freeze(&mut self, keys: &mut ReadKeys) {
        if self.map.is_empty() {
            return;
        }
        let mut all = self.thawed(keys);
        all.extend(std::mem::take(&mut self.map));
        let mut frozen: Vec<FrozenRead> =
            all.into_iter().map(|(k, r)| FrozenRead { key: keys.index(k), failed: r.failed, fingerprint: r.fingerprint }).collect();
        // Stable: of a key recorded twice (into a frozen set), the first
        // record stays.
        frozen.sort_by_key(|f| f.key);
        frozen.dedup_by_key(|f| f.key);
        self.frozen = frozen.into_boxed_slice();
        self.table = keys.id;
    }

    /// Moves a frozen set's reads back into `map`, for a record into a
    /// stored set (freeze it again after).
    pub(crate) fn thaw(&mut self, keys: &ReadKeys) {
        // A frozen read is older than any read the map took since: it wins.
        let back = self.thawed(keys);
        self.map.extend(back);
    }

    /// Takes the frozen reads out as (key, read) pairs, in index order.
    fn thawed(&mut self, keys: &ReadKeys) -> Vec<(ReadKey, Read)> {
        self.check_table(keys);
        let out = self.frozen.iter().map(|f| (keys.keys[f.key as usize], Read { fingerprint: f.fingerprint, failed: f.failed })).collect();
        self.frozen = Box::default();
        self.table = 0;
        out
    }

    /// A frozen set read with a table other than its own would answer with
    /// other keys: fail closed.
    fn check_table(&self, keys: &ReadKeys) {
        assert!(self.frozen.is_empty() || self.table == keys.id, "a frozen read set was read with another ReadKeys table");
    }

    /// Records a call edge to a checked body whose *body* (not only its
    /// signature) the reader's result depends on: today, a const fn body
    /// evaluated while checking a body (a const block, an array length).
    /// The fingerprint value does not matter yet: `read_fingerprint`
    /// cannot recompute a body fingerprint, so it reports a sentinel
    /// that never matches and the reader always rechecks when it is a
    /// walk candidate. Mono records the same key with a real body
    /// fingerprint when it lands (W-MONO, wave B).
    pub fn record_checked(&mut self, def: DefId, fingerprint: Fingerprint) {
        self.record(ReadKey::Checked(def), fingerprint, false);
    }

    /// The read recorded for a key, if this run read that node. The frozen
    /// part first: the first record of a key wins.
    pub(crate) fn get(&self, keys: &ReadKeys, key: &ReadKey) -> Option<Read> {
        self.check_table(keys);
        let frozen = keys.ids.get(key).and_then(|&i| self.frozen.binary_search_by_key(&i, |f| f.key).ok());
        match frozen {
            Some(at) => Some(Read { fingerprint: self.frozen[at].fingerprint, failed: self.frozen[at].failed }),
            None => self.map.get(key).copied(),
        }
    }

    /// True if this run read that node.
    pub(crate) fn contains(&self, keys: &ReadKeys, key: &ReadKey) -> bool {
        self.get(keys, key).is_some()
    }

    /// The read this sink recorded for a key: its map only, for a sink
    /// that still records (a frozen set's keys need their table, `get`).
    pub fn recorded(&self, key: &ReadKey) -> Option<Read> {
        self.map.get(key).copied()
    }

    /// Number of reads (a key recorded into a frozen set again counts twice).
    pub fn len(&self) -> usize {
        self.map.len() + self.frozen.len()
    }

    /// True if nothing was read.
    #[allow(dead_code)] // Tests use it.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Every recorded key, in no stable order: nothing may key on it.
    pub(crate) fn keys<'a>(&'a self, keys: &'a ReadKeys) -> impl Iterator<Item = &'a ReadKey> + 'a {
        self.iter(keys).map(|(k, _)| k)
    }

    /// Every recorded (key, read) pair, in no stable order. The dirty walk
    /// (`Program::reads_dirty`) iterates this; order does not matter there.
    pub(crate) fn iter<'a>(&'a self, keys: &'a ReadKeys) -> impl Iterator<Item = (&'a ReadKey, Read)> + 'a {
        self.check_table(keys);
        let frozen = self.frozen.iter().map(|f| (&keys.keys[f.key as usize], Read { fingerprint: f.fingerprint, failed: f.failed }));
        frozen.chain(self.map.iter().map(|(k, r)| (k, *r)))
    }
}

// ---------- Fingerprints ----------

/// The stable crate half a def hashes under in a fingerprint. Local-crate
/// defs use the program's stable crate hash and builtin defs use theirs, so
/// fingerprints match across sessions. A foreign session crate cannot occur
/// today (one crate per session); when W-RESOLVE loads more crates it gives
/// `Program` a crate table and this fallback goes away.
pub(crate) fn def_crate_hash(p: &Program, def: DefId) -> u64 {
    if def.krate == p.krate {
        p.stable_crate.0
    } else if def.krate == BUILTIN_CRATE {
        static BUILTIN: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
        *BUILTIN.get_or_init(|| crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false).0)
    } else {
        def.krate.0 as u64
    }
}

/// Hashes one def by its stable identity: crate hash, then def path hash.
pub(crate) fn hash_def_pub(h: &mut FxHasher, p: &Program, def: DefId) {
    def_crate_hash(p, def).hash(h);
    def.hash.0.hash(h);
}

fn hash_region(h: &mut FxHasher, r: Region) {
    match r {
        Region::Static => 0u8.hash(h),
        Region::Param(i) => (1u8, i).hash(h),
        Region::Bound(i) => (2u8, i).hash(h),
        // Placeholders and region inference variables are proof-local and must
        // never reach a stored signature; hash only the form, never the id.
        Region::Placeholder(_) => 3u8.hash(h),
        Region::Infer(_) => 4u8.hash(h),
        Region::Erased => 5u8.hash(h),
    }
}

fn hash_const(h: &mut FxHasher, tys: &impl TyIntern, c: ConstId) {
    match tys.const_kind(c) {
        ConstKind::Int(v) => (0u8, v).hash(h),
        ConstKind::Bool(b) => (1u8, b).hash(h),
        ConstKind::Char(c) => (2u8, c).hash(h),
        ConstKind::Param(i) => (3u8, i).hash(h),
        ConstKind::Infer(_) => 4u8.hash(h),
    }
}

fn hash_args(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, args: ArgsId) {
    let list = tys.args(args);
    (list.len() as u64).hash(h);
    for a in list {
        hash_arg(h, p, tys, a);
    }
}

fn hash_arg(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, a: &GenericArg) {
    match a {
        GenericArg::Ty(t) => {
            0u8.hash(h);
            hash_ty(h, p, tys, *t);
        }
        GenericArg::Lifetime(r) => {
            1u8.hash(h);
            hash_region(h, *r);
        }
        GenericArg::Const(c) => {
            2u8.hash(h);
            hash_const(h, tys, *c);
        }
    }
}

/// `hash_args` of a primitive builtin method's item type (`ty::prim_fn_def`, check's
/// `prim_item_value`): its second arg is the method name's symbol, numbered by the
/// interner in the order it meets names, which two processes do not share. So the name's
/// text is hashed, and an instance over the item (`opt.map(RefCell::borrow)`) has one key,
/// and one release fn name, in every build.
fn hash_prim_item_args(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, args: ArgsId) {
    let list = tys.args(args);
    (list.len() as u64).hash(h);
    for (i, a) in list.iter().enumerate() {
        let name = match a {
            GenericArg::Const(c) if i == 1 => match tys.const_kind(*c) {
                ConstKind::Int(v) => Some(Sym(v as u32)),
                _ => None,
            },
            _ => None,
        };
        match name {
            Some(name) => (3u8, p.name(name)).hash(h),
            None => hash_arg(h, p, tys, a),
        }
    }
}

fn hash_trait_ref(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, tr: &TraitRef) {
    hash_def_pub(h, p, tr.def);
    hash_args(h, p, tys, tr.args);
    let bindings = tys.bindings(tr.bindings);
    (bindings.len() as u64).hash(h);
    for (assoc, arg) in bindings {
        hash_def_pub(h, p, *assoc);
        match arg {
            GenericArg::Ty(t) => hash_ty(h, p, tys, *t),
            GenericArg::Lifetime(r) => hash_region(h, *r),
            GenericArg::Const(c) => hash_const(h, tys, *c),
        }
    }
}

/// Hashes one predicate: a bound, an associated type equality, or an
/// outlives fact, with defs in stable form.
fn hash_predicate(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, pred: &Predicate) {
    match pred {
        Predicate::Trait(b) => {
            (0u8, b.count).hash(h);
            hash_trait_ref(h, p, tys, &b.value);
        }
        Predicate::AssocEq(b) => {
            (1u8, b.count).hash(h);
            hash_def_pub(h, p, b.value.assoc);
            hash_args(h, p, tys, b.value.trait_args);
            hash_ty(h, p, tys, b.value.ty);
        }
        Predicate::Outlives(a, b) => {
            2u8.hash(h);
            hash_region(h, *a);
            hash_region(h, *b);
        }
        Predicate::TypeOutlives(t, r) => {
            3u8.hash(h);
            hash_ty(h, p, tys, *t);
            hash_region(h, *r);
        }
    }
}

/// Hashes one generics list: parameter kinds (names bind nothing a
/// reader sees) and predicates in source order.
fn hash_generics(h: &mut FxHasher, p: &Program, g: &Generics) {
    (g.params.len() as u64).hash(h);
    for param in &g.params {
        match param.kind {
            ParamKind::Lifetime => 0u8.hash(h),
            ParamKind::Type => 1u8.hash(h),
            ParamKind::Const(t) => {
                2u8.hash(h);
                hash_ty(h, p, &p.tys, t);
            }
        }
    }
    (g.predicates.len() as u64).hash(h);
    for pred in &g.predicates {
        hash_predicate(h, p, &p.tys, pred);
    }
}

/// Hashes one type by structure, with defs in stable form. This is the
/// in-memory fingerprint of section 8.1, not the 8.4 disk form: W-DRIVER owns
/// the disk translation and may reshape it. Kind tags follow `TyKind`
/// declaration order and change only when it grows at the end.
/// `hash_ty` of one type alone, as a value (check/dropck.rs).
pub(crate) fn hash_ty_value(p: &Program, tys: &impl TyIntern, t: Ty) -> u64 {
    let mut h = FxHasher::default();
    hash_ty(&mut h, p, tys, t);
    h.finish()
}

pub(crate) fn hash_ty(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty) {
    match tys.kind(t) {
        TyKind::Error => 0u8.hash(h),
        TyKind::Unit => 1u8.hash(h),
        TyKind::Bool => 2u8.hash(h),
        TyKind::Char => 3u8.hash(h),
        TyKind::Never => 4u8.hash(h),
        TyKind::Int(i) => (5u8, i.name()).hash(h),
        TyKind::Float(f) => (6u8, f.name()).hash(h),
        TyKind::Str => 7u8.hash(h),
        TyKind::Ref(r, m, inner) => {
            8u8.hash(h);
            hash_region(h, r);
            m.is_mut().hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::RawPtr(m, inner) => {
            (9u8, m.is_mut()).hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::Slice(inner) => {
            10u8.hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::Array(inner, n) => {
            11u8.hash(h);
            hash_ty(h, p, tys, inner);
            hash_const(h, tys, n);
        }
        TyKind::Tuple(ts) => {
            12u8.hash(h);
            let list = tys.tys_of(ts);
            (list.len() as u64).hash(h);
            for e in list {
                hash_ty(h, p, tys, *e);
            }
        }
        TyKind::Adt(def, args) => {
            13u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::FnPtr(sig) => {
            14u8.hash(h);
            let sig = tys.sig(sig);
            sig.count.hash(h);
            (sig.value.is_unsafe, sig.value.extern_c, sig.value.free_slots, sig.value.free_region, sig.value.binders).hash(h);
            for e in tys.tys_of(sig.value.inputs) {
                hash_ty(h, p, tys, *e);
            }
            hash_ty(h, p, tys, sig.value.output);
        }
        TyKind::FnDef(def, args) => {
            15u8.hash(h);
            hash_def_pub(h, p, def);
            if def == crate::ty::prim_fn_def() {
                hash_prim_item_args(h, p, tys, args);
            } else {
                hash_args(h, p, tys, args);
            }
        }
        TyKind::Closure(def, args) => {
            16u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Dyn(bounds, r) => {
            17u8.hash(h);
            hash_region(h, r);
            let b = tys.dyn_bounds(bounds);
            match &b.principal {
                Some(pr) => {
                    pr.count.hash(h);
                    hash_trait_ref(h, p, tys, &pr.value);
                }
                None => u32::MAX.hash(h),
            }
            (b.supertraits.len() as u64).hash(h);
            for st in &b.supertraits {
                st.count.hash(h);
                hash_trait_ref(h, p, tys, &st.value);
            }
            (b.auto.send, b.auto.sync, b.auto.unpin).hash(h);
        }
        TyKind::Opaque(def, args) => {
            18u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Param(i) => (19u8, i.0).hash(h),
        TyKind::Projection(assoc, args) => {
            20u8.hash(h);
            hash_def_pub(h, p, assoc.0);
            hash_args(h, p, tys, args);
        }
        // A body-local inference variable has no stable content; signatures
        // never hold one. Hash only the integer-variable form.
        TyKind::Infer(v) => (21u8, v.is_int()).hash(h),
    }
}

/// The structural fingerprint of one type in this program's global store.
/// Mono's per-arg layout reads (section 8.2) are its first production user.
#[allow(dead_code)]
fn ty_fingerprint(p: &Program, t: Ty) -> Fingerprint {
    let mut h = FxHasher::default();
    hash_ty(&mut h, p, &p.tys, t);
    Fingerprint(h.finish())
}

/// Every Adt def named inside one type, in walk order (duplicates kept;
/// the caller dedups through its cycle stack). FnDef, Closure, Opaque,
/// and Projection defs are not Adt layouts and do not appear here: their
/// content is covered by their own `Sig` nodes when a body reads them.
pub(crate) fn collect_adt_defs(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<DefId>) {
    collect_adt_defs_where(p, tys, t, out, &|_| false)
}

/// Which answer a `Layout` read stands behind (`Program::record_layout_reads_for`):
/// the pointers that answer stops at, whatever they point at.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Behind {
    /// `Clone`: a reference, raw pointer, fn pointer, `Rc`, `Arc`, or
    /// `Weak` clones (or not, for `&mut`) without its target.
    Clone,
    /// `Send` and `Sync`: a raw pointer, `Rc`, or `rc::Weak` has neither.
    SendSync,
    /// `Unpin` and the rest: only a raw pointer is fixed.
    Other,
}

/// True when the answer `behind` names is fixed at type `t`.
fn stops_at(tys: &impl TyIntern, t: Ty, behind: Behind) -> bool {
    match tys.kind(t) {
        TyKind::RawPtr(..) => true,
        TyKind::Ref(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) => behind == Behind::Clone,
        TyKind::Adt(..) => match tys.builtin_of(t) {
            Some(BuiltinTy::Rc | BuiltinTy::Weak) => behind != Behind::Other,
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Arc | crate::ty::sync::SyncTy::ArcWeak)) => behind == Behind::Clone,
            _ => false,
        },
        _ => false,
    }
}

/// `collect_adt_defs` that leaves out what lies behind a type `stop` takes.
fn collect_adt_defs_where(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<DefId>, stop: &dyn Fn(Ty) -> bool) {
    if stop(t) {
        return;
    }
    let args = |a: ArgsId, out: &mut Vec<DefId>| {
        for a in tys.args(a) {
            if let GenericArg::Ty(t) = a {
                collect_adt_defs_where(p, tys, *t, out, stop);
            }
        }
    };
    match tys.kind(t) {
        TyKind::Adt(def, a) => {
            out.push(def);
            args(a, out);
        }
        TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            collect_adt_defs_where(p, tys, inner, out, stop)
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts) {
                collect_adt_defs_where(p, tys, *e, out, stop);
            }
        }
        TyKind::FnPtr(sig) => {
            let sig = tys.sig(sig);
            for e in tys.tys_of(sig.value.inputs) {
                collect_adt_defs_where(p, tys, *e, out, stop);
            }
            collect_adt_defs_where(p, tys, sig.value.output, out, stop);
        }
        TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => args(a, out),
        TyKind::Dyn(bounds, _) => {
            let b = tys.dyn_bounds(bounds);
            let mut refs: Vec<&TraitRef> = b.principal.as_ref().map(|pr| &pr.value).into_iter().collect();
            refs.extend(b.supertraits.iter().map(|st| &st.value));
            for tr in refs {
                args(tr.args, out);
                for (_, arg) in tys.bindings(tr.bindings) {
                    if let GenericArg::Ty(t) = arg {
                        collect_adt_defs_where(p, tys, *t, out, stop);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Which deep walk a memo entry belongs to: Adt layouts by value
/// (`hash_adt_layout` over the Adts a value holds inline), Adt structure
/// (the same content over every Adt the fields name), or Adt regions
/// (`hash_adt_regions`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Deep {
    Layout,
    Structure,
    Regions,
}

/// The deep Adt fingerprints one fingerprint computation has made, so a
/// sub-type that many fields share is folded once (`adt_deep`). Callers
/// of `hash_ty_deep` make one per fingerprint and pass it along. The
/// program-wide `FpMemo` keeps the same values across computations.
/// The flag marks a fresh walk (`memo_check`): it neither reads nor
/// fills the program memo.
#[derive(Default)]
pub(crate) struct DeepMemo(FxMap<(Deep, DefId), u64>, bool);

/// The program-wide memo of deep Adt fingerprints, by `AdtId`. It is on
/// only while the program does not change: the driver turns it on after
/// collect and the std splice (`on`), and a kept program turns it off
/// before a patch edits it (`off`). Off, every fingerprint computation
/// still walks each Adt once (`DeepMemo`). Walks that fill it hold
/// `walk`: an Adt cycle publishes all its members before another walk
/// can see one of them, so no walk takes a member for a finished leaf.
///
/// Mono (`generics::materialize`) changes the program between body
/// checks, so there the memo follows it (`follow_begin`, `sync`): it is
/// on, and it starts empty again whenever `deep_stamp` moves.
#[derive(Default)]
pub struct FpMemo {
    layout: Vec<std::sync::OnceLock<u64>>,
    /// `DropCk` fingerprints (`drop_check_fingerprint`).
    dropck: Vec<std::sync::OnceLock<u64>>,
    structure: Vec<std::sync::OnceLock<u64>>,
    regions: Vec<std::sync::OnceLock<u64>>,
    /// `Answer` fingerprints, `ANSWER_KINDS` per Adt.
    answers: Vec<std::sync::OnceLock<u64>>,
    walk: std::sync::Mutex<()>,
    /// While mono runs on a program whose memo was off: the
    /// `deep_stamp` the current values were made under.
    follow: Option<u64>,
}

impl FpMemo {
    /// Turns the memo on, empty, for a program with `adts` Adts.
    pub fn on(&mut self, adts: usize) {
        self.layout = (0..adts).map(|_| Default::default()).collect();
        self.dropck = (0..adts).map(|_| Default::default()).collect();
        self.structure = (0..adts).map(|_| Default::default()).collect();
        self.regions = (0..adts).map(|_| Default::default()).collect();
        self.answers = (0..adts * ANSWER_KINDS).map(|_| Default::default()).collect();
    }

    /// Turns the memo off and drops its values.
    pub fn off(&mut self) {
        *self = FpMemo::default();
    }

    /// Starts following the program through mono when the memo is off
    /// (a collect); an on memo stays as its owner set it. `follow_end`
    /// turns a followed memo off again.
    pub(crate) fn follow_begin(&mut self) {
        if self.layout.is_empty() && self.regions.is_empty() {
            self.follow = Some(u64::MAX);
        }
    }

    /// `follow_begin` for a kept program delta (driver/kept_delta.rs,
    /// patch.rs): its body checks run after its edits, on a program that
    /// changes between them only as mono's does (`sync`). True when this
    /// call started following, so the caller ends it (`follow_end`).
    pub(crate) fn follow_scoped(&mut self) -> bool {
        let idle = self.follow.is_none() && self.layout.is_empty() && self.regions.is_empty();
        self.follow_begin();
        idle
    }

    pub(crate) fn follow_end(&mut self) {
        if self.follow.is_some() {
            self.off();
        }
    }

    /// Before each body check in mono: a followed memo drops its values
    /// when an input of the deep walk moved since they were made.
    pub(crate) fn sync(p: &mut Program) {
        if p.fp_memo.follow.is_none() {
            return;
        }
        let stamp = deep_stamp(p);
        if p.fp_memo.follow != Some(stamp) {
            p.fp_memo.on(p.adts.len());
            p.fp_memo.follow = Some(stamp);
        }
    }

    fn slot(&self, p: &Program, kind: Deep, def: DefId) -> Option<&std::sync::OnceLock<u64>> {
        let a = p.adt_by_def(def)?;
        match kind {
            Deep::Layout => self.layout.get(a.0 as usize),
            Deep::Structure => self.structure.get(a.0 as usize),
            Deep::Regions => self.regions.get(a.0 as usize),
        }
    }
}

impl DeepMemo {
    fn get(&self, p: &Program, kind: Deep, def: DefId) -> Option<u64> {
        if let Some(&v) = self.0.get(&(kind, def)) {
            return Some(v);
        }
        if self.1 {
            return None;
        }
        let v = p.fp_memo.slot(p, kind, def).and_then(|s| s.get().copied())?;
        if memo_check() {
            let fresh = adt_deep(p, kind, def, &mut DeepMemo(FxMap::default(), true));
            assert_eq!(fresh, v, "internal: stale deep fingerprint memo for {def:?} (LUST_CHECK_FPMEMO)");
        }
        Some(v)
    }

    fn put(&mut self, p: &Program, kind: Deep, def: DefId, v: u64) {
        self.0.insert((kind, def), v);
        if !self.1
            && let Some(s) = p.fp_memo.slot(p, kind, def)
        {
            let _ = s.set(v);
        }
    }
}

/// LUST_CHECK_FPMEMO=1: every value the program memo gives is computed
/// again by a fresh walk, and a difference panics (test sweeps).
fn memo_check() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("LUST_CHECK_FPMEMO").is_some_and(|v| v == "1"))
}

/// A stamp of the tables the deep walk reads that mono can grow
/// (`hash_adt_layout`, `hash_adt_regions`): their sizes. Mono writes only
/// new instance rows of `Program::adts` (a def maps to its template row,
/// so a walk never reaches one) and adds entries to these tables; it
/// edits no entry in place, so equal sizes mean equal walk inputs.
fn deep_stamp(p: &Program) -> u64 {
    let gx = &p.gx;
    let mut h = FxHasher::default();
    (gx.glue_methods.len(), gx.written_hash.len(), gx.borrow_impls.len(), gx.dyn_keys.len(), gx.adt_lifetimes.len()).hash(&mut h);
    (gx.index.impls_of_trait(gx.lang.hasher).len(), gx.index.impls_of_trait(gx.lang.build_hasher).len()).hash(&mut h);
    (p.regions.adt_facts.len(), p.regions.adt_fields.len(), p.regions.adt_bounds.len()).hash(&mut h);
    h.finish()
}

/// Hashes one type shallowly (`hash_ty`), then calls `r` for every Adt
/// def it names, in walk order.
fn hash_ty_refs(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    hash_ty(h, p, tys, t);
    let mut defs = Vec::new();
    collect_adt_defs(p, tys, t, &mut defs);
    for def in defs {
        r(h, def);
    }
}

/// True for a std type that holds its type args behind a pointer, or not
/// at all: owning heap pointers and collections, `RefCell` and lock
/// guards, thread and channel handles, a `thread_local!` key.
fn points_at_args(tys: &impl TyIntern, t: Ty) -> bool {
    use crate::ty::sync::SyncTy as S;
    matches!(
        tys.builtin_of(t),
        Some(BuiltinTy::Vec | BuiltinTy::Boxed | BuiltinTy::Rc | BuiltinTy::Weak | BuiltinTy::Hash(_))
            | Some(BuiltinTy::RefGuard | BuiltinTy::RefMutGuard | BuiltinTy::LocalKey | BuiltinTy::Fmt(_))
            | Some(BuiltinTy::Sync(
                S::Arc | S::ArcWeak | S::MutexGuard | S::RwLockReadGuard | S::RwLockWriteGuard | S::JoinHandle | S::ScopedJoinHandle | S::Sender | S::SyncSender | S::Receiver
            ))
    )
}

/// The Adt defs that the types `types` hold by value
/// (`Program::record_type_layout_reads`), with repeats; the hidden types
/// of opaques among them go to `hidden`.
fn by_value_adts(p: &Program, tys: &impl TyIntern, types: impl IntoIterator<Item = Ty>, defs: &mut Vec<DefId>, hidden: &mut Vec<Ty>) {
    let mut seen: FxMap<Ty, ()> = FxMap::default();
    let mut stack: Vec<Ty> = types.into_iter().collect();
    let ty_args = |a: ArgsId, stack: &mut Vec<Ty>| stack.extend(tys.args(a).iter().filter_map(|g| g.as_ty()));
    while let Some(t) = stack.pop() {
        if seen.insert(t, ()).is_some() {
            continue;
        }
        match tys.kind(t) {
            TyKind::Adt(def, args) => {
                defs.push(def);
                if !points_at_args(tys, t) {
                    ty_args(args, &mut stack);
                }
            }
            TyKind::Tuple(ts) => stack.extend(tys.tys_of(ts).iter().copied()),
            TyKind::Array(e, _) => stack.push(e),
            TyKind::Closure(_, a) => ty_args(a, &mut stack),
            TyKind::Opaque(def, _) => {
                if let Some(&h) = p.gx.opaque_hidden.get(&crate::check::generics::opaque_def(def)) {
                    hidden.push(h);
                }
            }
            _ => {}
        }
    }
}

/// Hashes one type deeply: the shallow structure (`hash_ty`) plus the
/// deep structure fingerprint of every Adt it names (`adt_deep`), which
/// covers that Adt's content and, transitively, every Adt its fields
/// name. The type of a const, static, or alias folds in this way: its
/// readers take the value or the type whole. Fn and Adt signatures fold
/// shallow (`sig_fingerprint`).
pub(crate) fn hash_ty_deep(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty, memo: &mut DeepMemo) {
    hash_ty_refs(h, p, tys, t, &mut |h, def| adt_deep(p, Deep::Structure, def, memo).hash(h));
}

/// Folds the written `Drop` and auto trait (`Send`, `Sync`, `Unpin`)
/// impls of Adt `def` into `h`: their headers and bounds, in a stable
/// order. Whether a type needs drop and which auto traits it has follow
/// its fields, so these impls reach every type that holds this one, as
/// its fields do. The other written impls of std and lang traits are
/// `LangImpls` reads of the bodies whose types name the Adt.
fn hash_structural_impls(h: &mut FxHasher, p: &Program, def: DefId) {
    let lang = &p.gx.lang;
    let mut impls: Vec<u64> = p
        .gx
        .index
        .impls_naming(def)
        .map(|id| p.gx.index.peek(id))
        .filter(|rec| rec.trait_def == lang.drop || lang.is_auto(rec.trait_def))
        .map(|rec| {
            let mut h = FxHasher::default();
            hash_trait_ref(&mut h, p, &p.tys, &rec.trait_ref);
            hash_generics(&mut h, p, &rec.generics);
            h.finish()
        })
        .collect();
    impls.sort_unstable();
    "structural-impls-v1".hash(h);
    impls.hash(h);
}

/// The deep fingerprint of one Adt in one walk: its own content
/// (`hash_adt_layout` or `hash_adt_regions`), where each Adt it names
/// folds in as that Adt's deep fingerprint. Adts that name each other
/// in a cycle (one strongly connected component of the "names" graph)
/// fold each other by def only, and each one's fingerprint covers the
/// content of every member, sorted by stable def identity. So the
/// value is a pure function of the reachable content, the same in
/// every run and walk order, and the walk visits each Adt once.
fn adt_deep(p: &Program, kind: Deep, def: DefId, memo: &mut DeepMemo) -> u64 {
    if kind == Deep::Regions && region_inert(p, def) {
        return regions_leaf(p, def);
    }
    if let Some(v) = memo.get(p, kind, def) {
        return v;
    }
    let _walk = (!memo.1 && !p.fp_memo.layout.is_empty()).then(|| p.fp_memo.walk.lock().unwrap_or_else(|e| e.into_inner()));
    if let Some(v) = memo.get(p, kind, def) {
        return v;
    }
    let mut scc = Scc { p, kind, order: FxMap::default(), stack: Vec::new() };
    scc.visit(def, memo);
    memo.get(p, kind, def).unwrap_or_default()
}

/// True for an Adt with no lifetime or type params: its region facts
/// (variance, outlives) are fixed whatever its fields hold (only
/// `'static` can appear in them), so the deep regions walk takes it as a
/// leaf by identity (`regions_leaf`); its fields' types are in its own
/// `Sig` already.
fn region_inert(p: &Program, def: DefId) -> bool {
    let Some(a) = p.adt_by_def(def) else { return false };
    p.gx.adt_lifetimes.get(&def).is_none_or(|l| l.is_empty())
        && p.gx.adt_generics.get(a.0 as usize).is_none_or(|g| g.params.iter().all(|q| matches!(q.kind, ParamKind::Const(_))))
}

/// The deep regions fingerprint of a `region_inert` Adt: its identity,
/// and the `Drop` and auto trait impls its readers' borrow ends follow.
fn regions_leaf(p: &Program, def: DefId) -> u64 {
    let mut h = FxHasher::default();
    "adt-regions-leaf-v2".hash(&mut h);
    hash_def_pub(&mut h, p, def);
    hash_structural_impls(&mut h, p, def);
    h.finish()
}

/// Folds one Adt's own content for walk `kind` into `h`; `r` folds each
/// Adt it names.
fn hash_adt_own(h: &mut FxHasher, p: &Program, kind: Deep, def: DefId, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    match kind {
        Deep::Layout => hash_adt_layout(h, p, def, true, r),
        Deep::Structure => hash_adt_layout(h, p, def, false, r),
        Deep::Regions => hash_adt_regions(h, p, def, r),
    }
}

/// Tarjan's strongly connected components over the Adts one deep walk
/// reaches (`adt_deep`). `order` holds (visit index, low link) for each
/// def seen; a seen def without a memo value is still on `stack`.
struct Scc<'p> {
    p: &'p Program,
    kind: Deep,
    order: FxMap<DefId, (u32, u32)>,
    stack: Vec<DefId>,
}

impl Scc<'_> {
    fn visit(&mut self, v: DefId, memo: &mut DeepMemo) {
        let (p, kind) = (self.p, self.kind);
        let index = self.order.len() as u32;
        self.order.insert(v, (index, index));
        self.stack.push(v);
        let mut succ: Vec<DefId> = Vec::new();
        hash_adt_own(&mut FxHasher::default(), p, kind, v, &mut |_, d| {
            if !succ.contains(&d) && !(kind == Deep::Regions && region_inert(p, d)) {
                succ.push(d);
            }
        });
        for w in succ {
            if memo.get(p, kind, w).is_some() {
                continue;
            }
            let low = match self.order.get(&w) {
                Some(&(wi, _)) => wi,
                None => {
                    self.visit(w, memo);
                    self.order[&w].1
                }
            };
            let e = self.order.get_mut(&v).expect("visited");
            e.1 = e.1.min(low);
        }
        if self.order[&v].1 != index {
            return;
        }
        let at = self.stack.iter().rposition(|d| *d == v).expect("on stack");
        let mut members = self.stack.split_off(at);
        members.sort_unstable_by_key(|d| (def_crate_hash(p, *d), d.hash.0));
        let mut h = FxHasher::default();
        (match kind {
            Deep::Layout => "adt-deep-layout-v2",
            Deep::Structure => "adt-deep-structure-v1",
            Deep::Regions => "adt-deep-regions-v1",
        })
        .hash(&mut h);
        (members.len() as u64).hash(&mut h);
        for &m in &members {
            hash_adt_own(&mut h, p, kind, m, &mut |h, d| match members.contains(&d) {
                true => {
                    "scc-member".hash(h);
                    hash_def_pub(h, p, d);
                }
                false if kind == Deep::Regions && region_inert(p, d) => regions_leaf(p, d).hash(h),
                false => memo.get(p, kind, d).unwrap_or_default().hash(h),
            });
        }
        let scc = h.finish();
        for &m in &members {
            let mut h = FxHasher::default();
            scc.hash(&mut h);
            hash_def_pub(&mut h, p, m);
            memo.put(p, kind, m, h.finish());
        }
    }
}

/// Folds one Adt's layout-relevant content into `h`: enum-ness, repr,
/// derives (every derived trait and the `#[default]` variant change
/// what checking and codegen do with a value, so they are part of this
/// fingerprint, not only of `Sig`), and per variant its name, shape, discriminant, and
/// field names and field types; `r` folds each Adt a type names (see
/// `adt_deep`). Builtin Adts (String, Vec, Option)
/// and unknown defs fold their def hash only: their layout is fixed by
/// the compiler, never by a user edit.
fn hash_adt_layout(h: &mut FxHasher, p: &Program, def: DefId, by_value: bool, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    "adt-layout-v2".hash(h);
    // By value, `r` folds only the Adts a field holds inline; the others
    // fold by identity, inside the field's type.
    let field_ty = |h: &mut FxHasher, t: Ty, r: &mut dyn FnMut(&mut FxHasher, DefId)| {
        if by_value {
            hash_ty(h, p, &p.tys, t);
            let (mut defs, mut hidden) = (Vec::new(), Vec::new());
            by_value_adts(p, &p.tys, [t], &mut defs, &mut hidden);
            for d in defs {
                r(h, d);
            }
        } else {
            hash_ty_refs(h, p, &p.tys, t, r);
        }
    };
    hash_def_pub(h, p, def);
    let Some(a) = p.adt_by_def(def) else { return };
    let adt = p.adt(a);
    adt.is_enum.hash(h);
    match adt.repr.kind {
        crate::ty::layout::ReprKind::Default => 0u8.hash(h),
        crate::ty::layout::ReprKind::C => 1u8.hash(h),
        crate::ty::layout::ReprKind::Transparent => 2u8.hash(h),
    }
    adt.repr.int.hash(h);
    adt.repr.align.hash(h);
    adt.repr.pack.hash(h);
    // The derive list is not part of the layout (PLAN R12, P3.3): every
    // reader of it records its own `Derives` read (check/derive_delta.rs).
    // `#[non_exhaustive]` changes match exhaustiveness answers over
    // this type, which layout readers (a match's scrutinee type) see.
    adt.non_exhaustive.hash(h);
    // The written impls derive glue calls for a value of this type.
    let glue = |tr: DefId| p.gx.glue_methods.contains_key(&(a, tr));
    (glue(p.gx.lang.clone), glue(p.gx.lang.default), glue(p.gx.lang.partial_eq), glue(p.gx.lang.partial_ord)).hash(h);
    p.gx.written_hash.contains_key(&a).hash(h);
    p.gx.borrow_impls.keys().filter(|(b, _)| *b == a).count().hash(h);
    p.gx.dyn_keys.get(&a).map(|k| (k.eq, k.hash, k.borrow)).hash(h);
    // The written `Hasher` and `BuildHasher` impls the hash glue calls
    // into: which methods they write, and the `Hasher` type (W-STD-B).
    // Read with no note (`peek`), as fingerprints read: this runs while a
    // body's read scope is open, and a note charged that body a
    // `LangImpls` read of every hasher the scan skips, or of none when the
    // fingerprint memo held this layout already.
    for tr in [p.gx.lang.hasher, p.gx.lang.build_hasher] {
        for &id in p.gx.index.impls_of_trait(tr) {
            let rec = p.gx.index.peek(id);
            if rec.synthetic != crate::traits::index::Synthetic::None || rec.head != crate::traits::index::SelfHead::Adt(def) {
                continue;
            }
            for &m in &rec.items {
                if let Some(l) = p.local_def(m.hash) {
                    p.name(p.fn_info(l).name).hash(h);
                }
            }
            for &(_, t) in &rec.assoc_tys {
                field_ty(h, t, r);
            }
        }
    }
    // Its written `Drop` and auto trait impls: drop glue and auto traits
    // of every type that holds this one read them.
    hash_structural_impls(h, p, def);
    // A generic Adt's parameters and bounds: a bound edit changes what
    // every use of the type must prove (generic reuse, W-PERF).
    if let Some(g) = p.gx.adt_generics.get(a.0 as usize) {
        hash_generics(h, p, g);
    }
    (adt.variants.len() as u64).hash(h);
    for v in &adt.variants {
        p.name(v.name).hash(h);
        match v.shape {
            VariantShape::Unit => 0u8.hash(h),
            VariantShape::Tuple => 1u8.hash(h),
            VariantShape::Named => 2u8.hash(h),
        }
        v.disc.hash(h);
        v.non_exhaustive.hash(h);
        (v.fields.len() as u64).hash(h);
        for (i, fd) in v.fields.iter().enumerate() {
            // Tuple fields carry a synthetic index `Sym`, not a name.
            if v.shape == VariantShape::Named {
                p.name(fd.name).hash(h);
            } else {
                (i as u64).hash(h);
            }
            field_ty(h, fd.ty, r);
        }
    }
}

/// The `Derives(def)` node's fingerprint: the derive list of the Adt
/// with that def, or a fixed value when this program has no such Adt.
fn derives_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "derives-v1".hash(&mut h);
    if let Some(a) = p.adt_by_def(def) {
        let d = p.adt(a).derives_unlogged();
        (d.debug, d.clone, d.copy, d.partial_eq, d.eq, d.hash, d.partial_ord, d.ord, d.default, d.default_variant).hash(&mut h);
    }
    Fingerprint(h.finish())
}

/// The `DeriveBits(def, mask)` node's fingerprint: the derive flags of
/// the Adt with that def that `mask` selects (and the `#[default]` variant
/// with the `Default` bit), or a fixed value when there is no such Adt.
fn derive_bits_fingerprint(p: &Program, def: DefId, mask: u16) -> Fingerprint {
    let mut h = FxHasher::default();
    "derive-bits-v1".hash(&mut h);
    mask.hash(&mut h);
    if let Some(a) = p.adt_by_def(def) {
        let d = p.adt(a).derives_unlogged();
        crate::check::derive_delta::masked(&d, mask).hash(&mut h);
        if mask & crate::check::derive_delta::bit::DEFAULT != 0 {
            d.default_variant.hash(&mut h);
        }
    }
    Fingerprint(h.finish())
}

/// The `LangImpls(def)` node's fingerprint: the shape (`lang_impl_shape`)
/// of each written std or lang trait impl whose trait ref names the Adt
/// template `def`, in a stable order, or a fixed value when there is none.
fn lang_impls_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut impls: Vec<(u64, u64, u64)> = p
        .gx
        .index
        .impls_naming(def)
        .map(|id| p.gx.index.peek(id))
        .map(|rec| (def_crate_hash(p, rec.trait_def), rec.trait_def.hash.0, lang_impl_shape(p, rec)))
        .collect();
    impls.sort_unstable();
    let mut h = FxHasher::default();
    "lang-impls-v2".hash(&mut h);
    impls.hash(&mut h);
    Fingerprint(h.finish())
}

/// The resolved shape of one impl record (`lang_impl_shape`) for the
/// trait-system key (gen_reuse.rs `trait_key`): the aliases and consts
/// its written header and bounds name are resolved in it.
pub(crate) fn resolved_impl_hash(p: &Program, def: DefId) -> u64 {
    p.gx.index.peek_def(def).map_or(0, |rec| lang_impl_shape(p, rec))
}

/// Every trait record, resolved, for the trait-system key: generics and
/// bounds (supertraits, associated type bounds), associated items, the
/// declared types of associated consts, and methods.
pub(crate) fn resolved_traits_hash(p: &Program) -> u64 {
    let mut recs: Vec<&crate::traits::index::TraitRecord> = p.gx.index.trait_records().collect();
    recs.sort_unstable_by_key(|r| (def_crate_hash(p, r.def), r.def.hash.0));
    let mut h = FxHasher::default();
    "resolved-traits-v1".hash(&mut h);
    (recs.len() as u64).hash(&mut h);
    for r in recs {
        hash_def_pub(&mut h, p, r.def);
        hash_generics(&mut h, p, &r.generics);
        (r.assoc_items.len() as u64).hash(&mut h);
        for &(d, n, is_type) in &r.assoc_items {
            hash_def_pub(&mut h, p, d);
            (p.name(n), is_type).hash(&mut h);
            if let Some(&(t, has_default)) = p.gx.trait_assoc_consts.get(&d) {
                hash_ty(&mut h, p, &p.tys, t);
                has_default.hash(&mut h);
            }
        }
        (r.methods.len() as u64).hash(&mut h);
        for &(d, n) in &r.methods {
            hash_def_pub(&mut h, p, d);
            p.name(n).hash(&mut h);
        }
    }
    h.finish()
}

/// One written std or lang trait impl as `LangImpls` reads see it, with no
/// deep walk: the trait ref, generics and bounds, associated type and
/// const bindings, the regioned header, and each item's name and
/// signature. Types fold shallow (`hash_ty`: defs in stable form, regions
/// included); a body that reads deeper into a named type records a `Sig`
/// or `Layout` read of its own. Items fold by name, so an impl added
/// before this one (which moves its items' def hashes) leaves it alone.
fn lang_impl_shape(p: &Program, rec: &crate::traits::index::ImplRecord) -> u64 {
    let tys = &p.tys;
    let mut h = FxHasher::default();
    "lang-impl-shape-v1".hash(&mut h);
    hash_trait_ref(&mut h, p, tys, &rec.trait_ref);
    hash_generics(&mut h, p, &rec.generics);
    (rec.assoc_tys.len() as u64).hash(&mut h);
    for (d, t) in &rec.assoc_tys {
        hash_def_pub(&mut h, p, *d);
        hash_ty(&mut h, p, tys, *t);
    }
    (rec.assoc_consts.len() as u64).hash(&mut h);
    for (d, c) in &rec.assoc_consts {
        hash_def_pub(&mut h, p, *d);
        hash_const(&mut h, tys, *c);
    }
    if let Some(ir) = p.regions.impl_regions.get(&rec.def) {
        1u8.hash(&mut h);
        for &t in ir.header.iter().chain(ir.assoc.iter().map(|(_, t)| t)) {
            hash_ty(&mut h, p, tys, t);
        }
        ir.facts.hash(&mut h);
        (ir.preds.len() as u64).hash(&mut h);
        for pred in &ir.preds {
            hash_predicate(&mut h, p, tys, pred);
        }
    }
    if let Some(head) = p.regions.impl_heads.get(&rec.def) {
        2u8.hash(&mut h);
        hash_ty(&mut h, p, tys, head.self_ty);
        for &r in &head.trait_lifetimes {
            hash_region(&mut h, r);
        }
        for w in &head.where_lts {
            w.param.hash(&mut h);
            hash_def_pub(&mut h, p, w.trait_def);
            for &r in &w.lifetimes {
                hash_region(&mut h, r);
            }
        }
    }
    (rec.items.len() as u64).hash(&mut h);
    for &d in &rec.items {
        let Some(l) = p.local_def(d.hash).filter(|l| p.def_id(*l) == d) else {
            hash_def_pub(&mut h, p, d);
            continue;
        };
        let f = p.fn_info(l);
        p.name(f.name).hash(&mut h);
        match f.self_kind {
            None => 0u8.hash(&mut h),
            Some(SelfKind::Value) => 1u8.hash(&mut h),
            Some(SelfKind::Ref) => 2u8.hash(&mut h),
            Some(SelfKind::RefMut) => 3u8.hash(&mut h),
            Some(SelfKind::Typed) => 4u8.hash(&mut h),
        }
        (f.params.len() as u64).hash(&mut h);
        for &t in &f.params {
            hash_ty(&mut h, p, tys, t);
        }
        hash_ty(&mut h, p, tys, f.ret);
        let def = f.def(&p.ast);
        (def.qual.is_const, def.qual.is_async, def.qual.is_unsafe, def.variadic).hash(&mut h);
        crate::check::caller::is_track_caller(p, l).hash(&mut h);
        match p.gx.fn_templates.get(l.0 as usize) {
            Some(Some(t)) => hash_generics(&mut h, p, &t.generics),
            _ => u64::MAX.hash(&mut h),
        }
        match p.regions.fns.get(&l) {
            Some(rs) => {
                1u8.hash(&mut h);
                rs.n_univ.hash(&mut h);
                for &t in rs.params.iter().chain(std::iter::once(&rs.ret)).chain(&rs.header) {
                    hash_ty(&mut h, p, tys, t);
                }
                for &(a, b) in &rs.facts {
                    hash_region(&mut h, a);
                    hash_region(&mut h, b);
                }
                rs.early.hash(&mut h);
                (rs.bounds.len() as u64).hash(&mut h);
                for pred in &rs.bounds {
                    hash_predicate(&mut h, p, tys, pred);
                }
            }
            None => 0u8.hash(&mut h),
        }
    }
    h.finish()
}

/// The `LayoutOf(adt)` node's fingerprint (section 8.1), separate from
/// `Sig`: it covers only what layout and value semantics read (see
/// `hash_adt_layout`), over the Adts a value holds inline (a type behind
/// a pointer or in a collection folds by identity, `Deep::Layout`). So an
/// edit that changes a type's methods or a field's visibility does not
/// dirty layout readers, and a field edit dirties them even when no
/// signature that names the type changed text.
pub(crate) fn layout_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "layout-v3".hash(&mut h);
    adt_deep(p, Deep::Layout, def, &mut DeepMemo::default()).hash(&mut h);
    Fingerprint(h.finish())
}

/// The kinds of `ReadKey::Answer`: the structural question asked of the Adt.
pub(crate) mod answer {
    /// `Send`, `Sync`, and `Unpin` together: a walk through `&T` asks
    /// `Sync` of a `Send` question.
    pub(crate) const AUTO: u8 = 0;
    pub(crate) const CLONE: u8 = 1;
    pub(crate) const PARTIAL_EQ: u8 = 2;
    pub(crate) const EQ: u8 = 3;
    pub(crate) const PARTIAL_ORD: u8 = 4;
    pub(crate) const DEFAULT: u8 = 5;
}

/// True for an Adt template with no generic params at all: its structural
/// answers are closed booleans (`ReadKey::Answer`).
fn closed_adt(p: &Program, def: DefId) -> bool {
    let Some(a) = p.adt_by_def(def) else { return false };
    p.gx.adt_lifetimes.get(&def).is_none_or(|l| l.is_empty()) && p.gx.adt_generics.get(a.0 as usize).is_none_or(|g| g.params.is_empty())
}

/// The `Answer(adt, kind)` node's fingerprint: the answer for the closed
/// type of the Adt (memoized while the program memo is on), or its
/// `Structure` fingerprint for an Adt with generic params. Computed with
/// the derive log closed: it notes nothing into a body that records it.
fn answer_fingerprint(p: &Program, def: DefId, kind: u8) -> Fingerprint {
    let slot = p.adt_by_def(def).and_then(|a| p.fp_memo.answers.get(a.0 as usize * ANSWER_KINDS + kind as usize));
    if let Some(v) = slot.and_then(|s| s.get()) {
        return Fingerprint(*v);
    }
    let mut h = FxHasher::default();
    ("answer-v1", kind).hash(&mut h);
    if closed_adt(p, def) {
        use crate::check::collect as c;
        crate::check::derive_delta::unlogged(|| {
            let mut tys = crate::ty::Tys::new(&p.tys);
            let t = tys.mk_adt(def, &[]);
            let lang = &p.gx.lang;
            match kind {
                answer::AUTO => {
                    for tr in [lang.send, lang.sync, lang.unpin] {
                        c::auto_structural(p, &mut tys, &[], tr, t, &mut c::AutoSeen::default()).hash(&mut h);
                    }
                }
                answer::CLONE => c::has_clone(p, &tys, t).hash(&mut h),
                answer::PARTIAL_EQ => c::has_eq(p, &tys, t).hash(&mut h),
                answer::EQ => c::has_total_eq(p, &tys, t).hash(&mut h),
                answer::PARTIAL_ORD => c::has_ord(p, &tys, t).hash(&mut h),
                _ => c::has_default(p, &tys, t).hash(&mut h),
            }
        });
    } else if let Some(shape) = adt_shape(p, def, kind != answer::AUTO) {
        ("shape", kind != answer::AUTO, shape).hash(&mut h);
    } else {
        structure_fingerprint(p, def).0.hash(&mut h);
    }
    let v = h.finish();
    if let Some(s) = slot {
        let _ = s.set(v);
    }
    Fingerprint(v)
}

/// The auto shape of a user Adt with type or lifetime params (`glue` false): what its auto
/// trait answers (`Send`, `Sync`, `Unpin`) for any instance are a function of,
/// with the auto answers of the instance's args (which a reader records
/// itself: `record_structure_reads` walks the instance type). Auto traits are
/// structural, so an instance's answer comes from its field types: the shape
/// folds the Adt's identity, its written auto trait impls, and every field type of
/// the template, params kept and regions left out, where a closed user Adt
/// counts by its own auto answer (`answer_fingerprint`), a generic one by its
/// shape (a back-reference inside a cycle), a std Adt by its def and args, and a
/// raw pointer, which answers nothing of its target, by itself. None when a
/// field holds a type the shape does not cover (a closure, an opaque type, a
/// projection): its `Answer` fingerprint is then the deep `Structure` one.
///
/// With `glue` it is the glue shape instead, for the derive glue answers
/// (`Clone`, `PartialEq`, `Eq`, `PartialOrd`, `Default`; `record_glue_reads`):
/// the Adt's derive list and its written std and lang trait impls in place of
/// its auto impls, and a closed user Adt counting by all five glue answers and
/// whether it is `Copy` (a `Cell<T>` clones when `T` is).
pub(crate) fn adt_shape(p: &Program, def: DefId, glue: bool) -> Option<u64> {
    fn adt(p: &Program, def: DefId, glue: bool, visiting: &mut Vec<DefId>) -> Option<u64> {
        if let Some(k) = visiting.iter().position(|&d| d == def) {
            let mut h = FxHasher::default();
            ("auto-shape-back", k).hash(&mut h);
            return Some(h.finish());
        }
        let a = p.adt_by_def(def)?;
        visiting.push(def);
        let mut h = FxHasher::default();
        ("adt-shape-v3", glue).hash(&mut h);
        hash_def_pub(&mut h, p, def);
        if glue {
            derives_fingerprint(p, def).0.hash(&mut h);
            lang_impls_fingerprint(p, def).0.hash(&mut h);
        }
        // The written impls of auto traits on the Adt (an `unsafe impl Send`):
        // the only impls an auto answer reads. Mono adds synthetic impls (glue,
        // `Drop` of instances) while it runs, which must not move the shape.
        let lang = &p.gx.lang;
        let mut impls: Vec<u64> = p
            .gx
            .index
            .impls_naming(def)
            .map(|id| p.gx.index.peek(id))
            .filter(|rec| !glue && lang.is_auto(rec.trait_def) && rec.synthetic == crate::traits::index::Synthetic::None)
            .map(|rec| {
                let mut h = FxHasher::default();
                hash_trait_ref(&mut h, p, &p.tys, &rec.trait_ref);
                hash_generics(&mut h, p, &rec.generics);
                h.finish()
            })
            .collect();
        impls.sort_unstable();
        impls.hash(&mut h);
        let mut ok = true;
        for v in &p.adts[a.0 as usize].variants {
            v.fields.len().hash(&mut h);
            for f in &v.fields {
                if ty(p, f.ty, glue, visiting, &mut h).is_none() {
                    ok = false;
                }
            }
        }
        visiting.pop();
        ok.then(|| h.finish())
    }
    fn ty(p: &Program, t: Ty, glue: bool, visiting: &mut Vec<DefId>, h: &mut FxHasher) -> Option<()> {
        let tys = &p.tys;
        match tys.kind(t) {
            TyKind::Adt(d, args) => {
                if p.user_adt(d) {
                    if closed_adt(p, d) && !glue {
                        ("closed", answer_fingerprint(p, d, answer::AUTO).0).hash(h);
                    } else if closed_adt(p, d) {
                        "closed-glue".hash(h);
                        for k in [answer::CLONE, answer::PARTIAL_EQ, answer::EQ, answer::PARTIAL_ORD, answer::DEFAULT] {
                            answer_fingerprint(p, d, k).0.hash(h);
                        }
                        let mut tys = crate::ty::Tys::new(&p.tys);
                        let t = tys.mk_adt(d, &[]);
                        crate::check::collect::is_copy(p, &tys, t).hash(h);
                    } else {
                        ("generic", adt(p, d, glue, visiting)?).hash(h);
                    }
                } else {
                    "std".hash(h);
                    hash_def_pub(h, p, d);
                }
                for g in tys.args(args) {
                    match *g {
                        GenericArg::Ty(e) => ty(p, e, glue, visiting, h)?,
                        GenericArg::Const(c) => ("const", tys.const_kind(c)).hash(h),
                        GenericArg::Lifetime(_) => {}
                    }
                }
            }
            TyKind::RawPtr(m, _) => ("raw", m.is_mut()).hash(h),
            TyKind::Ref(_, m, e) => {
                ("ref", m.is_mut()).hash(h);
                ty(p, e, glue, visiting, h)?;
            }
            TyKind::Slice(e) => {
                "slice".hash(h);
                ty(p, e, glue, visiting, h)?;
            }
            TyKind::Array(e, n) => {
                ("array", tys.const_kind(n)).hash(h);
                ty(p, e, glue, visiting, h)?;
            }
            TyKind::Tuple(ts) => {
                ("tuple", tys.tys_of(ts).len()).hash(h);
                for &e in tys.tys_of(ts) {
                    ty(p, e, glue, visiting, h)?;
                }
            }
            TyKind::Param(i) => ("param", i.0).hash(h),
            TyKind::Closure(..) | TyKind::Opaque(..) | TyKind::Projection(..) | TyKind::Infer(_) | TyKind::Error => return None,
            _ => hash_ty(h, p, tys, t),
        }
        Some(())
    }
    if !p.user_adt(def) || closed_adt(p, def) {
        return None;
    }
    // The walk reads derive lists and asks `Copy` of closed Adts: it must note
    // nothing into a body check that records this read.
    crate::check::derive_delta::unlogged(|| adt(p, def, glue, &mut Vec::new()))
}

/// `ReadKey::Answer` kinds per Adt in the program memo.
const ANSWER_KINDS: usize = 6;

/// The `Structure(adt)` node's fingerprint: the Adt's content and,
/// transitively, that of every Adt its fields name, behind pointers and
/// in collections too (`Deep::Structure`).
pub(crate) fn structure_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "structure-v1".hash(&mut h);
    adt_deep(p, Deep::Structure, def, &mut DeepMemo::default()).hash(&mut h);
    Fingerprint(h.finish())
}

/// Folds the regions of one regioned type (W-BORROW, `p.regions`) into
/// `h`: its structure with regions, then the deep regions fingerprint
/// of every Adt it names (`adt_deep`). Erased types hide what the borrow
/// checker reads here (`&'static str` and `&str` are one erased type;
/// an Adt's variance comes from its fields' regions), so a region-only
/// edit must move the `Sig` fingerprint of what it changed.
fn hash_regions_deep(h: &mut FxHasher, p: &Program, t: Ty, memo: &mut DeepMemo) {
    hash_ty_refs(h, p, &p.tys, t, &mut |h, def| adt_deep(p, Deep::Regions, def, memo).hash(h));
}

/// Folds one Adt's lifetime params and regioned field types into `h`;
/// `r` folds each Adt a field type names (see `hash_regions_deep`).
fn hash_adt_regions(h: &mut FxHasher, p: &Program, def: DefId, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    "adt-regions-v2".hash(h);
    hash_def_pub(h, p, def);
    // A `Drop` impl moves borrow ends and drop order.
    hash_structural_impls(h, p, def);
    (p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len()) as u64).hash(h);
    p.regions.adt_facts.get(&def).hash(h);
    // Its regioned trait bounds (tf-borrow r9): building a value replays them.
    if let Some(bs) = p.regions.adt_bounds.get(&def) {
        (bs.len() as u64).hash(h);
        for b in bs {
            if let Predicate::Trait(t) = b {
                hash_def_pub(h, p, t.value.def);
                for g in p.tys.args(t.value.args) {
                    match *g {
                        GenericArg::Ty(x) => hash_ty_refs(h, p, &p.tys, x, r),
                        GenericArg::Lifetime(x) => hash_region(h, x),
                        _ => {}
                    }
                }
            }
        }
    }
    let Some(variants) = p.regions.adt_fields.get(&def) else { return 0u8.hash(h) };
    (variants.len() as u64).hash(h);
    for fields in variants {
        (fields.len() as u64).hash(h);
        for &t in fields {
            hash_ty_refs(h, p, &p.tys, t, r);
        }
    }
}

/// Folds a fn's region signature into `h`: regioned params and return
/// (deeply), outlives facts, and early-bound flags. A caller's borrow
/// check reads all of them; the erased signature shows none.
fn hash_region_sig(h: &mut FxHasher, p: &Program, rs: Option<&crate::borrowck::RegionSig>) {
    "region-sig-v2".hash(h);
    let Some(rs) = rs else { return 0u8.hash(h) };
    1u8.hash(h);
    rs.n_univ.hash(h);
    let mut seen = DeepMemo::default();
    (rs.params.len() as u64).hash(h);
    for &t in &rs.params {
        hash_regions_deep(h, p, t, &mut seen);
    }
    hash_regions_deep(h, p, rs.ret, &mut seen);
    (rs.facts.len() as u64).hash(h);
    for &(a, b) in &rs.facts {
        hash_region(h, a);
        hash_region(h, b);
    }
    rs.early.hash(h);
    rs.opaque_caps.hash(h);
    (rs.header.len() as u64).hash(h);
    for &t in &rs.header {
        hash_regions_deep(h, p, t, &mut seen);
    }
    (rs.fn_bounds.len() as u64).hash(h);
    for b in &rs.fn_bounds {
        b.param.hash(h);
        (b.inputs.len() as u64).hash(h);
        for &t in b.inputs.iter().chain(b.output.iter()) {
            hash_regions_deep(h, p, t, &mut seen);
        }
        b.output.is_some().hash(h);
    }
    (rs.trait_bounds.len() as u64).hash(h);
    for b in &rs.trait_bounds {
        b.param.hash(h);
        hash_def_pub(h, p, b.trait_def);
        for &r in &b.lifetimes {
            hash_region(h, r);
        }
    }
    (rs.item_bounds.len() as u64).hash(h);
    for &(j, d, t) in &rs.item_bounds {
        j.hash(h);
        hash_def_pub(h, p, d);
        hash_regions_deep(h, p, t, &mut seen);
    }
    hash_preds_regions(h, p, &rs.bounds, &mut seen);
}

/// Folds regioned predicates into `h` (`RegionSig::bounds`,
/// `ImplRegions::preds`): a caller's borrow check replays the impls they
/// select with these regions.
fn hash_preds_regions(h: &mut FxHasher, p: &Program, preds: &[Predicate], seen: &mut DeepMemo) {
    let args = |h: &mut FxHasher, a: crate::ty::ArgsId, seen: &mut DeepMemo| {
        for g in p.tys.args(a) {
            match *g {
                GenericArg::Ty(t) => hash_regions_deep(h, p, t, seen),
                GenericArg::Lifetime(r) => hash_region(h, r),
                _ => 9u8.hash(h),
            }
        }
    };
    (preds.len() as u64).hash(h);
    for pred in preds {
        match *pred {
            Predicate::Trait(b) => {
                (0u8, b.count).hash(h);
                hash_def_pub(h, p, b.value.def);
                args(h, b.value.args, seen);
            }
            Predicate::AssocEq(b) => {
                (1u8, b.count).hash(h);
                hash_def_pub(h, p, b.value.assoc);
                args(h, b.value.trait_args, seen);
                hash_regions_deep(h, p, b.value.ty, seen);
            }
            Predicate::Outlives(a, b) => {
                2u8.hash(h);
                hash_region(h, a);
                hash_region(h, b);
            }
            Predicate::TypeOutlives(t, r) => {
                3u8.hash(h);
                hash_regions_deep(h, p, t, seen);
                hash_region(h, r);
            }
        }
    }
}

/// The fingerprint of a `Binding` node's answer (section 8.1: the resolved
/// def in disk form, or ambiguous, or absent). Wave A also folds the
/// resolved def's `Sig` fingerprint in: read-based reuse must not keep a
/// body that recorded only the binding (a fn used as a value, say) when
/// that def's signature changed. This is coarser than section 8.1's
/// node split and can narrow once read-coverage reviews prove every
/// signature use records a `Sig` read.
fn binding_fingerprint(p: &Program, res: BindingRes) -> Fingerprint {
    let mut h = FxHasher::default();
    "binding-v2".hash(&mut h);
    match res {
        BindingRes::Def(def) => {
            0u8.hash(&mut h);
            hash_def_pub(&mut h, p, def);
            sig_fingerprint(p, def).0.hash(&mut h);
        }
        BindingRes::Ambiguous => 1u8.hash(&mut h),
        BindingRes::Absent => 2u8.hash(&mut h),
    }
    Fingerprint(h.finish())
}

/// The fingerprint of an `AssocVis` node: the item's visibility and the
/// path of the module it is written in.
fn assoc_vis_fingerprint(p: &Program, entry: Option<&(VisKind, ModuleId)>) -> Fingerprint {
    let mut h = FxHasher::default();
    "assoc-vis-v1".hash(&mut h);
    if let (Some((vis, m)), Some(t)) = (entry, &p.resolved) {
        hash_vis(&mut h, p, vis);
        hash_module_path(&mut h, p, t, *m);
    }
    Fingerprint(h.finish())
}

/// The fingerprint of a `TraitInScope` node: its answer.
fn trait_in_scope_fingerprint(ans: bool) -> Fingerprint {
    let mut h = FxHasher::default();
    ("trait-in-scope-v1", ans).hash(&mut h);
    Fingerprint(h.finish())
}

/// Folds a probe head into a fingerprint. Head payloads hash by stable
/// content (def disk identity, scalar type name), never by session id.
fn hash_head(h: &mut FxHasher, p: &Program, head: Head) {
    match head {
        Head::Adt(def) => {
            0u8.hash(h);
            hash_def_pub(h, p, def);
        }
        Head::Int(i) => (1u8, i.name()).hash(h),
        Head::Float(f) => (2u8, f.name()).hash(h),
        Head::Bool => 3u8.hash(h),
        Head::Char => 4u8.hash(h),
        Head::Str => 5u8.hash(h),
        Head::Slice => 6u8.hash(h),
        Head::Array => 7u8.hash(h),
        Head::Tuple => 8u8.hash(h),
        Head::Never => 9u8.hash(h),
        Head::Unit => 10u8.hash(h),
        Head::Unknown => 11u8.hash(h),
    }
}

/// The fingerprint of a `MethodSet` node's candidate list, in probe order.
/// Candidate `Sig` fingerprints fold in for the same reason as in
/// `binding_fingerprint`. An empty set still folds the probe itself
/// (head, name, receiver form): builtin method dispatch answers those
/// probes through the compat path in check, so the probe is the read
/// on record for the builtin answer. That answer is fixed by the
/// compiler, and no user edit can add an inherent method to a builtin
/// or primitive head; when trait candidates join `method_candidates`,
/// they appear in the set and change this fingerprint by themselves.
fn method_set_fingerprint(p: &Program, key: &MethodSetKey, set: &MethodSet) -> Fingerprint {
    let mut h = FxHasher::default();
    "method-set-v3".hash(&mut h);
    (set.candidates.len() as u64).hash(&mut h);
    for c in &set.candidates {
        hash_def_pub(&mut h, p, c.def);
        sig_fingerprint(p, c.def).0.hash(&mut h);
        match c.trait_ {
            Some(t) => hash_def_pub(&mut h, p, t),
            None => 0u64.hash(&mut h),
        }
    }
    if set.candidates.is_empty() {
        "builtin-probe-v1".hash(&mut h);
        hash_head(&mut h, p, key.head);
        p.name(key.name).hash(&mut h);
        match key.form {
            ReceiverForm::Value => 0u8.hash(&mut h),
            ReceiverForm::Ref => 1u8.hash(&mut h),
            ReceiverForm::RefMut => 2u8.hash(&mut h),
        }
    }
    Fingerprint(h.finish())
}

/// The fingerprint of an `ImplSet` bucket: the bucket key (trait and
/// head) plus each impl's def and content (`impl_content`), sorted so the
/// bucket's discovery order does not matter (section 8.1). The content
/// joins because an impl keeps its def through edits to its where
/// clauses, associated types and consts, and method list.
fn impl_set_fingerprint(p: &Program, key: &ImplSetKey, set: &ImplSet) -> Fingerprint {
    // The `'static` dyn flag joins each impl (check::object): flipping
    // `impl X for dyn Tr` to `+ '_` keeps the def.
    let mut defs: Vec<(u64, u64, bool, u64)> = set
        .impls
        .iter()
        .map(|d| (def_crate_hash(p, *d), d.hash.0, p.gx.static_dyn_impls.contains(d), impl_content(p, *d)))
        .collect();
    defs.sort_unstable();
    let mut h = FxHasher::default();
    "impl-set-v2".hash(&mut h);
    hash_def_pub(&mut h, p, key.trait_);
    hash_head(&mut h, p, key.head);
    (defs.len() as u64).hash(&mut h);
    for d in defs {
        d.hash(&mut h);
    }
    // A blanket impl bounded by a derivable trait (`impl<T: Debug> U for
    // T`): whether a local Adt head selects it follows that Adt's derive
    // list, so the derive flags its bounds name join (sigedit R13 v2).
    if let Head::Adt(d) = key.head
        && let Some(a) = p.adt_by_def(d)
    {
        let mask = set
            .impls
            .iter()
            .filter_map(|&i| p.gx.index.by_def(i))
            .filter(|(_, rec)| rec.blanket.is_some())
            .fold(0u16, |m, (_, rec)| m | crate::check::derive_delta::bound_mask(p, &rec.generics.predicates));
        if mask != 0 {
            crate::check::derive_delta::masked(&p.adt(a).derives_unlogged(), mask).hash(&mut h);
        }
    }
    Fingerprint(h.finish())
}

/// The content of one impl as selection and its callers see it: header
/// (trait ref pattern), generics and where clauses, associated type and
/// const bindings, and each item's def and signature. Method bodies are
/// not in it (each is its own fn, checked on its own).
fn impl_content(p: &Program, def: DefId) -> u64 {
    let Some(rec) = p.gx.index.peek_def(def) else { return 0 };
    let mut h = FxHasher::default();
    "impl-content-v1".hash(&mut h);
    hash_trait_ref(&mut h, p, &p.tys, &rec.trait_ref);
    // A header's regions for a trait with lifetime params (W-BORROW):
    // callers' borrow checks replay them.
    // Any trait impl's regioned header and where-clauses (tf-borrow r9):
    // a bound that selects the impl replays them.
    if let Some(ir) = p.regions.impl_regions.get(&def) {
        let mut seen = DeepMemo::default();
        for &t in ir.header.iter().chain(ir.assoc.iter().map(|(_, t)| t)) {
            hash_regions_deep(&mut h, p, t, &mut seen);
        }
        ir.facts.hash(&mut h);
        hash_preds_regions(&mut h, p, &ir.preds, &mut seen);
    }
    if let Some(head) = p.regions.impl_heads.get(&def) {
        let mut seen = DeepMemo::default();
        hash_regions_deep(&mut h, p, head.self_ty, &mut seen);
        for &r in &head.trait_lifetimes {
            hash_region(&mut h, r);
        }
        for w in &head.where_lts {
            w.param.hash(&mut h);
            hash_def_pub(&mut h, p, w.trait_def);
            for &r in &w.lifetimes {
                hash_region(&mut h, r);
            }
        }
    }
    hash_generics(&mut h, p, &rec.generics);
    (rec.assoc_tys.len() as u64).hash(&mut h);
    for (d, t) in &rec.assoc_tys {
        hash_def_pub(&mut h, p, *d);
        hash_ty(&mut h, p, &p.tys, *t);
    }
    (rec.assoc_consts.len() as u64).hash(&mut h);
    for (d, c) in &rec.assoc_consts {
        hash_def_pub(&mut h, p, *d);
        hash_const(&mut h, &p.tys, *c);
    }
    (rec.items.len() as u64).hash(&mut h);
    for d in &rec.items {
        hash_def_pub(&mut h, p, *d);
        sig_fingerprint(p, *d).0.hash(&mut h);
    }
    h.finish()
}

/// Folds one visibility into `h`: its form, and for `pub(in path)` the
/// written path by name (never by `Sym` id).
fn hash_vis(h: &mut FxHasher, p: &Program, vis: &VisKind) {
    match vis {
        VisKind::Priv => 0u8.hash(h),
        VisKind::Pub => 1u8.hash(h),
        VisKind::Crate => 2u8.hash(h),
        VisKind::Super => 3u8.hash(h),
        VisKind::In(path) => {
            // By name, as when the segments were a list: their count, then each.
            let segs: Vec<&str> = p.name(*path).split("::").collect();
            4u8.hash(h);
            (segs.len() as u64).hash(h);
            for s in segs {
                s.hash(h);
            }
        }
    }
}

/// Folds one module into `h` by its name path from its crate root, never
/// by its session id. Privacy answers are functions of these paths: the
/// reader's own module is fixed by its def path, which keys its slot.
fn hash_module_path(h: &mut FxHasher, p: &Program, t: &ResolvedTables, m: ModuleId) {
    let path = t.modules.get(m.0 as usize).map_or(&[][..], |info| &info.path[..]);
    (path.len() as u64).hash(h);
    for s in path {
        p.name(*s).hash(h);
    }
}

/// Folds the visibility facts of one def into its `Sig` fingerprint
/// (section 8.1: `Sig` covers vis). These are the def's own visibility
/// and, for an Adt, the visibility of each named field, tuple field,
/// and inherent associated item, each with its defining module. Body
/// checking records a `Sig(adt)` read at every field, constructor, and
/// method privacy check (`check_field_vis` and kin in check/mod.rs), so
/// a visibility-only edit dirties those readers in the walk. Path and
/// re-export privacy are answered by the resolver, which reruns its
/// rewrite whenever `ResolvedTables::rewrite_epoch` moves; the own
/// visibility here also dirties the bodies whose `Binding` reads name
/// the def. Map entries fold order-free (their order is not a fact).
/// Programs without resolver tables are one module: no facts to fold.
fn hash_vis_facts(h: &mut FxHasher, p: &Program, def: DefId) {
    let Some(t) = &p.resolved else { return };
    if let Some(info) = t.def_info.get(&def) {
        hash_vis(h, p, &info.vis);
        hash_module_path(h, p, t, info.module);
    }
    if let Some((m, fields)) = t.field_vis.get(&def) {
        hash_module_path(h, p, t, *m);
        let mut acc = 0u64;
        for (name, vis) in fields {
            let mut e = FxHasher::default();
            p.name(*name).hash(&mut e);
            hash_vis(&mut e, p, vis);
            acc = acc.wrapping_add(e.finish());
        }
        (fields.len() as u64, acc).hash(h);
    }
    // `#[non_exhaustive]` (the type's and each variant's, in order):
    // construction, pattern, and exhaustiveness answers in other
    // crates read it through the same `Sig(adt)` reads as field
    // privacy, so toggling it must move this fingerprint.
    if let Some(a) = p.adt_by_def(def) {
        let adt = p.adt(a);
        adt.non_exhaustive.hash(h);
        for v in &adt.variants {
            v.non_exhaustive.hash(h);
        }
    }
    if let Some((m, fields)) = t.tuple_field_vis.get(&def) {
        hash_module_path(h, p, t, *m);
        (fields.len() as u64).hash(h);
        for vis in fields {
            hash_vis(h, p, vis);
        }
    }
    // Inherent item visibility is not here: its readers record one
    // `AssocVis` read per item.
}

/// Folds one evaluated const value into `h`. `StaticRef` (`StaticPlace`) indices are
/// collect-order positions, not stable content, so they fold the
/// referenced static's name and (depth-capped) value instead.
fn hash_const_value(h: &mut FxHasher, p: &Program, v: &crate::ty::consteval::ConstValue, depth: u32) {
    use crate::ty::consteval::ConstValue;
    match v {
        ConstValue::Int(x) => (0u8, x).hash(h),
        ConstValue::Float(bits, f) => (10u8, bits, f.name()).hash(h),
        ConstValue::Bool(b) => (1u8, b).hash(h),
        ConstValue::Char(c) => (2u8, c).hash(h),
        ConstValue::Str(i) => {
            3u8.hash(h);
            p.ast.strings.get(*i as usize).map_or("", String::as_str).hash(h);
        }
        // Hashed as the text, like a literal of the same text.
        ConstValue::StrBytes(b) => {
            3u8.hash(h);
            std::str::from_utf8(b.as_slice()).unwrap_or("").hash(h);
        }
        ConstValue::Unit => 4u8.hash(h),
        ConstValue::Aggregate(vals) => {
            5u8.hash(h);
            (vals.len() as u64).hash(h);
            for v in vals {
                hash_const_value(h, p, v, depth);
            }
        }
        ConstValue::Variant(variant, vals) => {
            (6u8, variant).hash(h);
            (vals.len() as u64).hash(h);
            for v in vals {
                hash_const_value(h, p, v, depth);
            }
        }
        ConstValue::Repeat(inner, n) => {
            (7u8, n).hash(h);
            hash_const_value(h, p, inner, depth);
        }
        ConstValue::Ref(inner) => {
            8u8.hash(h);
            hash_const_value(h, p, inner, depth);
        }
        ConstValue::FnPtr(f) => {
            11u8.hash(h);
            p.fn_defs.get(*f as usize).map(|d| d.hash.0).hash(h);
        }
        ConstValue::Bytes(b) => {
            12u8.hash(h);
            b.as_slice().hash(h);
        }
        ConstValue::StaticPlace(i, path) => {
            (13u8, path).hash(h);
            hash_const_value(h, p, &ConstValue::StaticRef(*i), depth);
        }
        ConstValue::StaticRef(i) => {
            9u8.hash(h);
            match p.statics.get(*i as usize) {
                Some(s) => {
                    p.name(s.name).hash(h);
                    if depth < 8 {
                        hash_const_value(h, p, &s.value, depth + 1);
                    }
                }
                None => 0u8.hash(h),
            }
        }
    }
}

/// The fingerprint of one const or static item's evaluated value, made
/// once per item (`ConstItem::value_fp`): `Sig` reads in every walk, the
/// const fn value check, and the statics fingerprint all fold it, and a
/// large table's value is costly to walk.
pub(crate) fn value_fp(p: &Program, value: &crate::ty::consteval::ConstValue, cell: &std::sync::OnceLock<u64>) -> u64 {
    *cell.get_or_init(|| {
        let mut h = FxHasher::default();
        hash_const_value(&mut h, p, value, 0);
        h.finish()
    })
}

thread_local! {
    /// Set by a fingerprint that read state mono still writes
    /// (`Program::read_fingerprint_stable`).
    static MONO_READ: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The fingerprint of one def's resolved signature (section 8.1 `Sig` node):
/// signature types with defs in stable form, plus the def's visibility
/// facts (`hash_vis_facts`). Types hash *deeply* (see
/// `hash_ty_deep`): a field, layout, derive, or discriminant edit to a
/// named Adt changes every signature that names it, so the dirty walk
/// rechecks bodies that read the signature. That is what lets the walk
/// cover type edits, not only signature text edits. Const and static
/// defs fold their evaluated value in (a value edit that keeps the
/// value invalidates nothing); type aliases fold their resolved target.
/// Generics and predicates join when generic collect fills them
/// (W-TRAITS-CORE); today they are empty for every user def.
fn sig_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "sig-v4".hash(&mut h);
    hash_vis_facts(&mut h, p, def);
    hash_def_pub(&mut h, p, def);
    let mut seen = DeepMemo::default();
    if let Some(local) = p.local_def(def.hash).filter(|l| p.def_id(*l) == def) {
        let f = p.fn_info(local);
        0u8.hash(&mut h);
        // Types fold shallow here, by identity: what a caller reads of a
        // type's content it records itself (`Sig` reads of the Adts it
        // opens, a `Layout` read of each type it holds by value,
        // `record_type_layout_reads`), so an edit deep inside a type
        // dirties those bodies, not every caller of every fn that names
        // it. The same holds for a method's Self type.
        match f.owner {
            Some(a) => hash_def_pub(&mut h, p, p.def_of_adt(a)),
            None => 0u64.hash(&mut h),
        }
        match f.self_kind {
            None => 0u8.hash(&mut h),
            Some(SelfKind::Value) => 1u8.hash(&mut h),
            Some(SelfKind::Ref) => 2u8.hash(&mut h),
            Some(SelfKind::RefMut) => 3u8.hash(&mut h),
            Some(SelfKind::Typed) => 4u8.hash(&mut h),
        }
        (f.params.len() as u64).hash(&mut h);
        for t in &f.params {
            hash_ty(&mut h, p, &p.tys, *t);
        }
        // Qualifiers are part of the caller-visible signature (an
        // `unsafe fn` flip changes what callers may do). Parameter
        // names and patterns are not: they bind only the body's own
        // locals, and the driver guards those with its per-slot head
        // hash, so a param rename reuses callers.
        (f.def(&p.ast).qual.is_const, f.def(&p.ast).qual.is_async, f.def(&p.ast).qual.is_unsafe, f.def(&p.ast).variadic).hash(&mut h);
        // The written visibility and the defining module: a caller of an
        // `impl dyn Tr` method checks access against them at the call
        // (`Ctx::check_dyn_method_vis`). Methods have no `def_info`
        // entry, so `hash_vis_facts` does not cover them.
        if let Some(t) = &p.resolved {
            hash_vis(&mut h, p, &crate::resolve::imports::vis_from_ast(&f.def(&p.ast).vis, &p.interner));
            if let Some(&m) = t.fn_module.get(local.0 as usize) {
                hash_module_path(&mut h, p, t, m);
            }
        }
        // `impl dyn Tr` vs `impl dyn Tr + '_`: the same types, but only
        // the first needs a `'static` receiver (check::object).
        p.gx.static_dyn_fns.contains(&local).hash(&mut h);
        // `#[track_caller]` adds a C parameter callers pass (check/caller.rs).
        crate::check::caller::is_track_caller(p, local).hash(&mut h);
        hash_ty(&mut h, p, &p.tys, f.ret);
        // A generic fn's `impl Trait` return: callers' revealed checks
        // read its hidden type (check/opaque.rs); one that holds the
        // value reads its layout (`record_type_layout_reads`). Mono can
        // still reveal it (`read_fingerprint_stable`).
        let od = crate::check::generics::opaque_def(def);
        if p.gx.opaques.contains_key(&od) {
            MONO_READ.set(true);
        }
        if let Some(&hidden) = p.gx.opaque_hidden.get(&od) {
            hash_ty(&mut h, p, &p.tys, hidden);
        }
        // The bounds of its `impl Trait` return: all callers see of it
        // (`impl Sh + Clone` to `impl Sh + Send` drops `.clone()`).
        match p.gx.opaques.get(&crate::check::generics::opaque_def(def)) {
            Some(o) => {
                (o.bounds.len() as u64).hash(&mut h);
                for pred in &o.bounds {
                    hash_predicate(&mut h, p, &p.tys, pred);
                }
                // Their written regions (`&'static` in `impl Fn(&u8) ->
                // &'static u8`), which the bounds erase.
                for b in &o.fn_outs {
                    for &t in b.inputs.iter().chain(b.output.iter()) {
                        hash_regions_deep(&mut h, p, t, &mut seen);
                    }
                }
            }
            None => u64::MAX.hash(&mut h),
        }
        // `fn f(x: &str)` and `fn f(x: &'static str)` erase alike;
        // callers' borrow checks read the region signature (W-BORROW).
        hash_region_sig(&mut h, p, p.regions.fns.get(&local));
        hash_region_sig(&mut h, p, p.regions.opaque_sigs.get(&local));
        // Callers of a trait impl method see the trait's signature too
        // (`trait_view`): a trait-only region edit moves the impl's.
        if let Some(m) = crate::borrowck::impl_trait_method(p, local) {
            hash_region_sig(&mut h, p, p.regions.trait_methods.get(&m));
        }
        f.ret_borrows_from.map(|i| i as u64 + 1).unwrap_or(0).hash(&mut h);
        // A generic fn's parameters and bounds (its impl's too, merged
        // in by collect): callers prove the bounds (generic reuse).
        match p.gx.fn_templates.get(local.0 as usize) {
            Some(Some(t)) => hash_generics(&mut h, p, &t.generics),
            _ => u64::MAX.hash(&mut h),
        }
    } else if p.adt_by_def(def).is_some() {
        1u8.hash(&mut h);
        // Its own content, the Adts its fields name by identity (as for
        // a fn above): a body that opens a field's type records that
        // type's `Sig` itself, and one that holds a value its `Layout`.
        hash_adt_layout(&mut h, p, def, false, &mut |h, d| hash_def_pub(h, p, d));
        // Lifetime params and field regions (W-BORROW): `&'a T` and
        // `&'static T` fields erase alike.
        adt_deep(p, Deep::Regions, def, &mut seen).hash(&mut h);
    } else if let Some(data) = p.defs.get(def) {
        2u8.hash(&mut h);
        // Const and static payloads are found by def; aliases by flat
        // name, which the def record carries.
        if let Some(item) = p.const_by_def(def).map(|i| &p.consts[i as usize]) {
            0u8.hash(&mut h);
            hash_ty_deep(&mut h, p, &p.tys, item.ty, &mut seen);
            value_fp(p, &item.value, &item.value_fp).hash(&mut h);
            // Whether `&C` is promoted (lower `promotable`).
            item.qualif.hash(&mut h);
        } else if let Some(item) = p.static_by_def(def).map(|i| &p.statics[i as usize]) {
            // A static's type folds by identity: its readers hold a place,
            // and its value is emitted in the glue unit, whose rebuild
            // reads the deep type (`statics_fingerprint`). A const's value
            // is inlined into its readers, so its type folds deep.
            1u8.hash(&mut h);
            item.mutable.hash(&mut h);
            hash_ty(&mut h, p, &p.tys, item.ty);
            value_fp(p, &item.value, &item.value_fp).hash(&mut h);
            // A `thread_local!` key's form and init fn (W-TLS): key
            // method calls carry both in their IR (lower/tls.rs).
            if let Some(k) = item.tls {
                k.eager.hash(&mut h);
                hash_def_pub(&mut h, p, p.def_id(k.init));
            }
        } else if let Some(ty) = p.aliases.get(&data.name) {
            // The target by identity, as a signature type.
            1u8.hash(&mut h);
            hash_ty(&mut h, p, &p.tys, *ty);
        } else if let Some(la) = p.gx.generic_aliases.get(&data.name) {
            // A lifetime alias (W-BORROW) resolves at each use: its tokens
            // carry the regions, its erased body the type.
            2u8.hash(&mut h);
            la.body_hash.hash(&mut h);
            hash_ty(&mut h, p, &p.tys, la.erased);
        } else {
            p.name(data.name).hash(&mut h);
        }
    } else if let Some(item) = p.static_by_def(def).map(|i| &p.statics[i as usize]) {
        // A nested (fn-body) static: collect gives it a def in
        // `static_defs` but no `Defs` record, so the branch above
        // misses it. Its value must still fold in: `statics_fingerprint`
        // is the only record that makes a later build rebuild the
        // glue unit when a nested static's initializer edits.
        2u8.hash(&mut h);
        1u8.hash(&mut h);
        item.mutable.hash(&mut h);
        hash_ty(&mut h, p, &p.tys, item.ty);
        value_fp(p, &item.value, &item.value_fp).hash(&mut h);
        if let Some(k) = item.tls {
            k.eager.hash(&mut h);
            hash_def_pub(&mut h, p, p.def_id(k.init));
        }
    } else {
        3u8.hash(&mut h);
    }
    // A trait method's region signature (W-BORROW): calls through a
    // bound or a stub read it, and the trait item's text alone does not
    // reach this node.
    if let Some(rs) = p.regions.trait_methods.get(&def) {
        hash_region_sig(&mut h, p, Some(rs));
    }
    // Param defaults (W-CHECK-G): `S<u8>` means `S<u8, D>`, so a default
    // edit changes what every path that omits the arg names. The default
    // folds by identity, as signature types do: a reader of the type it
    // names records its own reads.
    if let Some(ds) = p.gx.param_defaults.get(&def) {
        for d in ds {
            match d {
                Some(GenericArg::Ty(t)) => hash_ty(&mut h, p, &p.tys, *t),
                Some(GenericArg::Const(c)) => p.tys.const_kind(*c).hash(&mut h),
                _ => 0u8.hash(&mut h),
            }
        }
    }
    Fingerprint(h.finish())
}

/// A `DropCk` node: the drop-check constraint of Adt template `def`
/// (check/dropck.rs `template_constraint_hash`), memoized per Adt while
/// the program memo is on.
fn drop_check_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let slot = p.adt_by_def(def).and_then(|a| p.fp_memo.dropck.get(a.0 as usize));
    if let Some(v) = slot.and_then(|s| s.get()) {
        return Fingerprint(*v);
    }
    let v = crate::check::derive_delta::unlogged(|| crate::check::dropck::template_constraint_hash(p, def));
    if let Some(s) = slot {
        let _ = s.set(v);
    }
    Fingerprint(v)
}

/// The fingerprint of the program's statics as the glue unit emits
/// them: each static's `Sig` fingerprint (evaluated value; its
/// visibility rides along, so a visibility edit costs one glue rebuild)
/// and its type's deep content, in definition order. The driver stores the fingerprint of
/// the statics last built into a glue unit and rebuilds that unit
/// when a later build's statics differ. This must be a built-state
/// comparison, not an edit trigger: a `check` request consumes the
/// edit that moved a value, and the following `build` request sees
/// an unchanged file.
/// The (Adt, method slot) pairs glue calls: written Display/Debug `fmt`
/// methods (`gx.fmt_methods`) and Drop methods (`gx.drop_methods`), in a
/// stable order. `slots` is the build's fn slot table.
pub(crate) fn glue_method_slots_fp(p: &Program, slots: &[u32]) -> u64 {
    let mut h = FxHasher::default();
    "glue-slots-v1".hash(&mut h);
    let slot = |f: crate::def::LocalDefId| slots.get(f.0 as usize).copied().unwrap_or(u32::MAX);
    let mut fm: Vec<(u32, u8, u32)> = p.gx.fmt_methods.iter().map(|(&(a, k), &f)| (a.0, k, slot(f))).collect();
    fm.sort_unstable();
    fm.hash(&mut h);
    let mut dm: Vec<(u32, u32)> = p.gx.drop_methods.iter().map(|(&a, &f)| (a.0, slot(f))).collect();
    dm.sort_unstable();
    dm.hash(&mut h);
    h.finish()
}

pub(crate) fn statics_fingerprint(p: &Program) -> u64 {
    let mut h = FxHasher::default();
    "statics-v1".hash(&mut h);
    (p.static_defs.len() as u64).hash(&mut h);
    for &def in &p.static_defs {
        sig_fingerprint(p, def).0.hash(&mut h);
        // The glue unit emits the value in the type's C layout: the type's
        // deep content joins here (the `Sig` folds it by identity).
        if let Some(item) = p.static_by_def(def).map(|i| &p.statics[i as usize]) {
            hash_ty_deep(&mut h, p, &p.tys, item.ty, &mut DeepMemo::default());
        }
    }
    h.finish()
}

// ---------- Query functions (section 8.2) ----------

/// The signature payload a `sig_of` query returns. Fn and Adt payloads still
/// live in the compat tables today (`FnInfo`, `AdtDef`); the query is the
/// only door to them that records a read. Other defs answer with their
/// `Defs` record until their payloads land.
#[allow(dead_code)] // The `Other` payload is read when non-fn/Adt payloads land.
pub enum SigOf<'p> {
    Fn(&'p FnInfo),
    Adt(&'p AdtDef),
    Other(&'p DefData),
    Missing,
}

impl<'a> Program {
    /// Resolves one module name in one namespace and records the `Binding`
    /// read. This is the frozen binding query wave A codes against: callers
    /// get a `DefId` and turn it into a session-local index through
    /// `local_def`, `adt_by_def`, or `Defs` queries, never the other way.
    ///
    /// When the crate went through the resolver (W-RESOLVE), this reads
    /// the section 1.3 module tables: per-module bindings with glob
    /// ambiguity, plus the flat-name index the merged AST's rewritten
    /// names resolve through (the checker asks in the root module). A
    /// table miss falls through to the single-file layer below, which
    /// also still answers for the builtin `String`/`Vec`/`Option`
    /// prelude defs. With no resolved tables (single-file programs),
    /// only that layer answers: one root module, never `Ambiguous`.
    /// The signature is the frozen S7 one; no caller changed.
    pub fn binding(&self, reads: &mut Reads, module: ModuleId, ns: Namespace, name: Sym) -> BindingRes {
        let res = self.binding_res(module, ns, name);
        reads.record_with(ReadKey::Binding(BindingKey { module: self.mod_key(module), ns, name }), res == BindingRes::Absent, || binding_fingerprint(self, res));
        res
    }

    /// The read key of module `m` (`ModKey`).
    pub(crate) fn mod_key(&self, m: ModuleId) -> ModKey {
        match &self.resolved {
            Some(t) => ModKey(t.module_key(m)),
            None => ModKey::bare(m),
        }
    }

    /// The module a read key names in this program, if it has one.
    pub(crate) fn mod_of_key(&self, k: ModKey) -> Option<ModuleId> {
        match &self.resolved {
            Some(t) => t.module_by_key(k.0),
            None => (k.0 >> 63 == 1).then_some(ModuleId(k.0 as u32)),
        }
    }

    /// `binding_res` for a stored key: Absent when its module is gone.
    pub(crate) fn binding_res_at(&self, k: &BindingKey) -> BindingRes {
        match self.mod_of_key(k.module) {
            Some(m) => self.binding_res(m, k.ns, k.name),
            None => BindingRes::Absent,
        }
    }

    /// The binding answer without recording. The dirty walk replays old
    /// reads against the new program through this; `binding` is the only
    /// recording door. The resolver tables (W-RESOLVE) answer here
    /// first, so replays see the same answers as `binding`.
    pub(crate) fn binding_res(&self, module: ModuleId, ns: Namespace, name: Sym) -> BindingRes {
        // Spliced std source sees no user names (see `STD_MODULE`).
        if module == crate::ty::defs::STD_MODULE {
            return BindingRes::Absent;
        }
        // W-RESOLVE: the section 1.3 module tables answer first when the
        // crate went through the resolver; a miss falls through to the
        // single-file layer (builtins) below.
        if let Some(tables) = &self.resolved
            && let Some(res) = tables.binding(module, ns, name)
        {
            return res;
        }
        if module != ROOT_MODULE {
            return BindingRes::Absent;
        }
        match ns {
            Namespace::Value => match self.fn_names.get(&name) {
                Some(&f) => BindingRes::Def(self.def_id(f)),
                None => match self.type_names.get(&name) {
                    // A struct's name in value space is its constructor.
                    Some(&a) if !self.adt(a).is_enum => BindingRes::Def(self.def_of_adt(a)),
                    _ => BindingRes::Absent,
                },
            },
            Namespace::Type => match self.type_names.get(&name) {
                Some(&a) => BindingRes::Def(self.def_of_adt(a)),
                None => {
                    let b = self.tys.builtins();
                    if name == self.known.String {
                        BindingRes::Def(b.string)
                    } else if name == self.known.Vec {
                        BindingRes::Def(b.vec)
                    } else if name == self.known.Option {
                        BindingRes::Def(b.option)
                    } else {
                        BindingRes::Absent
                    }
                }
            },
            Namespace::Macro => BindingRes::Absent,
        }
    }

    /// The macro-namespace binding query of section 8.2, recorded at every
    /// expansion. It is `binding` in the macro namespace; the separate name
    /// keeps expansion call sites from depending on namespace plumbing.
    #[allow(dead_code)] // First caller is macro expansion (W-MACRO, wave A).
    pub fn macro_binding(&self, reads: &mut Reads, module: ModuleId, name: Sym) -> BindingRes {
        self.binding(reads, module, Namespace::Macro, name)
    }

    /// The candidate set for one method probe, recorded hit or miss
    /// (section 2.10 step 5). Probe every form in `ReceiverForm::PROBE_ORDER`
    /// and stop at the first hit, exactly as method resolution does: a body
    /// that picked a trait method must recheck when an inherent method of
    /// the same name appears, and only the recorded probes say so.
    ///
    /// Today only inherent user methods exist here, one candidate
    /// per inherent impl that defines the name on this Adt.
    /// Builtin methods on builtin and primitive heads still dispatch through
    /// the compat path in `check` and answer as an empty set here; the read
    /// is still recorded, with the probe itself in the fingerprint (see
    /// `method_set_fingerprint`), so the probe is on record when source
    /// std turns those builtins into real defs.
    pub fn method_set(&self, reads: &mut Reads, head: Head, name: Sym, form: ReceiverForm) -> MethodSet {
        let set = self.method_candidates(head, name, form);
        let failed = set.candidates.is_empty();
        let key = MethodSetKey { head, name, form };
        reads.record_with(ReadKey::MethodSet(key), failed, || method_set_fingerprint(self, &key, &set));
        set
    }

    /// Records the `MethodSet` reads of every receiver form for one name on
    /// one Adt. A lookup that reads the inherent method tables directly (a
    /// `S::f` path, an inherent-first check) depends on the same candidates
    /// a method probe sees, so it records the same reads.
    pub fn inherent_reads(&self, reads: &mut Reads, adt: DefId, name: Sym) {
        for form in ReceiverForm::PROBE_ORDER {
            let _ = self.method_set(reads, Head::Adt(adt), name, form);
        }
    }

    /// The method candidate set without recording. See `binding_res`.
    /// Mono instances of an inherent template join the compat method
    /// table (`generics::fn_instance`), but the template is the
    /// candidate: which instances exist depends on what collect
    /// materialized, so with them the set (and a `MethodSet` read)
    /// would differ between a warm and a cold program of the same text.
    fn method_candidates(&self, head: Head, name: Sym, form: ReceiverForm) -> MethodSet {
        let mut set = MethodSet::default();
        if let Head::Adt(def) = head
            && let Some(a) = self.adt_by_def(def)
            && let Some(fs) = self.methods.get(&(a, name))
        {
            for &f in fs.iter().filter(|f| self.gx.fn_class.get(f.0 as usize) != Some(&crate::check::generics::FnClass::Instance)) {
                let receiver = match self.fn_info(f).self_kind {
                    Some(SelfKind::Value) | Some(SelfKind::Typed) => Some(ReceiverForm::Value),
                    Some(SelfKind::Ref) => Some(ReceiverForm::Ref),
                    Some(SelfKind::RefMut) => Some(ReceiverForm::RefMut),
                    None => None,
                };
                // An associated fn without `self` surfaces in the first probe
                // only, marked with no receiver (see `MethodCandidate`).
                if receiver == Some(form) || (receiver.is_none() && form == ReceiverForm::Value) {
                    set.candidates.push(MethodCandidate { def: self.def_id(f), receiver, trait_: None });
                }
            }
        }
        set
    }

    /// The impl bucket for one trait and Self head, recorded at every
    /// selection (section 8.2; `traits::solve` step 2 calls it through
    /// `SolveCx::record_impl_set`). See `ImplSet` for which buckets fill.
    pub fn impl_set(&self, reads: &mut Reads, trait_: DefId, head: Head) -> ImplSet {
        let set = self.impl_bucket(trait_, head);
        let key = ImplSetKey { trait_, head };
        reads.record_with(ReadKey::ImplSet(key), set.impls.is_empty(), || impl_set_fingerprint(self, &key, &set));
        // Only a derivable trait's answer reads the derive list (its
        // derived record, or the lack of one). Another trait's impls that
        // a derive list decides (a blanket bounded by `Debug`) prove that
        // bound as a goal of its own, which records its own read.
        let bit = crate::check::derive_delta::trait_bit(self, trait_);
        if let Head::Adt(def) = head
            && bit != 0
            && self.adt_by_def(def).is_some()
        {
            self.record_derive_bits(reads, def, bit);
        }
        set
    }

    /// The def a `Derives` read of Adt `a` keys on: the template's, for
    /// an instance (instances copy their template's list). None for a
    /// placeholder row.
    pub(crate) fn derive_def(&self, a: AdtId) -> Option<DefId> {
        match self.gx.adt_instance_of.get(a.0 as usize).copied().flatten() {
            Some((template, _)) => Some(template),
            None => self.gx.adt_info.get(a.0 as usize).map(|&(def, _)| def).filter(|&d| d != DefId::PLACEHOLDER),
        }
    }

    /// Records a `Derives` read of the Adt template `def`.
    /// check/derive_delta.rs calls it for each def a scope noted.
    pub(crate) fn record_derives(&self, reads: &mut Reads, def: DefId) {
        reads.record_with(ReadKey::Derives(def), self.adt_by_def(def).is_none(), || derives_fingerprint(self, def));
    }

    /// Records a `DeriveBits` read of the traits `mask` of the Adt template
    /// `def` (check/derive_delta.rs `bit`).
    pub(crate) fn record_derive_bits(&self, reads: &mut Reads, def: DefId, mask: u16) {
        reads.record_with(ReadKey::DeriveBits(def, mask), self.adt_by_def(def).is_none(), || derive_bits_fingerprint(self, def, mask));
    }

    /// Records a `DropCk` read of the Adt template `def`.
    pub(crate) fn record_drop_check(&self, reads: &mut Reads, def: DefId) {
        reads.record_with(ReadKey::DropCk(def), self.adt_by_def(def).is_none(), || drop_check_fingerprint(self, def));
    }

    /// Records a `LangImpls` read of the Adt template `def`.
    pub(crate) fn record_lang_impls(&self, reads: &mut Reads, def: DefId) {
        reads.record_with(ReadKey::LangImpls(def), self.gx.index.impls_naming(def).next().is_none(), || lang_impls_fingerprint(self, def));
    }

    /// Records a `LangImpls` read of each user Adt template that the
    /// types `types` name, arguments included (one body's expression,
    /// pattern, and local types): a lookup of a std or lang trait impl for
    /// one of them, found or not, is a read of that Adt's impls.
    pub fn record_type_lang_reads(&self, reads: &mut Reads, tys: &impl TyIntern, types: impl IntoIterator<Item = Ty>) {
        if reads.off {
            return;
        }
        let mut seen: FxMap<Ty, ()> = FxMap::default();
        let mut defs: Vec<DefId> = Vec::new();
        for t in types {
            if seen.insert(t, ()).is_none() {
                collect_adt_defs(self, tys, t, &mut defs);
            }
        }
        defs.sort_unstable_by_key(|d| (d.krate.0, d.hash.0));
        defs.dedup();
        for def in defs {
            if self.user_adt(def) {
                self.record_lang_impls(reads, def);
            }
        }
    }

    /// Records a `Layout` read of each user Adt template that one body's
    /// expression, pattern, and local types hold by value:
    /// inline, in a tuple, array, or enum payload, in a closure's captures,
    /// an opaque's hidden type, or the args of a generic type that holds
    /// them (`points_at_args`). Drop glue, copies, sizes, and tags of a value follow
    /// its deep layout, which fn and Adt signatures fold only shallow
    /// (`sig_fingerprint`). A reference, raw pointer, `Box`, `Vec`, `Rc`,
    /// `Arc`, or hashed collection points at its target, so a type held
    /// only behind one costs no read here; the readers that look through
    /// one record their own (auto traits, release C field offsets).
    pub fn record_type_layout_reads(&self, reads: &mut Reads, tys: &impl TyIntern, types: impl IntoIterator<Item = Ty>) {
        if reads.off {
            return;
        }
        let mut defs: Vec<DefId> = Vec::new();
        let mut hidden: Vec<Ty> = Vec::new();
        by_value_adts(self, tys, types, &mut defs, &mut hidden);
        // Hidden types live in the program's interner, as do theirs.
        let mut opened: FxMap<Ty, ()> = FxMap::default();
        while !hidden.is_empty() {
            let next: Vec<Ty> = std::mem::take(&mut hidden).into_iter().filter(|&t| opened.insert(t, ()).is_none()).collect();
            by_value_adts(self, &self.tys, next, &mut defs, &mut hidden);
        }
        defs.sort_unstable_by_key(|d| (d.krate.0, d.hash.0));
        defs.dedup();
        for def in defs {
            if self.user_adt(def) {
                let _ = self.layout_of(reads, def);
            }
        }
    }

    /// Notes (check/derive_delta.rs, `bit::LAYOUT`) a `Layout` read of Adt
    /// `a` (its template, for an instance) and of each user Adt its
    /// instance args name: codegen asked its layout (cgen `c_layout`), as
    /// release C does for a field read at an offset and the LLVM backend for
    /// a pointee's size, in a body that may hold it only behind a pointer.
    pub(crate) fn note_adt_layout(&self, a: AdtId) {
        if !crate::check::derive_delta::open() {
            return;
        }
        let Some(def) = self.derive_def(a) else { return };
        let mut defs = vec![def];
        if let Some(Some((_, args))) = self.gx.adt_instance_of.get(a.0 as usize) {
            for g in self.tys.args(*args) {
                if let GenericArg::Ty(t) = *g {
                    collect_adt_defs(self, &self.tys, t, &mut defs);
                }
            }
        }
        defs.retain(|&d| self.user_adt(d));
        crate::check::derive_delta::note_defs(&defs, crate::check::derive_delta::bit::LAYOUT);
    }

    /// True for an Adt template of user source: not spliced std source,
    /// not a shipped crate, not a builtin def. Only these key
    /// `LangImpls` reads (`ImplIndex::name_adts`): no user impl of a std
    /// trait can name only std types.
    pub(crate) fn user_adt(&self, def: DefId) -> bool {
        self.adt_by_def(def).is_some_and(|a| {
            let span = self.adts[a.0 as usize].span;
            !self.std_source_span(span) && self.shipped_crate_at(span).is_none()
        })
    }

    /// The user Adt templates (`user_adt`) the trait ref arguments `args`
    /// name: the Adts a written impl's `LangImpls` reads key on.
    pub(crate) fn lang_named_adts(&self, args: crate::ty::ArgsId) -> Vec<DefId> {
        let mut defs = Vec::new();
        for a in self.tys.args(args) {
            if let GenericArg::Ty(t) = *a {
                collect_adt_defs(self, &self.tys, t, &mut defs);
            }
        }
        defs.retain(|&d| self.user_adt(d));
        defs.sort_unstable_by_key(|d| (d.krate.0, d.hash.0));
        defs.dedup();
        defs
    }

    /// True for a written impl with trait ref `tr` that `LangImpls` reads
    /// cover in place of the trait-system key (gen_reuse.rs `trait_key`):
    /// a std or lang trait (not local, no `ImplSet` reads) and a user Adt
    /// in the trait ref.
    pub(crate) fn lang_keyed_impl(&self, tr: &TraitRef) -> bool {
        !self.impls_read_covered(tr.def) && !self.gx.index.trait_record(tr.def).is_some_and(|r| r.local) && !self.lang_named_adts(tr.args).is_empty()
    }

    /// True for a trait whose impls fill `ImplSet` buckets, and so stay out
    /// of the trait-system key (`gen_reuse::trait_key`): a user trait (a
    /// trait item of this crate) with no associated const. A `<T as K>::C`
    /// path reads an impl's const with no recorded read.
    pub(crate) fn impls_read_covered(&self, trait_: DefId) -> bool {
        self.gx.index.trait_record(trait_).is_some_and(|r| r.local && r.assoc_items.iter().all(|&(_, _, is_type)| is_type))
    }

    /// The impls of trait `trait_` that a Self type with this head can
    /// select: the same head after `Head::of` peels references, or a Self
    /// pattern with no head (a blanket impl). An `Unknown` head takes every
    /// impl. For a trait `impls_read_covered` does not take (a std or lang
    /// trait, a user trait with an associated const), only its written
    /// impls: the trait-system key leaves out a std or lang trait impl that
    /// names a user Adt (`impl PartialEq<G> for i32`), and one added under
    /// an unchanged body can make its call ambiguous (Sol's const-body
    /// review, blocker 1). Derived impls are read through derive lists.
    fn impl_bucket(&self, trait_: DefId, head: Head) -> ImplSet {
        let mut set = ImplSet::default();
        let covered = self.impls_read_covered(trait_);
        for &id in self.gx.index.impls_of_trait(trait_) {
            let rec = if covered { self.gx.index.get(id) } else { self.gx.index.peek(id) };
            if !covered && rec.synthetic != crate::traits::index::Synthetic::None {
                continue;
            }
            let h = Head::of(&self.tys, rec.self_ty(&self.tys));
            if head == Head::Unknown || h == Head::Unknown || h == head {
                set.impls.push(rec.def);
            }
        }
        set
    }

    /// One def's resolved signature. Callers that only need identity facts
    /// (kind, parent, generics, param env) use `Defs` queries, which read
    /// this same `Sig` node per section 2.1; `sig_of` is for the payload.
    pub fn sig_of(&self, reads: &mut Reads, def: DefId) -> SigOf<'_> {
        let (out, failed) = if let Some(local) = self.local_def(def.hash).filter(|l| self.def_id(*l) == def) {
            (SigOf::Fn(self.fn_info(local)), false)
        } else if let Some(a) = self.adt_by_def(def) {
            (SigOf::Adt(self.adt(a)), false)
        } else if let Some(data) = self.defs.get(def) {
            (SigOf::Other(data), false)
        } else {
            (SigOf::Missing, true)
        };
        reads.record_with(ReadKey::Sig(def), failed, || sig_fingerprint(self, def));
        out
    }

    /// The layout fingerprint of one Adt def (`layout_fingerprint`),
    /// recorded as a `Layout` read. It is separate from the Adt's `Sig`
    /// fingerprint: a method or visibility edit on the type does not
    /// move it, and a field, repr, or discriminant edit of the type or of
    /// one it holds by value does.
    pub fn layout_of(&self, reads: &mut Reads, adt: DefId) -> Option<Fingerprint> {
        let known = self.adt_by_def(adt).is_some() || self.defs.get(adt).is_some();
        if !known {
            reads.record_with(ReadKey::Layout(adt), true, || layout_fingerprint(self, adt));
            return None;
        }
        if let Some(r) = reads.recorded(&ReadKey::Layout(adt)) {
            return Some(r.fingerprint);
        }
        let fp = layout_fingerprint(self, adt);
        reads.record(ReadKey::Layout(adt), fp, false);
        Some(fp)
    }

    /// Records a `Layout` read for every Adt named inside one type.
    /// Body checking uses this where it consumes a layout answer
    /// directly (`size_of`/`align_of` on a compound written type,
    /// `offset_of!`, layout queries inside body const evaluation): a
    /// written-type `Binding` read only names the outermost path, so
    /// `[S; 2]` or `(S, u8)` would otherwise record nothing for `S`.
    pub fn record_layout_reads(&self, reads: &mut Reads, tys: &impl TyIntern, t: Ty) {
        if reads.off {
            return;
        }
        let mut defs = Vec::new();
        collect_adt_defs(self, tys, t, &mut defs);
        for def in defs {
            let _ = self.layout_of(reads, def);
        }
    }

    /// Records the reads of a structural answer (an auto trait, a derive
    /// glue walk, `kind` of `answer`) about one type: for every Adt inside
    /// it that the walk looks at (not behind the pointers whose answer is
    /// fixed, `Behind`: `Rc<Checker>: Clone` reads nothing of `Checker`),
    /// the `Answer` of a user Adt (for one with params, its shape:
    /// `adt_shape`), else its `Structure`.
    pub(crate) fn record_structure_reads(&self, reads: &mut Reads, tys: &impl TyIntern, t: Ty, behind: Behind, kind: u8) {
        if reads.off {
            return;
        }
        let mut defs = Vec::new();
        collect_adt_defs_where(self, tys, t, &mut defs, &|x| stops_at(tys, x, behind));
        defs.sort_unstable_by_key(|d| (d.krate.0, d.hash.0));
        defs.dedup();
        for def in defs {
            // A generic (or lifetime-generic) Adt's answer reads its shape
            // (`adt_shape`, through `answer_fingerprint`) in place of its whole
            // deep `Structure`.
            if self.user_adt(def) {
                reads.record_with(ReadKey::Answer(def, kind), false, || answer_fingerprint(self, def, kind));
            } else {
                let known = self.adt_by_def(def).is_some() || self.defs.get(def).is_some();
                reads.record_with(ReadKey::Structure(def), !known, || structure_fingerprint(self, def));
            }
        }
    }

    /// The `assoc_vis` entry of inherent item `name` of Adt `def`.
    fn assoc_vis_entry(&self, def: DefId, name: Sym) -> Option<&(VisKind, ModuleId)> {
        self.resolved.as_ref()?.assoc_vis.get(&def)?.get(&name)
    }

    /// Records the `AssocVis` read of inherent item `name` of Adt `def`.
    pub(crate) fn record_assoc_vis(&self, reads: &mut Reads, def: DefId, name: Sym) {
        let entry = self.assoc_vis_entry(def, name);
        reads.record_with(ReadKey::AssocVis(def, name), entry.is_none(), || assoc_vis_fingerprint(self, entry));
    }

    /// Whether a user trait is defined in or imported into `module`
    /// (under any name, `as _` included), recorded as a `TraitInScope`
    /// read. Method probes ask this for each candidate trait; the
    /// answer has no binding read of its own, since the import may use
    /// any name. Without resolver tables, and for a trait the tables do
    /// not know, every local trait counts as in scope.
    pub fn trait_in_module(&self, reads: &mut Reads, module: ModuleId, trait_def: DefId) -> bool {
        let ans = self.trait_in_module_answer(module, trait_def);
        reads.record_with(ReadKey::TraitInScope(self.mod_key(module), trait_def), !ans, || trait_in_scope_fingerprint(ans));
        ans
    }

    /// Whether `module` imports the std item `std_mod::name` (or with `name` `*`, globs
    /// `std_mod`) at module level, recorded as a `StdImport` read.
    pub(crate) fn std_import(&self, reads: &mut Reads, module: ModuleId, std_mod: &str, name: &str) -> bool {
        let (std_mod, name) = (self.interner.intern(std_mod), self.interner.intern(name));
        let ans = self.std_import_answer(module, std_mod, name);
        reads.record_with(ReadKey::StdImport(self.mod_key(module), std_mod, name), !ans, || trait_in_scope_fingerprint(ans));
        ans
    }

    /// The `std_import` answer without recording.
    pub(crate) fn std_import_answer(&self, module: ModuleId, std_mod: Sym, name: Sym) -> bool {
        let Some(res) = &self.resolved else { return false };
        let roots = |s: Sym| matches!(self.interner.get(s), "std" | "core" | "alloc");
        if self.interner.get(name) == "*" {
            return res.std_globs.iter().any(|(m, path)| *m == module && path.len() == 2 && roots(path[0]) && path[1] == std_mod);
        }
        let ns = crate::resolve::imports::ns_index(Namespace::Type) as u8;
        res.std_aliases
            .iter()
            .any(|(&(m, n, _), (_, path))| m == module && n == ns && path.len() == 3 && roots(path[0]) && path[1] == std_mod && path[2] == name)
    }

    /// The `trait_in_module` answer without recording. See `binding_res`.
    pub(crate) fn trait_in_module_answer(&self, module: ModuleId, trait_def: DefId) -> bool {
        use crate::resolve::imports::{BindState, ns_index};
        let Some(res) = &self.resolved else { return true };
        let Some(info) = res.def_info.get(&trait_def) else { return true };
        info.module == module
            || res.maps.get(module.0 as usize).is_some_and(|maps| {
                maps[ns_index(Namespace::Type)]
                    .values()
                    .any(|s| matches!(s, BindState::One(b) if res.target_def(b.target) == trait_def))
            })
    }

    /// The kind of a def a binding resolved to, through the `Defs` table.
    /// Callers use it to tell a free fn from a struct constructor without
    /// reading the checker's name maps. Reads no node beyond the `Binding`
    /// read that produced the def.
    pub fn binding_kind(&self, def: DefId) -> Option<DefsKind> {
        self.defs.kind_of(def)
    }

    /// `read_fingerprint`, and whether the answer read state that mono
    /// still writes while it runs (an opaque definer's hidden type, in a
    /// `Sig` or in a set that folds one): such an answer can move between
    /// two turns of materialize (gen_reuse.rs `prejudge`). `Answer` keys
    /// can move too (auto traits of the instances made); the caller keeps
    /// those apart.
    pub(crate) fn read_fingerprint_stable(&self, key: &ReadKey) -> (Read, bool) {
        let before = MONO_READ.replace(false);
        let read = self.read_fingerprint(key);
        let stable = !MONO_READ.replace(before);
        (read, stable)
    }

    /// What one recorded read would answer in this program now, without
    /// recording anything: the node fingerprint and failed flag the query
    /// functions above would store today. The dirty walk compares this
    /// with the stored read (section 8.2 rule 2). `Checked` reads carry a
    /// mono body fingerprint this stage cannot recompute (no mono stage
    /// records them yet), so they report a sentinel that never matches a
    /// stored fingerprint: a body with such a read always rechecks.
    pub fn read_fingerprint(&self, key: &ReadKey) -> Read {
        match key {
            ReadKey::Binding(k) => {
                let res = self.binding_res_at(k);
                Read { fingerprint: binding_fingerprint(self, res), failed: res == BindingRes::Absent }
            }
            ReadKey::MethodSet(k) => {
                let set = self.method_candidates(k.head, k.name, k.form);
                Read { fingerprint: method_set_fingerprint(self, k, &set), failed: set.candidates.is_empty() }
            }
            ReadKey::ImplSet(k) => {
                let set = self.impl_bucket(k.trait_, k.head);
                Read { fingerprint: impl_set_fingerprint(self, k, &set), failed: set.impls.is_empty() }
            }
            ReadKey::Sig(def) => {
                let known = self.local_def(def.hash).filter(|l| self.def_id(*l) == *def).is_some()
                    || self.adt_by_def(*def).is_some()
                    || self.defs.get(*def).is_some();
                Read { fingerprint: sig_fingerprint(self, *def), failed: !known }
            }
            ReadKey::Layout(def) => {
                let known = self.adt_by_def(*def).is_some() || self.defs.get(*def).is_some();
                Read { fingerprint: layout_fingerprint(self, *def), failed: !known }
            }
            ReadKey::DropCk(def) => Read { fingerprint: drop_check_fingerprint(self, *def), failed: self.adt_by_def(*def).is_none() },
            ReadKey::Checked(_) => Read { fingerprint: Fingerprint(u64::MAX), failed: true },
            ReadKey::TraitInScope(module, trait_def) => {
                let ans = self.mod_of_key(*module).is_some_and(|m| self.trait_in_module_answer(m, *trait_def));
                Read { fingerprint: trait_in_scope_fingerprint(ans), failed: !ans }
            }
            ReadKey::StdImport(module, std_mod, name) => {
                let ans = self.mod_of_key(*module).is_some_and(|m| self.std_import_answer(m, *std_mod, *name));
                Read { fingerprint: trait_in_scope_fingerprint(ans), failed: !ans }
            }
            ReadKey::Derives(def) => Read { fingerprint: derives_fingerprint(self, *def), failed: self.adt_by_def(*def).is_none() },
            ReadKey::DeriveBits(def, mask) => {
                Read { fingerprint: derive_bits_fingerprint(self, *def, *mask), failed: self.adt_by_def(*def).is_none() }
            }
            ReadKey::LangImpls(def) => {
                Read { fingerprint: lang_impls_fingerprint(self, *def), failed: self.gx.index.impls_naming(*def).next().is_none() }
            }
            ReadKey::Structure(def) => {
                let known = self.adt_by_def(*def).is_some() || self.defs.get(*def).is_some();
                Read { fingerprint: structure_fingerprint(self, *def), failed: !known }
            }
            ReadKey::AssocVis(def, name) => {
                let entry = self.assoc_vis_entry(*def, *name);
                Read { fingerprint: assoc_vis_fingerprint(self, entry), failed: entry.is_none() }
            }
            ReadKey::Answer(def, kind) => Read { fingerprint: answer_fingerprint(self, *def, *kind), failed: self.adt_by_def(*def).is_none() },
        }
    }

    /// The dirty walk of section 8.3 step 5, one body at a time: how many
    /// of `reads` no longer match this program. Zero means every node the
    /// body read (per-name bindings, method-set probes hit and miss,
    /// failed lookups, signatures) has the same answer as when the body
    /// was checked, so the stored result can be reused if the body itself
    /// is unchanged. The count (not just a bool) feeds the scale gate's
    /// invalidated-query row.
    #[cfg(test)]
    pub fn reads_dirty(&self, reads: &Reads, keys: &ReadKeys) -> usize {
        reads.iter(keys).filter(|(k, stored)| self.read_fingerprint(k) != *stored).count()
    }

    /// `reads_dirty` with a per-program memo of node answers: a walk
    /// over many bodies computes each node's fingerprint once. The
    /// driver's walks use this form; tests use the plain one.
    pub(crate) fn reads_dirty_memo(&self, reads: &Reads, keys: &ReadKeys, memo: &mut FxMap<ReadKey, Read>) -> usize {
        reads.iter(keys).filter(|(k, stored)| *memo.entry(**k).or_insert_with(|| self.read_fingerprint(k)) != *stored).count()
    }
}

/// One request's node answers for one program, by key index of one
/// `ReadKeys` table: the parallel form of `reads_dirty_memo`'s memo, which
/// the driver's walks over many sets share (the dirty walk over the plain
/// bodies, then the generic reuse walk over the instance bodies, which reads
/// ~60% of the same keys). A frozen read finds its answer by index, so a
/// walk hashes no key. The program must not change while one is in use.
#[derive(Default)]
pub(crate) struct KeyAnswers {
    /// The `ReadKeys::id` the answers index.
    table: u64,
    now: Vec<Option<Read>>,
}

impl KeyAnswers {
    /// How many reads of each set no longer match `p` (None: no set), as
    /// `Program::reads_dirty_memo` counts them. The keys the sets read that
    /// have no answer yet get one first, in parallel.
    pub(crate) fn dirty_counts(&mut self, p: &Program, sets: &[Option<&Reads>], keys: &ReadKeys) -> Vec<Option<usize>> {
        use crate::driver::compile::par_map;
        if self.table != keys.id {
            self.table = keys.id;
            self.now.clear();
        }
        self.now.resize(keys.len(), None);
        // The keys still to answer, as one bit set per share of the sets.
        let n = crate::pool::threads().max(1);
        let words = keys.len().div_ceil(64);
        let parts: Vec<&[Option<&Reads>]> = sets.chunks(sets.len().div_ceil(n).max(1)).collect();
        let now = &self.now;
        let marks: Vec<Vec<u64>> = par_map(&parts, |part| {
            let mut m = vec![0u64; words];
            for r in part.iter().flatten() {
                r.check_table(keys);
                for f in r.frozen.iter() {
                    let k = f.key as usize;
                    if now[k].is_none() {
                        m[k / 64] |= 1 << (k % 64);
                    }
                }
            }
            m
        });
        let mut need: Vec<u32> = Vec::new();
        for w in 0..words {
            let mut bits = marks.iter().fold(0u64, |a, m| a | m[w]);
            while bits != 0 {
                need.push((w * 64) as u32 + bits.trailing_zeros());
                bits &= bits - 1;
            }
        }
        let got = par_map(&need, |&k| p.read_fingerprint(&keys.keys[k as usize]));
        for (&k, r) in need.iter().zip(got) {
            self.now[k as usize] = Some(r);
        }
        let now = &self.now;
        par_map(sets, |r| {
            r.map(|r| {
                let frozen = r.frozen.iter().filter(|f| now[f.key as usize] != Some(Read { fingerprint: f.fingerprint, failed: f.failed })).count();
                frozen + r.map.iter().filter(|(k, stored)| p.read_fingerprint(k) != **stored).count()
            })
        })
    }
}

// ---------- The keyed dirty walk (sigedit P3.2) ----------

/// The slots whose stored reads (`Caches::slot_reads`) hold a key that
/// `moves` takes and whose fingerprint differs from `p`'s now, and then, to a
/// fixpoint, the slots with a `Checked(d)` read of a body `d` whose slot is
/// dirty (`def_slot`; the oracle's rule: it checks again). Every other slot's
/// reads are clean, given that no key outside `moves` changed (the caller's
/// proof). Also returns, by slot, whether its reads hold any `Checked` key.
/// The moved keys' fingerprints come from `answers`, the request's node
/// answers for `p`, and the missing ones are computed in parallel and join it
/// (the template and discovery replays read the same map, `GenReuse::memo`).
/// A derive delta knows which keys it can move (`Program::derive_key_moves`),
/// so only those keys' fingerprints are compared. Each set is scanned whole:
/// a frozen set is an array of key indexes, a moved key one bit (a reverse
/// index from keys to readers cost ~250 MB of front image).
pub(crate) fn keyed_dirty_slots(
    p: &Program,
    slot_reads: &[Option<Reads>],
    keys: &ReadKeys,
    quick: &(dyn Fn(&ReadKey) -> Option<bool> + Sync),
    moves: &mut dyn FnMut(&ReadKey) -> bool,
    def_slot: &dyn Fn(DefId) -> Option<usize>,
    answers: &mut FxMap<ReadKey, Read>,
) -> (Vec<bool>, Vec<bool>) {
    use crate::driver::compile::par_map;
    // The keys the sets read: by index (frozen parts), or whole (a part still
    // in its map).
    let mut used = vec![false; keys.len()];
    let mut loose: FxMap<ReadKey, ()> = FxMap::default();
    for r in slot_reads.iter().flatten() {
        r.check_table(keys);
        r.frozen.iter().for_each(|f| used[f.key as usize] = true);
        loose.extend(r.map.keys().map(|k| (*k, ())));
    }
    crate::driver::laps::mark("keyed/used");
    // `quick` answers most keys from tables on all cores; `moves` the rest,
    // one at a time.
    let ids: Vec<u32> = (0..keys.len() as u32).filter(|&i| used[i as usize]).collect();
    let quick_answers: Vec<Vec<Option<bool>>> =
        par_map(&ids.chunks(4096).collect::<Vec<_>>(), |c| c.iter().map(|&i| quick(&keys.keys[i as usize])).collect());
    let mut moved = vec![false; keys.len()];
    for (&i, q) in ids.iter().zip(quick_answers.into_iter().flatten()) {
        moved[i as usize] = q.unwrap_or_else(|| moves(&keys.keys[i as usize]));
    }
    let moved_loose: FxMap<ReadKey, ()> = loose.into_keys().filter(|k| quick(k).unwrap_or_else(|| moves(k))).map(|k| (k, ())).collect();
    crate::driver::laps::mark("keyed/classify");
    let missing: Vec<ReadKey> = ids
        .iter()
        .filter(|&&i| moved[i as usize])
        .map(|&i| keys.keys[i as usize])
        .chain(moved_loose.keys().copied())
        .filter(|k| !answers.contains_key(k))
        .collect();
    let fresh = par_map(&missing, |k| p.read_fingerprint(k));
    answers.extend(missing.into_iter().zip(fresh));
    crate::driver::laps::mark("keyed/fingerprint");
    // Each set compares its moved reads, and lists the bodies its `Checked`
    // reads name, on all cores.
    let checked: Vec<bool> = keys.keys.iter().map(|k| matches!(k, ReadKey::Checked(_))).collect();
    let answers = &*answers;
    let per_slot: Vec<(bool, Vec<DefId>)> = par_map(slot_reads, |r| {
        let Some(r) = r else { return (false, Vec::new()) };
        let changed = |k: &ReadKey, stored: Read| answers.get(k) != Some(&stored);
        let frozen_dirty = r.frozen.iter().any(|f| {
            moved[f.key as usize] && changed(&keys.keys[f.key as usize], Read { fingerprint: f.fingerprint, failed: f.failed })
        });
        let dirty = frozen_dirty || r.map.iter().any(|(k, v)| moved_loose.contains_key(k) && changed(k, *v));
        let mut defs: Vec<DefId> = r
            .frozen
            .iter()
            .filter(|f| checked[f.key as usize])
            .filter_map(|f| match keys.keys[f.key as usize] {
                ReadKey::Checked(d) => Some(d),
                _ => None,
            })
            .collect();
        defs.extend(r.map.keys().filter_map(|k| match k {
            ReadKey::Checked(d) => Some(*d),
            _ => None,
        }));
        (dirty, defs)
    });
    crate::driver::laps::mark("keyed/compare");
    let mut dirty: Vec<bool> = per_slot.iter().map(|(d, _)| *d).collect();
    let has_checked: Vec<bool> = per_slot.iter().map(|(_, defs)| !defs.is_empty()).collect();
    // The readers of each body by its slot, through `Checked` reads; dirt
    // spreads from each dirty slot to its readers.
    let mut readers_of: FxMap<usize, Vec<usize>> = FxMap::default();
    for (s, (_, defs)) in per_slot.iter().enumerate() {
        for &d in defs {
            if let Some(ds) = def_slot(d) {
                readers_of.entry(ds).or_default().push(s);
            }
        }
    }
    let mut work: Vec<usize> = (0..dirty.len()).filter(|&s| dirty[s]).collect();
    while let Some(s) = work.pop() {
        for &r in readers_of.get(&s).into_iter().flatten() {
            if !dirty[r] {
                dirty[r] = true;
                work.push(r);
            }
        }
    }
    crate::driver::laps::mark("keyed/checked");
    (dirty, has_checked)
}

/// What a derive delta can move, per read key (`Program::derive_key_moves`),
/// with its answers per def memoized for one walk.
pub(crate) struct DeriveMoves<'a> {
    reach: &'a crate::check::derive_delta::Reach,
    sig: FxMap<DefId, bool>,
    /// Every key's answer, when asked for many read sets that share keys
    /// (`memoized`; the read index asks each key once).
    keys: Option<FxMap<ReadKey, bool>>,
    /// The names of the fns whose signature moves (`MethodSet` keys key
    /// on the method name).
    names: Option<FxMap<Sym, ()>>,
    /// The Adt defs with a written `Hasher` or `BuildHasher` impl whose
    /// associated type names the reach (`hasher_reaches`), made on use.
    hashers: Option<FxMap<DefId, ()>>,
}

/// A `Sync` view of a `DeriveMoves` whose moved fn names are made: the
/// tables `Program::derive_key_moves_quick` reads.
pub(crate) struct QuickMoves<'a> {
    defs: &'a FxMap<DefId, ()>,
    sig: &'a FxMap<DefId, bool>,
    names: &'a FxMap<Sym, ()>,
}

impl<'a> DeriveMoves<'a> {
    /// The tables of `derive_key_moves_quick` (None before `moved_fn_names`).
    pub(crate) fn quick(&self) -> Option<QuickMoves<'_>> {
        Some(QuickMoves { defs: self.reach.defs(), sig: &self.sig, names: self.names.as_ref()? })
    }

    pub(crate) fn new(reach: &'a crate::check::derive_delta::Reach) -> DeriveMoves<'a> {
        DeriveMoves { reach, sig: FxMap::default(), keys: None, names: None, hashers: None }
    }

    /// As `new`, with every key's answer memoized.
    pub(crate) fn memoized(reach: &'a crate::check::derive_delta::Reach) -> DeriveMoves<'a> {
        DeriveMoves { keys: Some(FxMap::default()), ..DeriveMoves::new(reach) }
    }

    /// The signature answers and moved fn names this walk made
    /// (`moved_fn_names`), for a later walk over the same reach in the
    /// same request (`with_tables`). None before `moved_fn_names`.
    pub(crate) fn tables(&self) -> Option<DeriveTables> {
        Some(DeriveTables { sig: self.sig.clone(), names: self.names.clone()? })
    }

    /// A memoized walk over `reach` that starts from `tables`: the same
    /// answers as a fresh one, with no signature walked twice.
    pub(crate) fn with_tables(reach: &'a crate::check::derive_delta::Reach, tables: DeriveTables) -> DeriveMoves<'a> {
        DeriveMoves { reach, sig: tables.sig, keys: Some(FxMap::default()), names: Some(tables.names), hashers: None }
    }
}

/// `DeriveMoves::tables`: what `moved_fn_names` makes for one reach.
#[derive(Clone, Default)]
pub(crate) struct DeriveTables {
    sig: FxMap<DefId, bool>,
    names: FxMap<Sym, ()>,
}

impl Program {
    /// True when a derive delta over `m.reach` may move the fingerprint of
    /// `key` (sigedit P3.2, the keyed walk). It must hold for every key
    /// whose fingerprint reads a derive list of the reach, directly or
    /// through a deep hash: `Derives` and `Layout` of a reach Adt (a
    /// layout folds the layouts of its field types, and the reach holds
    /// every field user); `Sig` of a reach Adt, of a fn whose signature,
    /// owner, hidden type, or bounds name one, and of a const, static, or
    /// alias whose type names one; `Binding` through the `Sig` it folds;
    /// `MethodSet` for a reach head or a moved method's name; `ImplSet`
    /// for a reach head or a bucket with an impl that names one. `Checked`
    /// and `TraitInScope` read no derive list.
    pub(crate) fn derive_key_moves(&self, m: &mut DeriveMoves, key: &ReadKey) -> bool {
        if let Some(&b) = m.keys.as_ref().and_then(|k| k.get(key)) {
            return b;
        }
        let b = self.derive_key_moves_uncached(m, key);
        if let Some(k) = &mut m.keys {
            k.insert(*key, b);
        }
        b
    }

    /// `derive_key_moves` for each of `keys` (distinct): the tables'
    /// answers (`derive_key_moves_quick`) in parallel, the walk's for the
    /// keys they leave, all into `m`'s memo when it keeps one.
    pub(crate) fn derive_keys_moved(&self, m: &mut DeriveMoves, keys: &[ReadKey]) -> Vec<bool> {
        let quick: Vec<Option<bool>> = match m.quick() {
            Some(q) => crate::driver::compile::par_map(keys, |k| self.derive_key_moves_quick(&q, k)),
            None => vec![None; keys.len()],
        };
        let out: Vec<bool> = keys.iter().zip(quick).map(|(k, q)| q.unwrap_or_else(|| self.derive_key_moves(m, k))).collect();
        if let Some(memo) = &mut m.keys {
            memo.extend(keys.iter().copied().zip(out.iter().copied()));
        }
        out
    }

    /// `derive_key_moves` without the per-key memo.
    fn derive_key_moves_uncached(&self, m: &mut DeriveMoves, key: &ReadKey) -> bool {
        let reach = m.reach;
        match key {
            ReadKey::Derives(d) | ReadKey::DeriveBits(d, _) | ReadKey::Layout(d) | ReadKey::DropCk(d) | ReadKey::Structure(d) | ReadKey::Answer(d, _) => {
                self.adt_by_def(*d).is_none_or(|a| reach.row(self, a.0 as usize)) || self.hasher_reaches(m, *d)
            }
            // Impl shapes fold types shallow: no derive list.
            ReadKey::LangImpls(_) => false,
            ReadKey::Sig(def) => self.sig_moves(m, *def),
            ReadKey::Binding(k) => match self.binding_res_at(k) {
                BindingRes::Def(def) => self.sig_moves(m, def),
                _ => false,
            },
            ReadKey::MethodSet(k) => {
                if let Head::Adt(d) = k.head
                    && self.adt_by_def(d).is_some_and(|a| reach.row(self, a.0 as usize))
                {
                    return true;
                }
                self.moved_fn_names(m);
                m.names.as_ref().is_some_and(|n| n.contains_key(&k.name))
            }
            ReadKey::ImplSet(k) => {
                if let Head::Adt(d) = k.head
                    && self.adt_by_def(d).is_some_and(|a| reach.row(self, a.0 as usize))
                {
                    return true;
                }
                self.impl_bucket(k.trait_, k.head).impls.iter().any(|&d| {
                    self.gx.index.by_def(d).is_none_or(|(_, rec)| reach.record(&self.tys, rec) || rec.items.iter().any(|&it| self.sig_moves(m, it)))
                })
            }
            ReadKey::Checked(_) | ReadKey::TraitInScope(..) | ReadKey::StdImport(..) | ReadKey::AssocVis(..) => false,
        }
    }

    /// The names of the fns whose signature moves (`DeriveMoves::names`),
    /// made once per `m`. The `sig_moves` answers of every fn, Adt, const
    /// and static fill `m` on the way (`derive_key_moves_quick` reads them).
    pub(crate) fn moved_fn_names(&self, m: &mut DeriveMoves) {
        if m.names.is_some() {
            return;
        }
        // Every fn whose def is its own (`sig_moves`'s fn branch), in
        // parallel with a reach copy per chunk; the rest walk below.
        let own: Vec<u32> = (0..self.fns.len() as u32)
            .filter(|&i| {
                let d = self.def_id(LocalDefId(i));
                !m.sig.contains_key(&d) && self.local_def(d.hash) == Some(LocalDefId(i))
            })
            .collect();
        let chunks: Vec<&[u32]> = own.chunks(1024).collect();
        let defs = m.reach.defs();
        let parts = crate::driver::compile::par_map(&chunks, |c| {
            let r = crate::check::derive_delta::Reach::with_defs(defs.clone());
            c.iter().map(|&i| (self.def_id(LocalDefId(i)), self.fn_sig_moves(&r, LocalDefId(i)))).collect::<Vec<_>>()
        });
        m.sig.extend(parts.into_iter().flatten());
        let mut names = FxMap::default();
        for i in 0..self.fns.len() {
            let f = LocalDefId(i as u32);
            if self.sig_moves(m, self.def_id(f)) {
                names.insert(self.fn_info(f).name, ());
            }
        }
        m.names = Some(names);
        for i in 0..self.adts.len() {
            if let Some(d) = self.defs.def_of_adt(AdtId(i as u32)) {
                self.sig_moves(m, d);
            }
        }
        // A const's or static's answer is its type's (`sig_moves`, by index:
        // its lookups scan the def lists). The first index of a def counts.
        let not_fn_or_adt = |d: DefId| self.local_def(d.hash).filter(|l| self.def_id(*l) == d).is_none() && self.adt_by_def(d).is_none();
        let consts: FxMap<DefId, ()> = self.const_defs.iter().map(|&d| (d, ())).collect();
        for (i, &d) in self.const_defs.iter().enumerate() {
            if !m.sig.contains_key(&d) && not_fn_or_adt(d) {
                m.sig.insert(d, m.reach.ty(&self.tys, self.consts[i].ty));
            }
        }
        for (i, &d) in self.static_defs.iter().enumerate() {
            if !m.sig.contains_key(&d) && not_fn_or_adt(d) && !consts.contains_key(&d) {
                m.sig.insert(d, m.reach.ty(&self.tys, self.statics[i].ty));
            }
        }
    }

    /// `derive_key_moves` from tables only, for a parallel walk: None when
    /// the key needs the walk itself (the caller asks `derive_key_moves`).
    /// `m` must hold the moved fn names (`moved_fn_names`).
    pub(crate) fn derive_key_moves_quick(&self, m: &QuickMoves, key: &ReadKey) -> Option<bool> {
        let row = |d: DefId| self.adt_by_def(d).is_some_and(|a| self.derive_def(a).is_some_and(|x| m.defs.contains_key(&x)));
        match key {
            ReadKey::Sig(def) => m.sig.get(def).copied(),
            ReadKey::Binding(k) => match self.binding_res_at(k) {
                BindingRes::Def(def) => m.sig.get(&def).copied(),
                _ => Some(false),
            },
            ReadKey::MethodSet(k) => Some(matches!(k.head, Head::Adt(d) if row(d)) || m.names.contains_key(&k.name)),
            ReadKey::Checked(_) | ReadKey::TraitInScope(..) | ReadKey::StdImport(..) | ReadKey::AssocVis(..) => Some(false),
            // As `sig_moves` answers for an Adt def (no fn has that def).
            ReadKey::Derives(d) | ReadKey::DeriveBits(d, _) | ReadKey::Layout(d) | ReadKey::DropCk(d) | ReadKey::Structure(d) | ReadKey::Answer(d, _) => match self.adt_by_def(*d) {
                None => Some(true),
                Some(_) => m.sig.get(d).copied(),
            },
            ReadKey::ImplSet(_) => None,
            ReadKey::LangImpls(_) => Some(false),
        }
    }

    /// `derive_key_moves` for a `Sig` key (memoized in `m`).
    pub(crate) fn sig_moves(&self, m: &mut DeriveMoves, def: DefId) -> bool {
        if let Some(&b) = m.sig.get(&def) {
            return b;
        }
        let reach = m.reach;
        let tys = &self.tys;
        let b = if let Some(local) = self.local_def(def.hash).filter(|l| self.def_id(*l) == def) {
            self.fn_sig_moves(reach, local)
        } else if let Some(a) = self.adt_by_def(def) {
            reach.row(self, a.0 as usize) || self.hasher_reaches(m, def)
        } else if let Some(i) = self.const_by_def(def) {
            reach.ty(tys, self.consts[i as usize].ty)
        } else if let Some(i) = self.static_by_def(def) {
            reach.ty(tys, self.statics[i as usize].ty)
        } else if let Some(data) = self.defs.get(def) {
            // `sig_fingerprint`: an alias folds its type; any other def
            // only its name.
            match (self.aliases.get(&data.name), self.gx.generic_aliases.get(&data.name)) {
                (Some(&t), _) => reach.ty(tys, t),
                (None, Some(la)) => reach.ty(tys, la.erased),
                (None, None) => false,
            }
        } else {
            false
        };
        m.sig.insert(def, b);
        b
    }

    /// `sig_moves` for the local fn `local` (its def's own fn): its owner,
    /// signature, hidden type, opaque bounds, or predicates name the reach.
    fn fn_sig_moves(&self, reach: &crate::check::derive_delta::Reach, local: LocalDefId) -> bool {
        let tys = &self.tys;
        let def = self.def_id(local);
        let f = self.fn_info(local);
        let od = crate::check::generics::opaque_def(def);
        f.owner.is_some_and(|a| reach.row(self, a.0 as usize))
            || f.params.iter().any(|&t| reach.ty(tys, t))
            || reach.ty(tys, f.ret)
            || self.gx.opaque_hidden.get(&od).is_some_and(|&t| reach.ty(tys, t))
            || self.gx.opaques.get(&od).is_some_and(|o| o.bounds.iter().any(|q| reach.pred(tys, q)))
            || self.gx.fn_templates.get(local.0 as usize).and_then(Option::as_ref).is_some_and(|t| t.generics.predicates.iter().any(|q| reach.pred(tys, q)))
    }

    /// True when Adt `def`'s layout fingerprint folds a written `Hasher`
    /// or `BuildHasher` impl's associated type that names a reach Adt
    /// (`hash_adt_layout`).
    fn hasher_reaches(&self, m: &mut DeriveMoves, def: DefId) -> bool {
        if m.hashers.is_none() {
            let mut heads = FxMap::default();
            for tr in [self.gx.lang.hasher, self.gx.lang.build_hasher] {
                for &id in self.gx.index.impls_of_trait(tr) {
                    let rec = self.gx.index.get(id);
                    if let crate::traits::index::SelfHead::Adt(d) = rec.head
                        && rec.assoc_tys.iter().any(|&(_, t)| m.reach.ty(&self.tys, t))
                    {
                        heads.insert(d, ());
                    }
                }
            }
            m.hashers = Some(heads);
        }
        m.hashers.as_ref().is_some_and(|h| h.contains_key(&def))
    }
}

// ---------- Instance keys and the slot manifest (section 4.2) ----------

/// The discovery key of one monomorphized instance: a fn, method, closure,
/// or static initializer def plus its type and const args. Regions never
/// enter the key. Owned by W-TRAITS-CORE through wave A (the minimal generic
/// pipeline may reshape it); S7 only fixes the type and its hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstanceKey {
    pub def: DefId,
    pub args: ArgsId,
}

impl InstanceKey {
    /// A non-generic def is an instance with empty args (section 4.2).
    pub fn mono(def: DefId) -> InstanceKey {
        InstanceKey { def, args: EMPTY_ARGS }
    }
}

/// The stable hash of an instance key: def disk identity plus arg type and
/// const fingerprints, with lifetime args erased. Slot tables and manifest
/// files key on this, never on session ids inside `InstanceKey`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstanceKeyHash(pub u64);

impl InstanceKeyHash {
    /// The hash of one def in disk form applied to an already-computed args
    /// fingerprint. This is the bridge from today's slot keys, which are
    /// plain disk defs: they are instance keys with the empty-args
    /// fingerprint.
    pub fn of_disk_def(disk: DiskDefId, args_fingerprint: Fingerprint) -> InstanceKeyHash {
        let mut h = FxHasher::default();
        "instance-v1".hash(&mut h);
        disk.krate.0.hash(&mut h);
        disk.hash.0.hash(&mut h);
        args_fingerprint.0.hash(&mut h);
        InstanceKeyHash(h.finish())
    }

    /// The args fingerprint of the empty argument list.
    pub fn empty_args_fingerprint() -> Fingerprint {
        let mut h = FxHasher::default();
        "instance-args-v1".hash(&mut h);
        0u64.hash(&mut h);
        Fingerprint(h.finish())
    }
}

impl<'a> Program {
    /// The instance key of one of today's non-generic functions.
    #[allow(dead_code)] // First caller is mono (wave B); the slot manifest tests use it now.
    pub fn instance_key(&self, f: LocalDefId) -> InstanceKey {
        InstanceKey::mono(self.def_id(f))
    }

    /// The stable hash of an instance key under this program. Lifetime args
    /// are skipped: regions do not affect code (section 4.2).
    #[allow(dead_code)] // See `instance_key`.
    pub fn instance_key_hash(&self, key: &InstanceKey) -> InstanceKeyHash {
        let mut h = FxHasher::default();
        "instance-args-v1".hash(&mut h);
        let args = self.tys.args(key.args);
        let n_value_args = args.iter().filter(|a| !matches!(a, GenericArg::Lifetime(_))).count();
        (n_value_args as u64).hash(&mut h);
        for a in args {
            match a {
                GenericArg::Ty(t) => {
                    0u8.hash(&mut h);
                    hash_ty(&mut h, self, &self.tys, *t);
                }
                GenericArg::Lifetime(_) => {}
                GenericArg::Const(c) => {
                    2u8.hash(&mut h);
                    hash_const(&mut h, &self.tys, *c);
                }
            }
        }
        let args_fp = Fingerprint(h.finish());
        let disk = DiskDefId { krate: StableCrateHash(def_crate_hash(self, key.def)), hash: key.def.hash };
        InstanceKeyHash::of_disk_def(disk, args_fp)
    }
}

/// The final binary's slot manifest: which slot each instance owns in the
/// one `lust_fns` table (sections 1.7 and 4.2). Assignment is append-only
/// per bin session; unreachable instances leave dead slots, which stay in
/// the manifest so no live slot ever moves. The persisted byte form for
/// today's non-generic subset lives in `driver::session`
/// (`encode_slot_manifest`); the general disk form is W-DRIVER's, under the
/// versioned cache file of section 8.4, not frozen here.
#[derive(Clone, Debug, Default)]
pub struct SlotManifest {
    by_key: FxMap<InstanceKeyHash, u32>,
    by_slot: Vec<InstanceKeyHash>,
}

impl SlotManifest {
    /// An empty manifest.
    #[allow(dead_code)] // First production owner is the slot store (W-DRIVER); tests use it now.
    pub fn new() -> SlotManifest {
        SlotManifest::default()
    }

    /// Builds a manifest from today's slot map (plain disk defs, which are
    /// empty-args instance keys). Slots must be dense, as `slot_update`
    /// assigns them; a sparse map is a driver bug, caught in debug builds.
    #[allow(dead_code)] // See `new`.
    pub fn from_disk_slots(slot_of: &FxMap<DiskDefId, u32>) -> SlotManifest {
        let empty = InstanceKeyHash::empty_args_fingerprint();
        let mut entries: Vec<(u32, InstanceKeyHash)> = slot_of.iter().map(|(k, &s)| (s, InstanceKeyHash::of_disk_def(*k, empty))).collect();
        entries.sort_unstable();
        let mut m = SlotManifest::default();
        for (slot, key) in entries {
            debug_assert_eq!(slot as usize, m.by_slot.len(), "slot manifest from a sparse slot map");
            m.by_key.insert(key, slot);
            m.by_slot.push(key);
        }
        m
    }

    /// The slot an instance owns, if it has one.
    #[allow(dead_code)] // See `new`.
    pub fn slot_of(&self, key: InstanceKeyHash) -> Option<u32> {
        self.by_key.get(&key).copied()
    }

    /// The slot an instance owns, assigning the next free slot if it has
    /// none. Append-only: an existing slot never moves.
    #[allow(dead_code)] // See `new`.
    pub fn assign(&mut self, key: InstanceKeyHash) -> u32 {
        match self.by_key.get(&key) {
            Some(&slot) => slot,
            None => {
                let slot = self.by_slot.len() as u32;
                self.by_key.insert(key, slot);
                self.by_slot.push(key);
                slot
            }
        }
    }

    /// Number of slots ever assigned, dead slots included.
    #[allow(dead_code)] // See `new`.
    pub fn len(&self) -> usize {
        self.by_slot.len()
    }

    /// True if no slot was ever assigned.
    #[allow(dead_code)] // See `new`.
    pub fn is_empty(&self) -> bool {
        self.by_slot.is_empty()
    }

    /// The hash of the whole manifest, by slot. Only the table unit (the
    /// unit that emits `lust_fns` itself) keys on this; every other unit
    /// keys on its used-slots hash, so one new slot rebuilds only the
    /// table (section 4.2).
    #[allow(dead_code)] // See `new`.
    pub fn manifest_hash(&self) -> u64 {
        let mut h = FxHasher::default();
        "slot-manifest-v1".hash(&mut h);
        (self.by_slot.len() as u64).hash(&mut h);
        for (slot, key) in self.by_slot.iter().enumerate() {
            (slot as u64, key.0).hash(&mut h);
        }
        h.finish()
    }

    /// The used-slots hash for one unit, given the instance keys its emitted
    /// code references (callees, its own instances, tables and trampolines
    /// it names). None if some key has no slot yet: the unit cannot be
    /// keyed until slot assignment covers it.
    #[allow(dead_code)] // See `new`.
    pub fn used_slots_hash(&self, used: &[InstanceKeyHash]) -> Option<u64> {
        let mut pairs: Vec<(u64, u64)> = Vec::with_capacity(used.len());
        for key in used {
            pairs.push((key.0, self.slot_of(*key)? as u64));
        }
        pairs.sort_unstable();
        pairs.dedup();
        let mut h = FxHasher::default();
        "used-slots-v1".hash(&mut h);
        (pairs.len() as u64).hash(&mut h);
        for pair in pairs {
            pair.hash(&mut h);
        }
        Some(h.finish())
    }

    /// The instance key at one slot, if the slot was ever assigned.
    #[allow(dead_code)] // See `new`.
    pub fn key_at(&self, slot: u32) -> Option<InstanceKeyHash> {
        self.by_slot.get(slot as usize).copied()
    }

    /// Serializes the manifest in slot order (magic, count, then one
    /// 8-byte instance key hash per slot). Dense by construction
    /// (`by_slot`), so slot numbers need no bytes. This is the 8.4 disk
    /// form for generic instances; the disk-def form for today's
    /// non-generic slots lives in `driver::session`. W-DRIVER owns both
    /// forms: change one only by bumping its magic.
    #[allow(dead_code)] // See `new`.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + self.by_slot.len() * 8);
        out.extend_from_slice(SLOT_MANIFEST_INSTANCE_MAGIC);
        out.extend_from_slice(&(self.by_slot.len() as u32).to_le_bytes());
        for k in &self.by_slot {
            out.extend_from_slice(&k.0.to_le_bytes());
        }
        out
    }

    /// Reads bytes written by `encode`. None on any shape error (bad
    /// magic, wrong length, one instance in two slots), so a bad file is
    /// a cache miss, never a wrong slot. A decoded manifest assigns the
    /// same slots in any later discovery order: old keys answer from
    /// `by_key`, new keys append.
    #[allow(dead_code)] // See `new`.
    pub fn decode(b: &[u8]) -> Option<SlotManifest> {
        if b.get(..4)? != SLOT_MANIFEST_INSTANCE_MAGIC {
            return None;
        }
        let n = u32::from_le_bytes(b.get(4..8)?.try_into().ok()?) as usize;
        if b.len() != 8 + n.checked_mul(8)? {
            return None;
        }
        let mut m = SlotManifest::default();
        for i in 0..n {
            let at = 8 + i * 8;
            let key = InstanceKeyHash(u64::from_le_bytes(b[at..at + 8].try_into().ok()?));
            if m.by_key.insert(key, i as u32).is_some() {
                return None;
            }
            m.by_slot.push(key);
        }
        Some(m)
    }
}

/// Magic of the instance-hash slot manifest form. See `SlotManifest::encode`.
#[allow(dead_code)] // See `SlotManifest::new`.
const SLOT_MANIFEST_INSTANCE_MAGIC: &[u8; 4] = b"LSI1";

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{check_fn, collect};
    use crate::def::{CrateIds, DefPathHash, LOCAL_CRATE};
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// A frozen read set answers as before; a record of a key it holds keeps
    /// the first read, a thawed set takes a new key, and another table fails
    /// closed.
    #[test]
    fn a_frozen_read_set_reads_the_same() {
        let a = DefId { krate: LOCAL_CRATE, hash: DefPathHash(1) };
        let mut r = Reads::new();
        r.record(ReadKey::Sig(a), Fingerprint(1), false);
        r.record(ReadKey::Layout(a), Fingerprint(2), true);
        let mut keys = ReadKeys::default();
        let all = |r: &Reads, keys: &ReadKeys| r.iter(keys).map(|(k, v)| (*k, v)).collect::<FxMap<_, _>>();
        let before = all(&r, &keys);
        r.freeze(&mut keys);
        assert!(r.map.is_empty() && r.frozen.len() == 2 && keys.len() == 2);
        assert_eq!(all(&r, &keys), before);
        assert_eq!(r.get(&keys, &ReadKey::Layout(a)), Some(Read { fingerprint: Fingerprint(2), failed: true }));
        // A record into the frozen set (no thaw) keeps the first read of a key.
        r.record(ReadKey::Sig(a), Fingerprint(9), false);
        assert_eq!(r.get(&keys, &ReadKey::Sig(a)).map(|v| v.fingerprint), Some(Fingerprint(1)));
        r.thaw(&keys);
        r.freeze(&mut keys);
        assert_eq!((r.len(), r.get(&keys, &ReadKey::Sig(a)).map(|v| v.fingerprint)), (2, Some(Fingerprint(1))));
        r.thaw(&keys);
        r.record(ReadKey::Checked(a), Fingerprint(3), false);
        assert_eq!(r.len(), 3);
        // Another table's keys are not this set's: a read fails closed.
        r.freeze(&mut keys);
        let other = ReadKeys::default();
        assert!(std::panic::catch_unwind(|| r.get(&other, &ReadKey::Sig(a))).is_err());
    }

    /// Parses and collects one sample file, then runs `run` on the program.
    fn with_program(src: &str, run: impl FnOnce(&Interner, &mut Program)) {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        run(&interner, &mut program);
    }

    const SAMPLE: &str = "\
struct Foo { x: i64 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn helper() -> i64 { 40 }
fn main() {
    let f: Foo = Foo { x: helper() };
    let y = f.get() + 2;
    println!(\"{}\", y);
}
";

    /// A layout fingerprint notes no impl read into the read scope open
    /// while it runs (a body's check): it hashes the type's own written
    /// `Hasher` impl itself. Its scan of every `Hasher` impl once noted a
    /// `LangImpls` read of each, so a body checked with the fingerprint memo
    /// cold read every hasher of the program, and the same body checked
    /// with it warm read none (fx-coldmono, 2026-10-19 10:39).
    #[test]
    fn a_layout_fingerprint_notes_no_impl_read() {
        let src = "\
struct H1(u64);
impl std::hash::Hasher for H1 {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, b: &[u8]) { self.0 += b.len() as u64; }
}
struct H2(u64);
impl std::hash::Hasher for H2 {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, b: &[u8]) { self.0 ^= b.len() as u64; }
}
struct Foo { x: i64 }
fn main() {
    let f = Foo { x: 1 };
    println!(\"{}\", f.x + H1(2).0 as i64 + H2(3).0 as i64);
}
";
        with_program(src, |interner, p| {
            let def = |name: &str| (0..p.adts.len()).find(|&i| interner.get(p.adts[i].name) == name).map(|i| p.def_of_adt(crate::ty::AdtId(i as u32))).unwrap();
            for name in ["Foo", "H1"] {
                let ((), noted) = crate::check::derive_delta::scoped(true, || hash_adt_layout(&mut FxHasher::default(), p, def(name), true, &mut |_, _| {}));
                assert!(noted.is_empty(), "{name}: {noted:?}");
            }
        });
    }

    /// A primitive builtin method's item type (`ty::prim_fn_def`) holds the method name's
    /// symbol as a const. A symbol's number is its place in its interner shard, so two
    /// processes that meet names in another order (a parallel parse) number the same name
    /// apart. The type's fingerprint, and an instance key over it, hash the name's text: the
    /// same item gives the same fingerprint in both.
    #[test]
    fn prim_item_fingerprint_hashes_the_name_not_its_symbol_number() {
        let name = "zq_prim_method";
        // A name in the same shard: met first, it moves `name`'s number.
        let alone = Interner::default().intern(name);
        let other = (0..)
            .map(|i| format!("zq_shift_{i}"))
            .find(|o| {
                let i = Interner::default();
                i.intern(o);
                i.intern(name) != alone
            })
            .unwrap();
        let item = |first: Option<&str>| {
            let mut out = None;
            with_program(SAMPLE, |interner, p| {
                if let Some(o) = first {
                    interner.intern(o);
                }
                let sym = interner.intern(name);
                let (n, code) = (p.tys.intern_const(ConstKind::Int(sym.0 as u128)), p.tys.intern_const(ConstKind::Int(7)));
                let args = p.tys.intern_args(&[GenericArg::Ty(BOOL), GenericArg::Const(n), GenericArg::Const(code)]);
                let t = p.tys.intern(TyKind::FnDef(crate::ty::prim_fn_def(), args));
                out = Some((sym, ty_fingerprint(p, t)));
            });
            out.unwrap()
        };
        let ((a, fa), (b, fb)) = (item(None), item(Some(&other)));
        assert_ne!(a, b, "the two programs number the name apart");
        assert_eq!(fa, fb);
    }

    fn foo_head(p: &Program, interner: &Interner) -> Head {
        let a = p.type_names[&interner.intern("Foo")];
        Head::Adt(p.def_of_adt(a))
    }

    /// The S7 gate: a checked sample body records per-binding and
    /// method-set reads, hit and miss, through the query functions.
    #[test]
    fn sample_body_records_binding_and_method_set_reads() {
        with_program(SAMPLE, |interner, p| {
            let (ck, errs) = check_fn(p, p.main.unwrap());
            assert!(errs.is_empty(), "{errs:?}");
            let reads = &ck.reads;
            let value =
                |name: &str| ReadKey::Binding(BindingKey { module: ModKey::bare(ROOT_MODULE), ns: Namespace::Value, name: interner.intern(name) });
            // The `helper()` call reads one value binding, by that name only.
            let helper = reads.recorded(&value("helper")).expect("helper binding read");
            assert!(!helper.failed);
            // The `let f: Foo` annotation reads one type binding.
            let foo_ty = ReadKey::Binding(BindingKey { module: ModKey::bare(ROOT_MODULE), ns: Namespace::Type, name: interner.intern("Foo") });
            assert_eq!(reads.recorded(&foo_ty).map(|r| r.failed), Some(false));
            // A name the body never mentions has no read: reads are per name,
            // never per scope.
            assert!(reads.recorded(&value("missing")).is_none());
            // `f.get()` probes receiver forms in order: the by-value probe
            // misses and records a failed read, the `&self` probe hits, and
            // probing stops there.
            let head = foo_head(p, interner);
            let probe = |form| ReadKey::MethodSet(MethodSetKey { head, name: interner.intern("get"), form });
            assert_eq!(reads.recorded(&probe(ReceiverForm::Value)).map(|r| r.failed), Some(true), "by-value probe miss is recorded");
            assert_eq!(reads.recorded(&probe(ReceiverForm::Ref)).map(|r| r.failed), Some(false), "shared probe hit is recorded");
            assert!(reads.recorded(&probe(ReceiverForm::RefMut)).is_none(), "probing stops at the hit");
            // The callee signatures the body used are on record too.
            let helper_def = p.def_id(p.fn_names[&interner.intern("helper")]);
            assert!(reads.recorded(&ReadKey::Sig(helper_def)).is_some());
        });
    }

    /// A name that does not resolve is a failed read with the same key as a
    /// hit, so adding the def later rechecks exactly this body (8.2 rule 3).
    #[test]
    fn failed_binding_is_a_failed_read() {
        with_program("fn main() { nosuch(); }\n", |interner, p| {
            let (ck, errs) = check_fn(p, p.main.unwrap());
            assert!(!errs.is_empty(), "the call must also be an error");
            let key = ReadKey::Binding(BindingKey { module: ModKey::bare(ROOT_MODULE), ns: Namespace::Value, name: interner.intern("nosuch") });
            assert_eq!(ck.reads.recorded(&key).map(|r| r.failed), Some(true));
            // The same key in a program that defines the name is a hit with a
            // different fingerprint.
            let mut reads = Reads::new();
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Macro, interner.intern("nosuch")), BindingRes::Absent);
            let macro_key = ReadKey::Binding(BindingKey { module: ModKey::bare(ROOT_MODULE), ns: Namespace::Macro, name: interner.intern("nosuch") });
            assert_eq!(reads.recorded(&macro_key).map(|r| r.failed), Some(true));
            // Different keys, same fingerprint: the fingerprint covers the
            // node's answer ("absent"), not which node was asked.
            assert_eq!(reads.recorded(&macro_key).unwrap().fingerprint, ck.reads.recorded(&key).unwrap().fingerprint);
        });
    }

    /// The frozen binding query answers per namespace behind today's
    /// single-file resolver, and records each key once.
    #[test]
    fn binding_query_answers_per_namespace() {
        with_program(SAMPLE, |interner, p| {
            let mut reads = Reads::new();
            let helper = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("helper"));
            let BindingRes::Def(helper_def) = helper else { panic!("helper must resolve: {helper:?}") };
            assert_eq!(p.binding_kind(helper_def), Some(DefsKind::Fn));
            // A struct answers in both namespaces with the same def.
            let as_ty = p.binding(&mut reads, ROOT_MODULE, Namespace::Type, interner.intern("Foo"));
            let as_val = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("Foo"));
            assert_eq!(as_ty, as_val);
            assert_eq!(
                p.binding_kind(match as_ty {
                    BindingRes::Def(d) => d,
                    _ => unreachable!(),
                }),
                Some(DefsKind::Struct)
            );
            // Builtin types resolve in the type namespace only.
            let b = p.tys.builtins();
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Type, interner.intern("String")), BindingRes::Def(b.string));
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("String")), BindingRes::Absent);
            // One module today: any other module is absent, and a repeated
            // query records nothing new.
            assert_eq!(p.binding(&mut reads, ModuleId(9), Namespace::Value, interner.intern("helper")), BindingRes::Absent);
            let n = reads.len();
            let _ = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("helper"));
            assert_eq!(reads.len(), n, "the same key records once");
        });
    }

    /// Method-set probes split by receiver form, and an associated fn with
    /// no `self` surfaces only in the first probe, marked as no receiver.
    #[test]
    fn method_set_splits_by_receiver_form() {
        let src = "\
struct Foo { x: i64 }
impl Foo {
    fn make() -> Foo { Foo { x: 1 } }
    fn bump(&mut self) { self.x += 1; }
}
fn main() {}
";
        with_program(src, |interner, p| {
            let head = foo_head(p, interner);
            let mut reads = Reads::new();
            let make = p.method_set(&mut reads, head, interner.intern("make"), ReceiverForm::Value);
            assert_eq!(make.first().map(|c| c.receiver), Some(None), "assoc fn has no receiver");
            assert!(p.method_set(&mut reads, head, interner.intern("make"), ReceiverForm::Ref).candidates.is_empty());
            assert!(p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::Value).candidates.is_empty());
            assert!(p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::Ref).candidates.is_empty());
            let bump = p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::RefMut);
            assert_eq!(bump.first().map(|c| (c.receiver, c.trait_)), Some((Some(ReceiverForm::RefMut), None)));
            // A miss on a primitive head still records, as a failed read.
            assert!(p.method_set(&mut reads, Head::Int(IntTy::I64), interner.intern("nope"), ReceiverForm::Value).candidates.is_empty());
            let key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Int(IntTy::I64), name: interner.intern("nope"), form: ReceiverForm::Value });
            assert_eq!(reads.recorded(&key).map(|r| r.failed), Some(true));
        });
    }

    /// A def that is not a user trait reads an empty bucket, recorded as a
    /// failed lookup.
    #[test]
    fn impl_set_records_the_empty_bucket() {
        with_program(SAMPLE, |interner, p| {
            let mut reads = Reads::new();
            let any_trait = p.def_id(p.fn_names[&interner.intern("helper")]);
            let head = foo_head(p, interner);
            assert!(p.impl_set(&mut reads, any_trait, head).impls.is_empty());
            let key = ReadKey::ImplSet(ImplSetKey { trait_: any_trait, head });
            assert_eq!(reads.recorded(&key).map(|r| r.failed), Some(true));
            // The layout query answers for a known Adt and fails the read for
            // a def this crate does not have.
            let Head::Adt(adt) = head else { unreachable!() };
            assert!(p.layout_of(&mut reads, adt).is_some());
            let missing = DefId { krate: p.krate, hash: DefPathHash(0xdead) };
            assert_eq!(p.layout_of(&mut reads, missing), None);
            assert_eq!(reads.recorded(&ReadKey::Layout(missing)).map(|r| r.failed), Some(true));
        });
    }

    /// A user trait's bucket holds the impls for the head (through
    /// references) and the blankets, and its read moves when an impl joins
    /// the bucket or an impl in it changes; an impl for another head does
    /// not move it.
    #[test]
    fn impl_set_buckets_follow_user_trait_impls() {
        let base = "trait Tr { fn go(&self) -> i64; }\nstruct A;\nstruct B;\nimpl Tr for A { fn go(&self) -> i64 { 1 } }\nfn main() {}\n";
        let read = |src: &str| -> (usize, Fingerprint) {
            let mut out = (0, Fingerprint(0));
            with_program(src, |interner, p| {
                let mut reads = Reads::new();
                let tr = p.gx.trait_names[&interner.intern("Tr")];
                let head = Head::Adt(p.def_of_adt(p.type_names[&interner.intern("A")]));
                let n = p.impl_set(&mut reads, tr, head).impls.len();
                out = (n, reads.recorded(&ReadKey::ImplSet(ImplSetKey { trait_: tr, head })).unwrap().fingerprint);
            });
            out
        };
        let (n, fp) = read(base);
        assert_eq!(n, 1);
        let blanket = base.replace("fn main", "impl<T: Copy> Tr for &T { fn go(&self) -> i64 { 3 } }\nfn main");
        assert_eq!(read(&blanket).0, 2, "a blanket impl joins every bucket");
        let other = base.replace("fn main", "impl Tr for B { fn go(&self) -> i64 { 2 } }\nfn main");
        assert_eq!(read(&other), (1, fp), "an impl for another head keeps the read");
        let reff = base.replace("impl Tr for A", "impl Tr for &A");
        assert_ne!(read(&reff).1, fp, "an impl header edit moves the read");
    }

    /// A signature edit that keeps every name (so every DefId is the same)
    /// must still move the `Sig` fingerprint: the fingerprint is over
    /// resolved types, not identity.
    #[test]
    fn sig_fingerprint_tracks_signature_types() {
        let fp_of = |src: &str| -> Fingerprint {
            let mut out = Fingerprint(0);
            with_program(src, |interner, p| {
                let mut reads = Reads::new();
                let def = p.def_id(p.fn_names[&interner.intern("f")]);
                let _ = p.sig_of(&mut reads, def);
                out = reads.recorded(&ReadKey::Sig(def)).unwrap().fingerprint;
            });
            out
        };
        let a = fp_of("fn f(x: i64) -> i64 { x }\nfn main() {}\n");
        let same = fp_of("fn f(x: i64) -> i64 { x + 1 }\nfn main() {}\n");
        let changed = fp_of("fn f(x: bool) -> i64 { 1 }\nfn main() {}\n");
        assert_eq!(a, same, "a body edit does not move the signature fingerprint");
        assert_ne!(a, changed, "a parameter type edit does");
    }

    /// Non-generic instance keys hash exactly like today's disk-def slot
    /// keys, and lifetime args never enter the hash (section 4.2).
    #[test]
    fn instance_key_hash_erases_lifetimes() {
        with_program(SAMPLE, |interner, p| {
            let f = p.fn_names[&interner.intern("helper")];
            let key = p.instance_key(f);
            let hash = p.instance_key_hash(&key);
            assert_eq!(key.args, EMPTY_ARGS);
            assert_eq!(hash, InstanceKeyHash::of_disk_def(p.disk_id(f), InstanceKeyHash::empty_args_fingerprint()));
            let lt_args = p.tys.intern_args(&[GenericArg::Lifetime(Region::Static)]);
            let lt_key = InstanceKey { def: key.def, args: lt_args };
            assert_eq!(p.instance_key_hash(&lt_key), hash, "lifetime args are erased");
            let ty_args = p.tys.intern_args(&[GenericArg::Ty(int(IntTy::I64))]);
            let ty_key = InstanceKey { def: key.def, args: ty_args };
            assert_ne!(p.instance_key_hash(&ty_key), hash, "type args are not");
            // The type fingerprint helper behind these hashes is structural:
            // equal types built twice hash equal, different types do not.
            assert_eq!(ty_fingerprint(p, int(IntTy::I64)), ty_fingerprint(p, int(IntTy::I64)));
            assert_ne!(ty_fingerprint(p, int(IntTy::I64)), ty_fingerprint(p, BOOL));
        });
    }

    /// The section 4.2 slot rule in miniature: one new slot leaves every
    /// unrelated unit's used-slots hash alone and moves only the full
    /// manifest hash (the table unit's key).
    #[test]
    fn used_slots_hash_survives_a_new_slot() {
        let disk = |k: u64, h: u64| DiskDefId { krate: StableCrateHash(k), hash: DefPathHash(h) };
        let key = |k: u64, h: u64| InstanceKeyHash::of_disk_def(disk(k, h), InstanceKeyHash::empty_args_fingerprint());
        let mut slot_of = FxMap::default();
        slot_of.insert(disk(1, 10), 0);
        slot_of.insert(disk(1, 20), 1);
        slot_of.insert(disk(1, 30), 2);
        let mut m = SlotManifest::from_disk_slots(&slot_of);
        assert_eq!(m.len(), 3);
        assert_eq!(m.slot_of(key(1, 20)), Some(1));
        let unit = [key(1, 10), key(1, 30)];
        let before = m.used_slots_hash(&unit).unwrap();
        let table_before = m.manifest_hash();
        // One new reachable instance: append-only, old slots stay put.
        assert_eq!(m.assign(key(1, 99)), 3);
        assert_eq!(m.assign(key(1, 99)), 3, "assign is stable");
        assert_eq!(m.slot_of(key(1, 10)), Some(0));
        assert_eq!(m.used_slots_hash(&unit), Some(before), "unrelated units keep their key");
        assert_ne!(m.manifest_hash(), table_before, "the table unit rebuilds");
        assert_eq!(m.used_slots_hash(&[key(7, 7)]), None, "a key with no slot cannot key a unit");
    }

    /// The lowered sample body carries the read set with it, and every call
    /// in it is a terminator with a cleanup (unwind) successor.
    #[test]
    fn lowered_body_carries_reads_and_call_terminators() {
        use crate::ir::{CallTarget, Terminator};
        with_program(SAMPLE, |interner, p| {
            let main = p.main.unwrap();
            let (ck, errs) = check_fn(p, main);
            assert!(errs.is_empty(), "{errs:?}");
            let body = crate::lower::lower(p, main, ck);
            let key = ReadKey::Binding(BindingKey { module: ModKey::bare(ROOT_MODULE), ns: Namespace::Value, name: interner.intern("helper") });
            assert!(body.reads.recorded(&key).is_some(), "the read set rides with the body result");
            let (mut fn_calls, mut builtin_calls) = (0, 0);
            for b in &body.blocks {
                if let Terminator::Call { target, unwind, .. } = &b.term {
                    assert!(unwind.is_some(), "every call carries a cleanup edge (W-CORELANG)");
                    match target {
                        CallTarget::Fn(_) | CallTarget::Indirect(_) | CallTarget::Dyn(_) => fn_calls += 1,
                        CallTarget::Builtin(_) | CallTarget::Intrinsic(_) => builtin_calls += 1,
                    }
                }
            }
            assert!(fn_calls >= 2, "helper() and f.get() are fn call terminators, got {fn_calls}");
            let _ = builtin_calls;
            assert!(crate::borrowck::borrowck(p, &body).is_empty(), "the sample borrow-checks clean");
        });
    }

    /// Collects `src` under a shared interner (as one session does across
    /// requests) and returns main's recorded reads. The program itself is
    /// dropped; reads hold only stable keys (`Sym` in the shared
    /// interner, path-hash `DefId`s), so they replay against the next
    /// program built on the same interner.
    fn main_reads(interner: &std::sync::Arc<Interner>, known: &std::sync::Arc<Known>, src: &str) -> Reads {
        let lexed = lexer::lex(src, FileId(0), 0, interner).unwrap();
        let ast = parser::parse(&lexed, interner, known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let (ck, _) = check_fn(&program, program.main.unwrap());
        ck.reads
    }

    /// Dirty counts of `reads` replayed against a fresh collect of `src`
    /// on the same interner. See `main_reads`.
    fn dirty_in(interner: &std::sync::Arc<Interner>, known: &std::sync::Arc<Known>, src: &str, reads: &Reads) -> usize {
        let lexed = lexer::lex(src, FileId(0), 0, interner).unwrap();
        let ast = parser::parse(&lexed, interner, known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        program.reads_dirty(reads, &ReadKeys::default())
    }

    /// The dirty walk (8.3 step 5): an unrelated added fn dirties nothing
    /// a body read; a callee signature edit, a moved method candidate,
    /// and a failed lookup that now resolves each dirty the body that
    /// read them (8.2 rule 3).
    #[test]
    fn dirty_walk_replays_reads_against_new_program() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let reads = main_reads(&interner, &known, SAMPLE);
        // Same program: clean by construction.
        assert_eq!(dirty_in(&interner, &known, SAMPLE, &reads), 0, "unchanged program");
        // One new unrelated pub fn: no read of main names it, so the walk
        // reuses main (the scale-gate new-fn scenario in miniature).
        let added = format!("{SAMPLE}fn extra() -> i64 {{ 3 }}\n");
        assert_eq!(dirty_in(&interner, &known, &added, &reads), 0, "unrelated fn added");
        // Callee signature edit (helper returns bool now): the Sig read
        // and the Binding read (sig folded in) both move.
        let sig_edit = SAMPLE.replace("fn helper() -> i64 { 40 }", "fn helper() -> bool { true }");
        assert!(dirty_in(&interner, &known, &sig_edit, &reads) >= 2, "callee sig edit dirties");
        // Method receiver edit (&self -> &mut self): the recorded Ref
        // probe hit becomes a miss, so the method-set read moves.
        let method_edit = SAMPLE.replace("fn get(&self)", "fn get(&mut self)");
        assert!(dirty_in(&interner, &known, &method_edit, &reads) >= 1, "method probe edit dirties");
        // Failed lookup: a body that called a missing fn rechecks once
        // the fn exists, and only because its failed Binding read moved.
        let failing = main_reads(&interner, &known, "fn main() { println!(\"{}\", nosuch()); }\n");
        assert_eq!(dirty_in(&interner, &known, "fn main() { println!(\"{}\", nosuch()); }\n", &failing), 0, "still missing");
        let fixed = "fn nosuch() -> i64 { 1 }\nfn main() { println!(\"{}\", nosuch()); }\n";
        assert!(dirty_in(&interner, &known, fixed, &failing) >= 1, "added def dirties the failed lookup");
    }

    /// `KeyAnswers` (the driver's parallel walks) counts what `reads_dirty`
    /// counts, for frozen sets of one table, also when a second walk takes
    /// the first walk's answers.
    #[test]
    fn key_answers_count_as_the_plain_walk() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let missing = "fn main() { println!(\"{}\", nosuch()); }\n";
        let (plain_a, plain_b) = (main_reads(&interner, &known, SAMPLE), main_reads(&interner, &known, missing));
        let mut keys = ReadKeys::default();
        let (mut a, mut b) = (plain_a.clone(), plain_b.clone());
        a.freeze(&mut keys);
        b.freeze(&mut keys);
        let sig_edit = SAMPLE.replace("fn helper() -> i64 { 40 }", "fn helper() -> bool { true }");
        let fixed = format!("fn nosuch() -> i64 {{ 1 }}\n{SAMPLE}");
        for src in [SAMPLE, &sig_edit, &fixed] {
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let p = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let none = ReadKeys::default();
            let want = vec![Some(p.reads_dirty(&plain_a, &none)), None, Some(p.reads_dirty(&plain_b, &none))];
            let mut answers = KeyAnswers::default();
            assert_eq!(answers.dirty_counts(&p, &[Some(&a), None, Some(&b)], &keys), want, "{src}");
            assert_eq!(answers.dirty_counts(&p, &[Some(&b)], &keys), vec![want[2]], "a second walk, {src}");
        }
    }

    /// Type edits dirty through a body's own reads: a body that only
    /// receives a struct from a callee and reads a nested field rechecks
    /// when the nested type changes (the `Layout` read of the struct it
    /// holds; `make`'s `Sig` folds `Outer` by name only), and stays clean
    /// when an unrelated type changes. This is what lets the dirty walk
    /// run in full mode (type edits), not only on signature text.
    #[test]
    fn dirty_walk_covers_type_edits_through_deep_sigs() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "\
struct Inner { x: i64 }
struct Outer { f: Inner }
struct Unused { n: i64 }
fn make() -> Outer { Outer { f: Inner { x: 1 } } }
fn main() { let v = make(); println!(\"{}\", v.f.x); }
";
        let reads = main_reads(&interner, &known, src);
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let nested = src.replace("struct Inner { x: i64 }", "struct Inner { x: bool }");
        assert!(dirty_in(&interner, &known, &nested, &reads) >= 1, "nested field type edit dirties through Layout(Outer)");
        // Derive lists left the layout (P3.3): a body dirties on a derive
        // edit only through its own Derives / DeriveBits reads.
        let derive = src.replace("struct Inner { x: i64 }", "#[derive(Clone)]\nstruct Inner { x: i64 }");
        assert_eq!(dirty_in(&interner, &known, &derive, &reads), 0, "a derive edit main never asks about stays clean");
        let unrelated = src.replace("struct Unused { n: i64 }", "struct Unused { n: bool }");
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "unrelated type edit stays clean");
    }

    /// A field read through a reference records the struct's `Sig`, with
    /// or without module tables: the body holds no value of the struct,
    /// and the signature that gave it the reference names the struct by
    /// identity only. A field type edit dirties the body.
    #[test]
    fn field_reads_through_references_record_the_struct() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "\
struct Foo { x: i64, y: i64 }
fn get(o: &Foo) -> i64 { o.x }
fn main() {}
";
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let (ck, errs) = check_fn(&program, program.fn_names[&interner.intern("get")]);
        assert!(errs.is_empty(), "{errs:?}");
        let retyped = src.replace("x: i64, y", "x: u8, y");
        assert!(dirty_in(&interner, &known, &retyped, &ck.reads) >= 1, "the read field's type edit dirties the body");
        let other = src.replace("y: i64", "y: u8");
        assert!(dirty_in(&interner, &known, &other, &ck.reads) >= 1, "so does an edit of another field (the field list is one Sig)");
    }

    /// An auto trait question about a type with no generic params reads
    /// the answer (`ReadKey::Answer`), not the type's whole structure: a
    /// field edit inside the type that keeps it `Send` keeps the body that
    /// asks clean; a field that makes it not `Send` dirties the body.
    #[test]
    fn auto_trait_questions_read_the_answer() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "\
struct Inner { x: i64 }
struct Outer { a: Inner }
fn need_send<T: Send>(_: &T) {}
fn ask(o: &Outer) { need_send(o); }
fn main() {}
";
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let (ck, errs) = check_fn(&program, program.fn_names[&interner.intern("ask")]);
        assert!(errs.is_empty(), "{errs:?}");
        let reads = ck.reads;
        assert!(reads.keys(&ReadKeys::default()).any(|k| matches!(k, ReadKey::Answer(_, answer::AUTO))), "the Send question reads Answer(Outer)");
        assert!(!reads.keys(&ReadKeys::default()).any(|k| matches!(k, ReadKey::Structure(_))), "and no Structure");
        let kept = src.replace("struct Inner { x: i64 }", "struct Inner { x: i64, y: u8 }");
        assert_eq!(dirty_in(&interner, &known, &kept, &reads), 0, "a field that keeps Send keeps the body clean");
        let lost = src.replace("struct Inner { x: i64 }", "struct Inner { x: *const i64 }");
        assert!(dirty_in(&interner, &known, &lost, &reads) >= 1, "a raw pointer field makes Outer not Send");
    }

    /// The layout fingerprint is its own node: it moves on field edits,
    /// not on a method or derive edit of the same type, and
    /// `layout_of` records it so the walk replays it.
    /// Deep fingerprints (`adt_deep`) over a type graph with a shared
    /// sub-type and a cycle: the same values with the program memo on or
    /// off, in any order, and for any item order in the source. A
    /// structure edit moves every type that reaches it and no other; a
    /// layout edit only the types that hold it by value (not behind the
    /// `Box`es of the cycle).
    #[test]
    fn deep_fingerprints_are_memo_and_order_free() {
        const SRC: &str = "struct A { b: Box<B>, c: C }\nstruct B { a: Option<Box<A>>, x: u8 }\nstruct C { x: u32 }\n\
                           struct D { a: A, c: C, e: (C, [C; 2]) }\nfn main() {}\n";
        fn fps(src: &str, memo: bool, rev: bool) -> Vec<(Fingerprint, Fingerprint, Fingerprint)> {
            let mut out = Vec::new();
            with_program(src, |interner, p| {
                if memo {
                    p.fp_memo.on(p.adts.len());
                }
                let mut names = ["A", "B", "C", "D"];
                if rev {
                    names.reverse();
                }
                for n in names {
                    let def = p.def_of_adt(p.type_names[&interner.intern(n)]);
                    out.push((layout_fingerprint(p, def), sig_fingerprint(p, def), structure_fingerprint(p, def)));
                }
                if rev {
                    out.reverse();
                }
            });
            out
        }
        let base = fps(SRC, false, false);
        assert_eq!(fps(SRC, true, false), base, "the program memo keeps the values");
        assert_eq!(fps(SRC, true, true), base, "walk order does not matter");
        let moved = SRC.replace("struct C { x: u32 }\n", "").replace("fn main", "struct C { x: u32 }\nfn main");
        assert_eq!(fps(&moved, true, false), base, "item order does not matter");
        let moved = |a: &[(Fingerprint, Fingerprint, Fingerprint)], b: &[(Fingerprint, Fingerprint, Fingerprint)], f: fn(&(Fingerprint, Fingerprint, Fingerprint)) -> Fingerprint| {
            a.iter().zip(b).map(|(x, y)| f(x) != f(y)).collect::<Vec<_>>()
        };
        let c_edit = fps(&SRC.replace("x: u32", "x: u64"), true, false);
        let b_edit = fps(&SRC.replace("x: u8", "x: u16"), true, false);
        assert_eq!(moved(&base, &c_edit, |x| x.2), [true, true, true, true], "C's edit moves the structure of A, B (through A), C, and D");
        assert_eq!(moved(&base, &b_edit, |x| x.2), [true, true, false, true], "B's edit moves the structure of its cycle and D");
        assert_eq!(moved(&base, &c_edit, |x| x.0), [true, false, true, true], "C's edit moves the layout of A, C, and D: B holds A in a Box");
        assert_eq!(moved(&base, &b_edit, |x| x.0), [false, true, false, false], "B's edit moves only B's layout: A holds B in a Box");
    }

    /// The memo that follows mono (`FpMemo::sync`): a table the deep
    /// walk reads grows (a glue method for C), and the next sync drops the
    /// values made before, so A's fingerprint is the fresh one again.
    #[test]
    fn followed_memo_drops_values_when_walk_inputs_grow() {
        const SRC: &str = "struct A { c: C }\nstruct C { x: u32 }\nfn main() {}\n";
        with_program(SRC, |interner, p| {
            let def = p.def_of_adt(p.type_names[&interner.intern("A")]);
            let c = p.type_names[&interner.intern("C")];
            p.fp_memo.follow_begin();
            FpMemo::sync(p);
            let before = layout_fingerprint(p, def);
            p.gx.glue_methods.insert((c, p.gx.lang.clone), LocalDefId(0));
            assert_eq!(layout_fingerprint(p, def), before, "the memo holds the old value until the next sync");
            FpMemo::sync(p);
            let after = layout_fingerprint(p, def);
            p.fp_memo.follow_end();
            assert!(p.fp_memo.layout.is_empty(), "a followed memo is off again after mono");
            assert_ne!(after, before, "C's glue moves A");
            assert_eq!(layout_fingerprint(p, def), after, "the synced value is the fresh walk's");
        });
    }

    #[test]
    fn layout_fingerprint_tracks_layout_not_methods() {
        fn layout_of_src(src: &str) -> Fingerprint {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let a = program.type_names[&interner.intern("Foo")];
            layout_fingerprint(&program, program.def_of_adt(a))
        }
        let base = "struct Foo { x: i64 }\nimpl Foo { fn get(&self) -> i64 { self.x } }\nfn main() {}\n";
        let method_edit = base.replace("fn get(&self) -> i64 { self.x }", "fn get(&self) -> i64 { self.x + 1 }");
        assert_eq!(layout_of_src(base), layout_of_src(&method_edit), "method body edit keeps the layout");
        let field_edit = base.replace("struct Foo { x: i64 }", "struct Foo { x: i64, y: i64 }");
        assert_ne!(layout_of_src(base), layout_of_src(&field_edit), "field edit moves the layout");
        // Derive lists are their own reads (Derives, DeriveBits), not
        // layout content (sigedit P3.3).
        let derive_edit = base.replace("struct Foo", "#[derive(Clone)]\nstruct Foo");
        assert_eq!(layout_of_src(base), layout_of_src(&derive_edit), "a derive edit keeps the layout fingerprint");
        let eq_base = base.replace("struct Foo", "#[derive(PartialEq, Eq, Hash)]\nstruct Foo");
        for (from, to) in [("Eq, Hash", "Hash"), ("Eq, Hash", "Eq")] {
            let edited = eq_base.replace(from, to);
            assert_eq!(layout_of_src(&eq_base), layout_of_src(&edited), "an `Eq` or `Hash` derive edit keeps the layout");
        }
        with_program(base, |interner, p| {
            let a = p.type_names[&interner.intern("Foo")];
            let def = p.def_of_adt(a);
            let mut reads = Reads::new();
            let fp = p.layout_of(&mut reads, def).expect("known adt");
            assert_eq!(reads.recorded(&ReadKey::Layout(def)).map(|r| r.fingerprint), Some(fp));
            assert_eq!(p.read_fingerprint(&ReadKey::Layout(def)).fingerprint, fp, "replay agrees with the recording");
            assert_ne!(fp, sig_fingerprint(p, def), "layout is a separate fingerprint from sig");
        });
    }

    /// Member visibility (ARCH 8.1): the field privacy check records a
    /// `Sig(adt)` read and the method privacy check an `AssocVis` read of
    /// the one method; a visibility-only edit moves that fingerprint (so
    /// the stored read is dirty) while the layout stands, and a method's
    /// edit leaves `Sig(adt)` alone. The tables are built by hand here; the
    /// daemon cases in scripts/fuzz/smoke.py run the same edge end to end.
    #[test]
    fn sig_covers_member_visibility() {
        let src = "struct Foo { x: i64 }\nimpl Foo { fn get(&self) -> i64 { self.x } }\n\
                   fn make() -> Foo { Foo { x: 1 } }\nfn main() { let n = make().x + make().get(); println!(\"{}\", n); }\n";
        with_program(src, |interner, p| {
            let def = p.def_of_adt(p.type_names[&interner.intern("Foo")]);
            let main_reads = |p: &Program| {
                let (ck, errs) = check_fn(p, p.main.unwrap());
                assert!(errs.is_empty(), "{errs:?}");
                ck.reads.clone()
            };
            // No module tables: no privacy check, but the field read still
            // records Sig(Foo) (its type).
            assert!(main_reads(p).recorded(&ReadKey::Sig(def)).is_some(), "a field read records Sig(Foo) without module tables too");
            let mut tables = ResolvedTables::new(interner.intern("test"));
            tables.field_vis.insert(def, (ROOT_MODULE, [(interner.intern("x"), VisKind::Pub)].into_iter().collect()));
            tables.assoc_vis.insert(def, [(interner.intern("get"), (VisKind::Pub, ROOT_MODULE))].into_iter().collect());
            p.resolved = Some(std::sync::Arc::new(tables));
            let stored = main_reads(p);
            let (sig, layout) = (sig_fingerprint(p, def), layout_fingerprint(p, def));
            assert_eq!(stored.recorded(&ReadKey::Sig(def)).map(|r| r.fingerprint), Some(sig), "privacy checks read Sig(Foo)");
            assert_eq!(p.reads_dirty(&stored, &ReadKeys::default()), 0);
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.field_vis.get_mut(&def).unwrap().1.insert(interner.intern("x"), VisKind::Priv);
            assert_ne!(sig_fingerprint(p, def), sig, "a field visibility edit moves Sig");
            assert_eq!(layout_fingerprint(p, def), layout, "and not the layout");
            assert!(p.reads_dirty(&stored, &ReadKeys::default()) > 0, "the field reader is dirty");
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.field_vis.get_mut(&def).unwrap().1.insert(interner.intern("x"), VisKind::Pub);
            assert_eq!(sig_fingerprint(p, def), sig, "the edit back restores Sig");
            let get = ReadKey::AssocVis(def, interner.intern("get"));
            let vis = stored.recorded(&get).map(|r| r.fingerprint);
            assert!(vis.is_some(), "the method privacy check reads AssocVis(Foo::get)");
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.assoc_vis.get_mut(&def).unwrap().insert(interner.intern("get"), (VisKind::Crate, ROOT_MODULE));
            assert_eq!(sig_fingerprint(p, def), sig, "a method visibility edit leaves Sig(Foo)");
            assert_ne!(Some(p.read_fingerprint(&get).fingerprint), vis, "and moves AssocVis(Foo::get)");
            assert!(p.reads_dirty(&stored, &ReadKeys::default()) > 0, "the method caller is dirty");
        });
    }

    /// A body that copies an Adt only inside a tuple and clones it only
    /// inside an Option names no signature that holds it, yet its answer
    /// reads the Adt's derive list: it records a derive read of the trait
    /// it asks, which an edit of that trait dirties and an unrelated
    /// derive edit does not (R12).
    #[test]
    fn derive_answers_record_derives_reads() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "#[derive(Clone, Copy)]\nstruct A { x: u8 }\n#[derive(Clone)]\nstruct U;\n\
                   fn main() { let t = (A { x: 1 }, 2u8); let u = t; let o = Some(A { x: 3 }); let p = o.clone(); \
                   println!(\"{} {} {}\", t.0.x, u.0.x, p.unwrap().x); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys(&ReadKeys::default()).any(|k| matches!(k, ReadKey::Derives(_) | ReadKey::DeriveBits(..))), "a derive read is recorded");
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        // Per trait (DeriveBits): the type check asks A only about Clone
        // (`o.clone()`). The tuple copy is borrowck's question, which the
        // driver's body scope records as its own read.
        let no_copy = src.replacen("#[derive(Clone, Copy)]", "#[derive(Clone)]", 1);
        assert_eq!(dirty_in(&interner, &known, &no_copy, &reads), 0, "-Copy on A: the type check never asked about Copy");
        let neither = src.replacen("#[derive(Clone, Copy)]\nstruct A", "struct A", 1);
        assert!(dirty_in(&interner, &known, &neither, &reads) >= 1, "-Clone on A dirties o.clone()");
        let unrelated = src.replacen("#[derive(Clone)]\nstruct U;", "#[derive(Clone, Copy)]\nstruct U;", 1);
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "+Copy on an Adt main never asks about stays clean");
    }

    /// A const def's `Sig` fingerprint folds its evaluated value: a
    /// value edit moves it, a same-value rephrase does not (ARCH 8.1).
    #[test]
    fn const_sig_fingerprint_tracks_the_value() {
        fn const_fp(src: &str) -> Fingerprint {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let hash = crate::def::item_hash(ids.stable, &[], crate::def::DefKind::Const, "MAX", 0);
            sig_fingerprint(&program, DefId { krate: ids.local, hash })
        }
        let a = const_fp("const MAX: i64 = 3;\nfn main() { println!(\"{}\", MAX); }\n");
        let changed = const_fp("const MAX: i64 = 4;\nfn main() { println!(\"{}\", MAX); }\n");
        assert_ne!(a, changed, "value edit moves the const sig");
        let same = const_fp("const MAX: i64 = 1 + 2;\nfn main() { println!(\"{}\", MAX); }\n");
        assert_eq!(a, same, "same value, same fingerprint");
    }

    /// A const used as a pattern records its `Sig` read: a value edit
    /// dirties the matching body, an unrelated const edit does not.
    /// (Review B2: the pattern path used to read the flat const table
    /// with no recorded read, so a warm daemon kept the old value.)
    #[test]
    fn pattern_const_read_dirties_on_value_edit() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "const K: i64 = 3;\nconst U: i64 = 9;\nfn main() { let x: i64 = 3; println!(\"{}\", match x { K => 1, _ => 0 }); }\n";
        let reads = main_reads(&interner, &known, src);
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let edited = src.replace("const K: i64 = 3;", "const K: i64 = 4;");
        assert!(dirty_in(&interner, &known, &edited, &reads) >= 1, "pattern const value edit dirties");
        let unrelated = src.replace("const U: i64 = 9;", "const U: i64 = 10;");
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "unrelated const edit stays clean");
    }

    /// A const fn body evaluated while checking a body records a
    /// `Checked` read, whose replay never matches: the reader
    /// rechecks whenever it is a walk candidate, even against the
    /// same program. That is the transitive edge from a body to the
    /// const fn bodies it evaluates (review B1, body-local half).
    #[test]
    fn const_block_call_records_checked_read() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "const fn k() -> i64 { 3 }\nfn main() { let x = const { k() }; println!(\"{}\", x); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys(&ReadKeys::default()).any(|k| matches!(k, ReadKey::Checked(_))), "a Checked read is recorded");
        assert!(dirty_in(&interner, &known, src, &reads) >= 1, "Checked reads always dirty (sentinel replay)");
    }

    /// `size_of` over a compound type records a layout read for the
    /// Adt inside it: a field edit dirties the body even though the
    /// written type's outermost path is not the Adt.
    #[test]
    fn size_of_compound_type_records_layout_read() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "struct S { a: u8 }\nfn main() { println!(\"{}\", std::mem::size_of::<[S; 2]>()); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys(&ReadKeys::default()).any(|k| matches!(k, ReadKey::Layout(_))), "a Layout read is recorded");
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let edited = src.replace("struct S { a: u8 }", "struct S { a: u64 }");
        assert!(dirty_in(&interner, &known, &edited, &reads) >= 1, "field edit dirties through the layout read");
    }

    /// A builtin method probe records the probe itself: two different
    /// builtin method names on the same head have different empty-set
    /// fingerprints, so the recorded read names the answer the compat
    /// dispatch gave, not a shared "empty bucket".
    #[test]
    fn builtin_method_probe_records_the_probe() {
        with_program("fn main() { let mut v = Vec::new(); v.push(1); println!(\"{}\", v.len()); }\n", |interner, p| {
            let (ck, _) = check_fn(p, p.main.unwrap());
            let vec_def = p.tys.builtins().vec;
            let push_key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Adt(vec_def), name: interner.intern("push"), form: ReceiverForm::Value });
            let recorded = ck.reads.recorded(&push_key).expect("the push probe is recorded");
            assert!(recorded.failed, "no user candidate: a failed (builtin) probe");
            let pop_key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Adt(vec_def), name: interner.intern("pop"), form: ReceiverForm::Value });
            assert_ne!(
                recorded.fingerprint,
                p.read_fingerprint(&pop_key).fingerprint,
                "different builtin probes have different fingerprints"
            );
            assert_eq!(recorded.fingerprint, p.read_fingerprint(&push_key).fingerprint, "replay agrees");
        });
    }

    /// The instance slot manifest survives a restart in any discovery
    /// order (4.2): decode gives every old instance its old slot, and bad
    /// bytes never decode.
    #[test]
    fn instance_manifest_round_trips() {
        let key = |h: u64| {
            InstanceKeyHash::of_disk_def(
                DiskDefId { krate: StableCrateHash(1), hash: DefPathHash(h) },
                InstanceKeyHash::empty_args_fingerprint(),
            )
        };
        let mut m = SlotManifest::new();
        // Discovery order 30, 10, 20 in the first daemon.
        assert_eq!(m.assign(key(30)), 0);
        assert_eq!(m.assign(key(10)), 1);
        assert_eq!(m.assign(key(20)), 2);
        let mut back = SlotManifest::decode(&m.encode()).unwrap();
        // A restarted daemon discovers in the opposite order.
        assert_eq!(back.assign(key(20)), 2, "old instance keeps its slot");
        assert_eq!(back.assign(key(10)), 1);
        assert_eq!(back.assign(key(30)), 0);
        assert_eq!(back.key_at(2), Some(key(20)));
        // Bad bytes never decode to wrong slots.
        let bytes = m.encode();
        assert_eq!(SlotManifest::decode(&bytes[..bytes.len() - 1]).map(|d| d.len()), None, "truncated");
        let mut dup = bytes.clone();
        dup[16..24].copy_from_slice(&bytes[8..16]);
        assert!(SlotManifest::decode(&dup).is_none(), "one instance in two slots");
    }
}
