// Reads of the flat name maps, and the dynamic read-coverage check.
//
// A body check's stored read set must cover every program answer it used: a
// stored result is reused while its reads hold, so an answer with no read can
// move under an unchanged body (wrong code: rc05-rc10, 4e697b7d1, the std trait
// imports). While one body check runs on this thread (`scoped`), the flat name
// maps (`NameMap`: type names, aliases, traits, generic aliases) log each
// lookup, and the check records a type binding read of each name it looked up
// (`names`, in `check_fn_with`). Fingerprints computed to record a read are not
// lookups of the check (`muted`).
//
// With `LUST_CHECK_READS=1` the resolver's binding, trait-in-scope and std
// import answers log too, and each body check reports every access that no
// read of its stored set covers (`uncovered`; `LUST_READCOVER_LOG` collects
// them, `LUST_READCOVER_BT=1` adds a backtrace each). An uncovered access is a
// missing read (a fix), or one a read covers in a way the rules do not see (a
// rule in `uncovered`, with its reason). scripts/read-cover.sh is the lane.
use crate::check::collect::Program;
use crate::def::DefId;
use crate::driver::graph::{BindingRes, Namespace, ReadKey, ReadKeys, Reads};
use crate::intern::Sym;
use crate::ty::defs::ModuleId;
use std::cell::RefCell;

/// One access a body check made.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Access {
    /// A flat name map lookup of type resolution (`ResolveCx`): a user Adt,
    /// trait, alias or generic alias by its (flattened) name, and whether
    /// the map held it.
    Name(&'static str, Sym, bool),
    /// A resolver binding lookup (`Program::binding_res`).
    Binding(ModuleId, Namespace, Sym),
    /// Whether a user trait is in scope in a module (`trait_in_module_answer`).
    TraitInModule(ModuleId, DefId),
    /// A module's std import (`std_import_answer`); `name` `*` for a glob.
    StdImport(ModuleId, Sym, Sym),
    /// One impl record the impl index handed out (`ImplIndex::get`): the
    /// impl's def and its trait.
    Impl(DefId, DefId),
    /// The impl list of one trait (`impls_of_trait`, a bucket).
    ImplsOf(DefId),
    /// A scan of every impl (`all_impls`).
    AllImpls,
}

/// True when `LUST_CHECK_READS` is set (and not `0`).
pub(crate) fn on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_CHECK_READS").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// True when the check runs with `LUST_READCOVER_BT` set.
fn bt_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| on() && std::env::var_os("LUST_READCOVER_BT").is_some())
}

thread_local! {
    /// This thread's log while a body check runs, and the mute depth.
    static LOG: RefCell<(Option<Vec<Access>>, u32)> = const { RefCell::new((None, 0)) };
    /// Debug (`LUST_READCOVER_BT`): the first backtrace of each access.
    static BT: RefCell<std::collections::HashMap<Access, String>> = RefCell::new(Default::default());
}

/// Logs one access when a scope is open on this thread and not muted.
pub(crate) fn note(a: Access) {
    // Flat name lookups always log: the body check records their reads
    // (`names`). The other accesses log for the check only.
    if !matches!(a, Access::Name(..)) && !on() {
        return;
    }
    LOG.with(|l| {
        let mut l = l.borrow_mut();
        if l.1 == 0
            && let Some(v) = &mut l.0
        {
            v.push(a);
            if bt_on() {
                BT.with(|b| b.borrow_mut().entry(a).or_insert_with(|| std::backtrace::Backtrace::force_capture().to_string()).len());
            }
        }
    });
}

/// Runs `f` with this thread's log muted (a fingerprint a read records).
pub(crate) fn muted<R>(f: impl FnOnce() -> R) -> R {
    LOG.with(|l| l.borrow_mut().1 += 1);
    struct Back;
    impl Drop for Back {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().1 -= 1);
        }
    }
    let _back = Back;
    f()
}

/// Runs one body check `f` with the log open; returns its accesses.
pub(crate) fn scoped<R>(f: impl FnOnce() -> R) -> (R, Vec<Access>) {
    let outer = LOG.with(|l| l.borrow_mut().0.replace(Vec::new()));
    let out = f();
    let log = LOG.with(|l| std::mem::replace(&mut l.borrow_mut().0, outer)).unwrap_or_default();
    (out, log)
}

/// The flat names a body check looked up (`Access::Name`), each once. The
/// check records a type binding read of each: the maps answer by flat name
/// with no read of their own, and the resolver answers a flat name in every
/// module, so that read changes when what the name denotes does.
pub(crate) fn names(log: &[Access]) -> Vec<Sym> {
    let mut seen = crate::intern::FxSet::default();
    log.iter()
        .filter_map(|a| match *a {
            Access::Name(_, s, _) if seen.insert(s) => Some(s),
            _ => None,
        })
        .collect()
}

/// The accesses of one body check that no read of `reads` covers, deduplicated.
/// `reads` is a set still recording (not frozen).
pub(crate) fn uncovered(p: &Program, reads: &Reads, log: &[Access]) -> Vec<Access> {
    let keys = ReadKeys::default();
    let mut out: Vec<Access> = Vec::new();
    let has = |want: &dyn Fn(&ReadKey) -> bool| reads.keys(&keys).any(want);
    for &a in log {
        if out.contains(&a) {
            continue;
        }
        let ok = match a {
            // A primitive name the map does not hold is the primitive: a root
            // item named like one has a `crate$` flat name (a532ab9ba).
            Access::Name(_, s, false) if PRIMITIVES.contains(&p.interner.get(s)) => true,
            // `Self` is a keyword: never a user item's name.
            Access::Name(_, s, false) if s == p.known.self_type => true,
            // A flat name is covered by a type binding read of that name in
            // any module: the resolver answers a flat name in every module
            // (`ResolvedTables::binding` falls back to `flat`), so a change to
            // what the flat name denotes changes that read's answer. It is
            // also covered by any read keyed by the def the name denotes (in
            // this map or another: a miss in the alias map for an enum's
            // name): a def's id is its path's hash, so the name keeps that def
            // while it exists, and the read fails when the def goes away or
            // changes its kind.
            Access::Name(_, s, _) => {
                let def = flat_def(p, s);
                has(&|k| match k {
                    ReadKey::Binding(b) if b.ns == Namespace::Type && b.name == s => true,
                    ReadKey::Binding(b) => def.is_some() && matches!(p.binding_res_at(b), BindingRes::Def(d) if Some(d) == def),
                    k => def.is_some() && key_def(k) == def,
                })
            }
            Access::Binding(m, ns, s) => {
                let mk = p.mod_key(m);
                has(&|k| matches!(k, ReadKey::Binding(b) if b.module == mk && b.ns == ns && b.name == s))
            }
            Access::TraitInModule(m, t) => {
                let mk = p.mod_key(m);
                has(&|k| matches!(k, ReadKey::TraitInScope(km, kt) if *km == mk && *kt == t))
            }
            Access::StdImport(m, sm, n) => {
                let mk = p.mod_key(m);
                has(&|k| matches!(k, ReadKey::StdImport(km, a, b) if *km == mk && *a == sm && *b == n))
            }
            // An impl record is part of the trait-system key, whose change
            // drops every stored result (gen_reuse.rs `trait_key`), except a
            // written impl of a user trait (`impls_read_covered`): its trait's
            // `ImplSet` reads replace the key for it. Synthetic impls (derived:
            // the derive notes; std's builtins) and foreign ones are fixed, and
            // `get` notes the `LangImpls` read of a lang-keyed impl itself.
            Access::Impl(i, t) => !user_impl(p, i, t) || has(&|k| matches!(k, ReadKey::ImplSet(s) if s.trait_ == t)),
            Access::ImplsOf(t) => !p.impls_read_covered(t) || has(&|k| matches!(k, ReadKey::ImplSet(s) if s.trait_ == t)),
            // Every impl: covered while no user trait has a written impl.
            Access::AllImpls => muted(|| p.gx.index.all_impls().all(|(_, r)| !user_impl(p, r.def, r.trait_def))),
        };
        if !ok {
            out.push(a);
        }
    }
    out
}

/// True for a written impl of this crate whose trait's impls stay out of the
/// trait-system key (`Program::impls_read_covered`).
fn user_impl(p: &Program, impl_def: DefId, trait_: DefId) -> bool {
    p.impls_read_covered(trait_)
        && p.gx.index.peek_def(impl_def).is_some_and(|r| r.local && r.synthetic == crate::traits::index::Synthetic::None)
}

/// Primitive type names (a scope layer under every module's items).
const PRIMITIVES: &[&str] =
    &["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "f32", "f64", "bool", "char", "str"];

/// The def a flat type-namespace name denotes now.
fn flat_def(p: &Program, s: Sym) -> Option<DefId> {
    if let Some(t) = &p.resolved {
        return t.flat[crate::resolve::imports::ns_index(Namespace::Type)].get(&s).copied();
    }
    muted(|| p.type_names.get(&s).map(|&a| p.def_of_adt(a)).or_else(|| p.gx.trait_names.get(&s).copied()))
}

/// The def a read is keyed by, for the reads that fail when it goes away.
fn key_def(k: &ReadKey) -> Option<DefId> {
    match *k {
        ReadKey::Sig(d)
        | ReadKey::Layout(d)
        | ReadKey::DropCk(d)
        | ReadKey::Checked(d)
        | ReadKey::Derives(d)
        | ReadKey::DeriveBits(d, _)
        | ReadKey::LangImpls(d)
        | ReadKey::Structure(d)
        | ReadKey::Answer(d, _)
        | ReadKey::AssocVis(d, _)
        | ReadKey::TraitInScope(_, d) => Some(d),
        ReadKey::ImplSet(ref k) => Some(k.trait_),
        _ => None,
    }
}

/// Reports the uncovered accesses of fn `name`'s body check: one line each on
/// stderr and in `LUST_READCOVER_LOG` (appended), `readcover: <fn>: <access>`.
pub(crate) fn report(p: &Program, name: &str, missing: &[Access]) {
    if missing.is_empty() {
        return;
    }
    let mut text = String::new();
    for a in missing {
        let desc = match *a {
            Access::Name(kind, s, hit) => format!("{kind} name {}{}", p.interner.get(s), if hit { " (hit)" } else { "" }),
            Access::Binding(m, ns, s) => format!("binding {ns:?} {} in module {}", p.interner.get(s), m.0),
            Access::TraitInModule(m, t) => format!("trait in scope {:?} in module {}", t, m.0),
            Access::StdImport(m, sm, n) => format!("std import {}::{} in module {}", p.interner.get(sm), p.interner.get(n), m.0),
            Access::Impl(i, t) => format!("impl {i:?} of trait {t:?}"),
            Access::ImplsOf(t) => format!("impls of trait {t:?}"),
            Access::AllImpls => "every impl".to_string(),
        };
        text.push_str(&format!("readcover: {name}: {desc}\n"));
        if let Some(bt) = BT.with(|b| b.borrow().get(a).cloned()) {
            let frames: Vec<&str> = bt.lines().filter(|l| !l.trim_start().starts_with("at ")).take(40).collect();
            text.push_str(&format!("{}\n", frames.join("\n")));
        }
    }
    eprint!("{text}");
    if let Some(path) = std::env::var_os("LUST_READCOVER_LOG") {
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = f.write_all(text.as_bytes());
        }
    }
}

/// A flat name map (`Program::type_names`, `aliases`, `GenTables::trait_names`,
/// `generic_aliases`) whose lookups by name log a `Name` access (`kind` names
/// the map). Whole-map reads (`is_empty`, `values`, `iter`) do not log.
#[derive(Clone, Debug)]
pub struct NameMap<V> {
    map: crate::intern::FxMap<Sym, V>,
    kind: &'static str,
}

impl<V> NameMap<V> {
    pub const fn new(kind: &'static str) -> Self {
        NameMap { map: crate::intern::FxMap::with_hasher(std::hash::BuildHasherDefault::new()), kind }
    }
    pub fn get(&self, name: &Sym) -> Option<&V> {
        let v = self.map.get(name);
        note(Access::Name(self.kind, *name, v.is_some()));
        v
    }
    pub fn get_mut(&mut self, name: &Sym) -> Option<&mut V> {
        self.map.get_mut(name)
    }
    pub fn contains_key(&self, name: &Sym) -> bool {
        let hit = self.map.contains_key(name);
        note(Access::Name(self.kind, *name, hit));
        hit
    }
    pub fn insert(&mut self, name: Sym, v: V) -> Option<V> {
        self.map.insert(name, v)
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.map.values()
    }
    pub fn keys(&self) -> impl Iterator<Item = &Sym> {
        self.map.keys()
    }
    pub fn iter(&self) -> impl Iterator<Item = (&Sym, &V)> {
        self.map.iter()
    }
}

impl<V> std::ops::Index<&Sym> for NameMap<V> {
    type Output = V;
    fn index(&self, name: &Sym) -> &V {
        self.get(name).expect("NameMap: no entry for name")
    }
}
