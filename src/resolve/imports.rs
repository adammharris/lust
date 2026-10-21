// The import worklist, module binding tables, visibility, and path
// resolution (docs/ARCH.md sections 1.3 and 1.5).
//
// State per module: for each namespace, a map `name -> BindState`. A
// binding's source sets priority: local def and explicit import beat glob
// at all times, even when the glob binding arrives first. Two globs that
// bring different defs under one name store `Ambiguous`, which is an
// error only when code uses the name. A re-export binding carries the
// `use` item's own visibility; the target def does not change, and there
// is no alias def. Visibility is checked per path segment against the
// binding found in that module, never as a minimum over the chain.
//
// Determinism: work items process in ModuleId order. The names of one
// glob copy go in any order: each name's copy reads the source's state of
// that name and writes the importer's (only the order of the importer's
// `glob_log`, which is read as a set, shows it). Each binding changes
// state at most twice (absent, glob, explicit), so the fixpoint ends; a round cap of `modules + 2` full
// sweeps guards against bugs (a hit is an internal error today).
use crate::ast;
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::driver::graph::{BindingRes, Namespace};
use crate::intern::{FxMap, Interner, Sym};
use crate::ty::defs::ModuleId;
use std::collections::BTreeMap;

/// `ResolvedTables::glob_src`, keyed by (module, namespace, name): one map
/// per module, so the writes of a glob copy stay in its importer's map. One
/// map for every module held millions of entries on tsgo, and each copy's
/// writes went all over it.
#[derive(Clone, Debug, Default)]
pub struct GlobSrc(Vec<FxMap<(u8, Sym), ModuleId>>);

impl GlobSrc {
    pub fn get(&self, k: &(ModuleId, u8, Sym)) -> Option<&ModuleId> {
        self.0.get(k.0.0 as usize)?.get(&(k.1, k.2))
    }

    pub fn contains_key(&self, k: &(ModuleId, u8, Sym)) -> bool {
        self.get(k).is_some()
    }

    pub fn insert(&mut self, k: (ModuleId, u8, Sym), src: ModuleId) -> Option<ModuleId> {
        let m = k.0.0 as usize;
        if self.0.len() <= m {
            self.0.resize_with(m + 1, FxMap::default);
        }
        self.0[m].insert((k.1, k.2), src)
    }

    pub fn remove(&mut self, k: &(ModuleId, u8, Sym)) -> Option<ModuleId> {
        self.0.get_mut(k.0.0 as usize)?.remove(&(k.1, k.2))
    }

    /// Room for `n` more entries of module `m`.
    pub fn reserve(&mut self, m: ModuleId, n: usize) {
        let m = m.0 as usize;
        if self.0.len() <= m {
            self.0.resize_with(m + 1, FxMap::default);
        }
        self.0[m].reserve(n);
    }

    /// True when module `m` has no entry.
    pub fn none_in(&self, m: ModuleId) -> bool {
        self.0.get(m.0 as usize).is_none_or(FxMap::is_empty)
    }

    /// Every entry, module by module.
    pub fn iter(&self) -> impl Iterator<Item = ((ModuleId, u8, Sym), ModuleId)> + '_ {
        self.0.iter().enumerate().flat_map(|(m, map)| map.iter().map(move |(&(ns, name), &src)| ((ModuleId(m as u32), ns, name), src)))
    }
}

/// The namespace index of a binding table (type, value, macro).
pub fn ns_index(ns: Namespace) -> usize {
    match ns {
        Namespace::Type => 0,
        Namespace::Value => 1,
        Namespace::Macro => 2,
    }
}

/// Visibility in resolver form. `In` holds the written path of a
/// `pub(in ...)` after the `in` keyword as one name, its segments joined by
/// `::` (`in_path` splits it), resolved against module paths by name when
/// checked: one `Sym` keeps a binding (`Bind`) at 40 bytes, where a list of
/// segments made it 56 (the binding maps hold millions).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VisKind {
    Priv,
    Pub,
    Crate,
    Super,
    In(Sym),
}

impl VisKind {
    /// The segments of a `pub(in path)` path (`VisKind::In`).
    pub fn in_path(path: Sym, interner: &Interner) -> Vec<Sym> {
        interner.get(path).split("::").map(|s| interner.intern(s)).collect()
    }
}

/// Converts written AST visibility to resolver form.
pub fn vis_from_ast(v: &ast::Vis, interner: &Interner) -> VisKind {
    match v {
        ast::Vis::Private => VisKind::Priv,
        ast::Vis::Public => VisKind::Pub,
        ast::Vis::Restricted { path, .. } => {
            let names: Vec<&str> = path.iter().map(|s| interner.get(s.name)).collect();
            match names.as_slice() {
                ["crate"] => VisKind::Crate,
                ["super"] => VisKind::Super,
                ["self"] => VisKind::Priv,
                _ => VisKind::In(interner.intern(&names.join("::"))),
            }
        }
    }
}

/// What a binding resolves to. An extern crate root is a target of its
/// own: items behind it belong to another crate's resolver (or to the
/// std compat layer for `std`/`core`/`alloc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Def(DefId),
    Module(ModuleId),
    Extern(u32),
    /// An enum variant (`use a::E::V`, `use a::E::*`): the Adt def plus
    /// the variant name. Variants are not defs of their own here.
    Variant(DefId, Sym),
}

/// One binding: where it points, the visibility it carries (the item's
/// own vis for a local def, the `use` item's vis for an import), its
/// source rank (0 empty, 1 glob, 2 local or explicit), and the module
/// whose scope defines privacy for it.
#[derive(Clone, Debug)]
pub struct Bind {
    pub target: Target,
    pub vis: VisKind,
    pub rank: u8,
    pub def_module: ModuleId,
}

/// What one clashing binding of an ambiguous name brings
/// (`ResolvedTables::ambig_vis`): an item, a std alias path, or the
/// ambiguity of a globbed module. `certain` says that ambiguity reaches
/// the importer whichever glob rustc saw first (`ambiguous_certain`).
#[derive(Clone, Debug, PartialEq)]
pub enum AmbItem {
    Item(Target),
    Std(Vec<Sym>),
    Amb { certain: bool },
}

/// One clashing binding of an ambiguous name: its visibility, the
/// module that defines privacy for it, and what it brings.
pub type AmbEntry = (VisKind, ModuleId, AmbItem);

/// One pending single import (`ResolvedTables::pending_single`).
#[derive(Clone, Debug)]
pub struct PendingSingle {
    pub span: Span,
    pub vis: VisKind,
    pub mod_path: Vec<Sym>,
    pub leading_colon: bool,
    pub last: Sym,
}

/// One name in one namespace of one module.
#[derive(Clone, Debug)]
pub enum BindState {
    One(Bind),
    Ambiguous,
}

/// What kind of local item a def names, for path rewriting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResKind {
    Fn,
    Adt,
    Const,
    Static,
    Alias,
    Macro,
    Trait,
}

/// Facts the rewrite pass needs about one local def, by DefId.
#[derive(Clone, Debug)]
pub struct DefInfo {
    pub kind: ResKind,
    /// The flat name the def carries in the merged AST (the plain name in
    /// the root module, a module-mangled unique name elsewhere).
    pub flat: Sym,
    pub module: ModuleId,
    pub vis: VisKind,
}

/// One module of a crate's module tree. One `ResolvedTables` holds the
/// trees of every crate in the workspace session (ARCH 1.8): each crate
/// is a detached subtree whose root has no parent, and `path` is the
/// name path inside that crate.
#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub parent: Option<ModuleId>,
    /// The module's own name (the crate name for a crate root).
    pub name: Sym,
    /// Names from the crate root to this module (empty for a root).
    pub path: Vec<Sym>,
    pub vis: VisKind,
    pub span: Span,
    /// `#[no_implicit_prelude]` applies (inherited from the parent too).
    pub no_prelude: bool,
    /// The crate root module of the crate this module belongs to.
    pub krate_root: ModuleId,
    /// True when the `mod` declaration carried `#[macro_use]`.
    pub macro_use: bool,
}

/// One extern crate in one crate's extern prelude. The prelude is per
/// crate: two crates in one session can name different dependency
/// crates with the same extern name, so every entry carries its owner.
#[derive(Clone, Debug)]
pub struct ExternInfo {
    /// The name paths use (`std`, `core`, a renamed dependency).
    pub name: String,
    pub def: DefId,
    /// True for `std`, `core`, and `alloc`: paths rooted there keep the
    /// std compat handling in collect and check.
    pub is_std_lib: bool,
    /// The crate root module this entry belongs to (the dependent crate).
    pub owner: ModuleId,
    /// For a dependency lust compiles from source in this session: the
    /// dependency crate's root module in these tables. Paths then walk
    /// its real bindings with normal visibility. None for std libs and
    /// for unsupported dependencies.
    pub root_module: Option<ModuleId>,
    /// For a dependency with no lust source, adapter, or shim crate
    /// yet: the reason (it names the crate), reported as L0508 where
    /// the dependency is used. None when the crate is usable.
    pub unsupported: Option<String>,
}

/// The resolved binding tables of one crate: the swap-in implementation
/// behind the S7 `Binding` query fns (driver/graph.rs). The driver
/// attaches one to `Program` after collect; checkers keep calling the
/// same fns and now get module answers.
pub struct ResolvedTables {
    pub modules: Vec<ModuleInfo>,
    pub maps: Vec<[FxMap<Sym, BindState>; 3]>,
    /// Per module, the names whose bindings, ambiguity lists, std
    /// aliases, glob sources, or pending single imports changed, in
    /// order (`touch`). A glob copy reads and writes one name at a
    /// time, so `run_imports` copies again only the names logged in the
    /// source or the importing module since the glob's last copy. Not
    /// part of any answer.
    pub glob_log: Vec<Vec<Sym>>,
    /// Every key `set_ambiguous` made `Ambiguous`, now or before: a
    /// superset of the `Ambiguous` entries of `maps`, so the order rule
    /// finds them without reading every binding of the session (a
    /// `run_imports` call per crate read all ~2M of them for tsgo). Not
    /// part of any answer.
    pub ambiguous_keys: FxMap<(ModuleId, u8, Sym), ()>,
    pub externs: Vec<ExternInfo>,
    /// Adt def -> associated fn name -> (vis, defining module).
    pub assoc_vis: FxMap<DefId, FxMap<Sym, (VisKind, ModuleId)>>,
    /// Adt def -> (field name -> vis) plus the defining module, for the
    /// field-access visibility check in check.
    pub field_vis: FxMap<DefId, (ModuleId, FxMap<Sym, VisKind>)>,
    /// Tuple-struct def -> per-field vis in declaration order plus the
    /// defining module, for tuple field and constructor checks in check.
    pub tuple_field_vis: FxMap<DefId, (ModuleId, Vec<VisKind>)>,
    /// Adt def -> variant names, for variant imports and `use E::*`.
    pub variants: FxMap<DefId, Vec<Sym>>,
    pub def_info: FxMap<DefId, DefInfo>,
    /// The defining module of each const, static, and associated
    /// const item, keyed by the item's span. The const evaluator in
    /// collect reads it to check field privacy in initializers:
    /// a span survives flattening and Ast concatenation, and items
    /// with no def of their own (anonymous consts, associated
    /// consts) still have one. Filled in `register_items`.
    pub const_init_module: FxMap<Span, ModuleId>,
    /// Flat name -> the source path text for diagnostics (`m0::Stats`,
    /// or `base::inner::Deep` for a source dependency, whose flat name
    /// carries only a hash of the crate). Filled where defs are renamed
    /// to flat names in the worklist. Display only; never a lookup key.
    pub display_names: FxMap<Sym, Sym>,
    /// Each module's own def (index by ModuleId), filled at registration.
    pub module_defs: Vec<DefId>,
    /// Flat name -> def, per namespace, for the merged AST's names. The
    /// checker resolves the rewritten flat names in the root module, so a
    /// root query for a flat name answers here.
    pub flat: [FxMap<Sym, DefId>; 3],
    /// The defining module of each flattened fn, in LocalDefId order.
    pub fn_module: Vec<ModuleId>,
    /// Crate roots by their `$crate` magic segment name. A macro defined
    /// in one crate and expanded in another has its `$crate` rewritten
    /// to a magic first segment (`$lust$crate$<hex>`, not a legal Rust
    /// identifier, so source text can never write it) that resolves to
    /// the defining crate's root even when it is not a direct dependency
    /// of the expanding crate.
    pub crate_magic: FxMap<Sym, ModuleId>,
    /// `use std::... [as Name]` bindings: (module, namespace index,
    /// bound name) -> the import's visibility and the canonical
    /// std path the name stands for. Std items have no local def
    /// to bind, so the rewrite pass expands the name back to the
    /// written path check reads. Ordered by module, so a glob import
    /// reads the aliases of its source module as one range.
    pub std_aliases: BTreeMap<(ModuleId, u8, Sym), (VisKind, Vec<Sym>)>,
    /// The `std_aliases` keys a glob import brought (rank 1), with the
    /// module whose scope defines privacy for each (`Bind::def_module`;
    /// an explicit alias uses its own module). A local item or explicit
    /// import of the name replaces one; a glob binding of another item
    /// makes the name ambiguous (`insert_glob_std_alias`).
    pub std_glob_aliases: FxMap<(ModuleId, u8, Sym), ModuleId>,
    /// Globs of a std crate root (`pub use std::*;`): the importing
    /// module, the glob's visibility, and the root (`std`, `core`,
    /// `alloc`), for the primitive-named modules such a glob binds no
    /// alias for (`primitive_module_under_std_glob`).
    pub std_root_globs: Vec<(ModuleId, VisKind, Sym)>,
    /// The source module a glob-bound name was copied from, keyed like
    /// `std_glob_aliases`. A glob copies the source module's current
    /// binding, and that binding can still upgrade (a glob binding in
    /// the source is replaced by its explicit import, which may name
    /// a different item): a later copy from the same source then
    /// replaces this binding instead of making the name ambiguous, as
    /// rustc resolves the name through the source's final binding.
    /// Fixpoint state only; the final answer stays in `maps`.
    pub glob_src: GlobSrc,
    /// The single imports (`use a::b::n;`) each module still waits on,
    /// by bound name, with each import's span, visibility, module path,
    /// leading `::`, and the name it reads. rustc
    /// hides a module's glob binding of a name while a single import of
    /// that name there is pending (`NameResolution::binding`): a glob of
    /// that module does not copy it yet, and a single import elsewhere
    /// that can see the pending one waits, so no importer reads a
    /// binding the single import later replaces. Fixpoint state of
    /// `run_imports` only.
    pub pending_single: FxMap<(ModuleId, Sym), Vec<PendingSingle>>,
    /// True once the fixpoint stalls: no sweep changes anything. Until
    /// then a single import that reads an ambiguous glob name waits,
    /// since the source's own explicit import may still settle it; after
    /// the stall it binds what is there (an L0507 at the end if it stays
    /// ambiguous). Fixpoint state of `run_imports` only.
    pub import_stall: bool,
    /// The bindings single imports made: (import span, importing
    /// module, source module, name read, namespace, target). rustc
    /// checks each import again against the final tables
    /// (`finalize_import`); `finalize_singles` does the same.
    pub single_binds: Vec<(Span, ModuleId, ModuleId, Sym, Namespace, Target)>,
    /// The visibilities (with defining module) of the glob bindings
    /// that made a name `Ambiguous`, keyed like `glob_src`. A glob
    /// copies an ambiguous name only to an importer that can see one
    /// of them, as rustc imports only accessible bindings: two private
    /// globs that clash stay inside their module. Fixpoint state only.
    pub ambig_vis: FxMap<(ModuleId, u8, Sym), Vec<AmbEntry>>,
    /// Single imports that read an ambiguous name, with the namespace,
    /// source module, and name read. rustc rejects such an import even
    /// when nothing uses it (E0659); `run_imports` reports the ones
    /// whose source is still ambiguous when the fixpoint ends.
    pub ambig_single: Vec<(Import, Namespace, ModuleId, Sym)>,
    /// The glob-bound names whose binding depends on rustc's glob event
    /// order, with every binding rustc may end with (`resolve::order`).
    /// Filled after the fixpoint; a read with an order-dependent answer
    /// is `PathRes::OrderDep` (L0509, a lust subset rule).
    pub order_dep: FxMap<(ModuleId, u8, Sym), crate::resolve::order::OrderSet>,
    /// The binding each `macro_rules!` definition leaves in its own
    /// module's macro namespace (`bind_outline_macros`). rustc has no
    /// such binding: no path import may read it, and a one-segment
    /// `use` reads textual scope instead (`macro_scopes`). A `use` that
    /// binds the macro name in that module replaces it with a real
    /// binding and removes the entry.
    pub macro_textual_binds: FxMap<(ModuleId, Sym), DefId>,
    /// The textual macro scope of each file, with the file's module
    /// (`macro_scope`), for `use name;` in the macro namespace. A macro
    /// with no local definition (a dependency's) is None. Set by the
    /// worklist before the import fixpoint.
    pub macro_scopes: FxMap<crate::diag::FileId, (ModuleId, crate::resolve::macro_scope::FileMacroScope<Option<DefId>>)>,
    /// Each source crate's cfg env and crate name, by its root module (the
    /// selected crate at the root, its source dependencies). The body patch
    /// expands a dependency's fn body alone with its own crate's
    /// (driver/patch.rs `expand_pure`).
    pub crate_cfgs: FxMap<ModuleId, (crate::resolve::cfg::CfgEnv, String)>,
    /// The adapter crates of the session (ARCH 3.6) and the files each
    /// one read. Check reads it for intrinsic privilege and to keep
    /// layout queries off adapter types whose layout is not exact.
    pub adapters: Vec<AdapterCrate>,
    /// Glob `use`s of std modules (`use std::cell::*;`), which bind
    /// nothing in `maps`: (module, path). They answer whether a
    /// non-prelude std type lust knows by name
    /// (`ty::lang::STD_IMPORTED_TYPES`) is in scope by glob; an
    /// explicit import of one is a `std_aliases` entry instead.
    pub std_globs: Vec<(ModuleId, Vec<Sym>)>,
    /// The shipped std platform crate of the session (W-SHIM; see
    /// `std_platform_path`): its root module and its `$crate` magic
    /// name. None when no file of the session mentions a platform
    /// module, so the crate was not loaded.
    pub std_platform: Option<(ModuleId, Sym)>,
    /// The hidden std source modules the std splice defined in the
    /// selected crate's root (src/stdmods.rs, W-STD-C): their names and
    /// module ids. They are bound nowhere; `std_module_at` walks the
    /// std paths of their rows into them.
    pub std_modules: Vec<(Sym, ModuleId)>,
    /// Where the std splice starts in the selected crate's root file
    /// (`CrateInput::std_splice_lo`): every byte from here on in file 0
    /// is shipped std source.
    pub std_splice_lo: Option<u32>,
    /// The driver's std splice ranges with their shipped crates, set
    /// before collect (`Program::shipped_crate_at` reads them while
    /// `Program::shipped_ranges` is still empty).
    pub std_ranges: Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
    /// The crate roots with an `extern crate alloc;` item at the root:
    /// only there (and in shipped std source) does `alloc` name the
    /// alloc crate, as in rustc edition 2024 (`extern_in_scope`).
    pub alloc_roots: Vec<ModuleId>,
    /// The file each `mod name;` without `#[path]` did not take:
    /// `name/mod.rs` beside the `name.rs` it loaded, or the reverse. Once
    /// one appears a cold resolve rejects that module (L0502); the body
    /// patch checks them (driver/patch.rs `find_edits`).
    pub module_alts: Vec<std::path::PathBuf>,
    /// Each module's key (`module_key`) and the module of each key, made on
    /// first use; `add_module` and `add_crate_root` drop it.
    module_index: std::sync::OnceLock<ModuleIndex>,
}

/// `ResolvedTables::module_index`: keys by module id, and ids by key (a key
/// two modules share answers no module).
#[derive(Default)]
struct ModuleIndex {
    keys: Vec<u64>,
    ids: FxMap<u64, ModuleId>,
}

/// The std modules whose items can come from the shipped platform
/// crate (`library/std/src/platform.rs`, W-SHIM): a written
/// `std::<module>::<item>` path resolves into that crate when the
/// crate defines the item. Other std paths keep the std compat
/// handling of collect and check.
pub const STD_PLATFORM_MODULES: &[&str] = &["io", "fs", "env", "path", "process", "ffi", "os"];

/// The platform modules the compiler has no std handling for at all:
/// every `std::<module>::<name>` path resolves in the platform crate,
/// so a name it lacks is an unresolved path, as in rustc, instead of
/// an unchecked std alias.
const STD_PLATFORM_FULL: &[&str] = &["io", "fs", "path", "ffi"];

/// One adapter crate in a session (see `resolve::adapters`).
#[derive(Clone, Debug)]
pub struct AdapterCrate {
    /// The crate name as paths write it (`rustc_hash`).
    pub name: String,
    pub files: Vec<crate::diag::FileId>,
    /// Source paths of the types whose layout equals upstream's.
    pub exact_layout: Vec<String>,
}

impl ResolvedTables {
    /// True when a glob of its std module imports the std type `name`
    /// into `module` (W-STD-A).
    pub fn std_glob_imports(&self, module: ModuleId, name: &str, interner: &Interner) -> bool {
        self.std_globs.iter().any(|(m, path)| {
            *m == module && {
                let p: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                crate::ty::lang::std_glob_imports(&p, name)
            }
        })
    }

    /// The std module path of a module-level glob in `module` that
    /// imports `name` from a sync or thread module (W-THREADS): a type
    /// (`AtomicUsize`, `atomic::Ordering`) or a free fn (`fence`). The
    /// resolver rewrites the bare name to that full std path, as it does
    /// for a fn-body glob, so check never reads it by its bare name.
    pub fn std_sync_glob_path(&self, module: ModuleId, name: &str, interner: &Interner) -> Option<Vec<Sym>> {
        self.std_globs.iter().find_map(|(m, path)| {
            let p: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
            (*m == module && crate::ty::lang::std_sync_glob_imports(&p, name)).then(|| path.clone())
        })
    }

    /// An empty table set with only the first crate's root module (id
    /// 0, the selected crate; dependency crates join with
    /// `add_crate_root`).
    pub fn new(crate_name: Sym) -> ResolvedTables {
        ResolvedTables {
            modules: vec![ModuleInfo {
                parent: None,
                name: crate_name,
                path: Vec::new(),
                vis: VisKind::Pub,
                span: Span::default(),
                no_prelude: false,
                krate_root: ModuleId(0),
                macro_use: false,
            }],
            maps: vec![Default::default()],
            glob_log: Vec::new(),
            ambiguous_keys: FxMap::default(),
            externs: Vec::new(),
            assoc_vis: FxMap::default(),
            field_vis: FxMap::default(),
            tuple_field_vis: FxMap::default(),
            variants: FxMap::default(),
            def_info: FxMap::default(),
            const_init_module: FxMap::default(),
            display_names: FxMap::default(),
            module_defs: vec![DefId::PLACEHOLDER],
            flat: Default::default(),
            fn_module: Vec::new(),
            crate_magic: FxMap::default(),
            std_aliases: BTreeMap::new(),
            std_glob_aliases: FxMap::default(),
            std_root_globs: Vec::new(),
            glob_src: GlobSrc::default(),
            pending_single: FxMap::default(),
            import_stall: false,
            single_binds: Vec::new(),
            ambig_vis: FxMap::default(),
            ambig_single: Vec::new(),
            order_dep: FxMap::default(),
            macro_textual_binds: FxMap::default(),
            macro_scopes: FxMap::default(),
            crate_cfgs: FxMap::default(),
            adapters: Vec::new(),
            std_globs: Vec::new(),
            std_platform: None,
            std_modules: Vec::new(),
            std_splice_lo: None,
            std_ranges: Vec::new(),
            alloc_roots: Vec::new(),
            module_alts: Vec::new(),
            module_index: std::sync::OnceLock::new(),
        }
    }

    /// Adds a detached crate root module for one more crate in the
    /// workspace session and returns its id.
    pub fn add_crate_root(&mut self, name: Sym) -> ModuleId {
        self.module_index = std::sync::OnceLock::new();
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleInfo {
            parent: None,
            name,
            path: Vec::new(),
            vis: VisKind::Pub,
            span: Span::default(),
            no_prelude: false,
            krate_root: id,
            macro_use: false,
        });
        self.maps.push(Default::default());
        self.module_defs.push(DefId::PLACEHOLDER);
        id
    }

    /// The crate root module of the crate `m` belongs to.
    pub fn root_of(&self, m: ModuleId) -> ModuleId {
        self.modules[m.0 as usize].krate_root
    }

    /// True when `rest` (the segments after `std`) resolves in the
    /// shipped std platform crate: a platform module
    /// (`STD_PLATFORM_MODULES`) and at least one more segment. In a
    /// `STD_PLATFORM_FULL` module every such path does; in the others
    /// only an item the crate defines and `from` can see (modules, then
    /// a last item in any namespace), so items the platform crate lacks
    /// keep the std compat handling. A path that ends at the module
    /// (`std::env`) never redirects: module imports keep their std alias.
    pub fn std_platform_has(&self, rest: &[Sym], from: ModuleId, interner: &Interner) -> bool {
        let Some((root, _)) = self.std_platform else { return false };
        if rest.len() < 2 || !STD_PLATFORM_MODULES.contains(&interner.get(rest[0])) {
            return false;
        }
        if STD_PLATFORM_FULL.contains(&interner.get(rest[0])) {
            return true;
        }
        let mut m = root;
        for (k, &seg) in rest.iter().enumerate() {
            if k + 1 == rest.len() {
                return [Namespace::Type, Namespace::Value, Namespace::Macro]
                    .into_iter()
                    .any(|ns| matches!(self.segment_in(m, seg, ns, from, interner), PathRes::Done(_)));
            }
            match self.segment_in(m, seg, Namespace::Type, from, interner) {
                PathRes::Done(Target::Module(next)) => m = next,
                // An Adt with an associated item after it (`std::io::Error::other`).
                PathRes::Done(Target::Def(_)) => return k > 0,
                _ => return false,
            }
        }
        false
    }

    /// The written path of a `std::<platform module>::...` import or
    /// path with `std` replaced by the platform crate's magic root
    /// segment, when `std_platform_has` holds for it. `path[0]` must
    /// already be known to name the std extern.
    pub fn std_platform_path(&self, path: &[Sym], from: ModuleId, interner: &Interner) -> Option<Vec<Sym>> {
        let (_, magic) = self.std_platform?;
        if path.first().is_none_or(|s| interner.get(*s) != "std") || !self.std_platform_has(&path[1..], from, interner) {
            return None;
        }
        let mut out = path.to_vec();
        out[0] = magic;
        Some(out)
    }

    /// True when an import of the written std `path` fell into the
    /// shipped platform module `src` but names an item that module
    /// does not define and the std compat handling serves
    /// (`std_platform_compat_path`, fx-stdos): the import then
    /// takes the std alias handling of the extern branch, as it
    /// did before the platform module existed, instead of an
    /// unresolved import. Only a written `std::...` path whose
    /// first segment names the std extern qualifies.
    pub fn std_platform_compat_fallback(&self, path: &[Sym], src: ModuleId, from: ModuleId, leading_colon: bool, interner: &Interner) -> bool {
        let Some((root, _)) = self.std_platform else { return false };
        if self.root_of(src) != root || path.first().is_none_or(|s| interner.get(*s) != "std") {
            return false;
        }
        if !leading_colon && !self.std_is_extern(from, interner) {
            return false;
        }
        let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        crate::ty::lang::std_platform_compat_path(&strs)
    }

    /// True when the first segment `std` of a path written in `from`
    /// names the std extern (no local item or import shadows it).
    fn std_is_extern(&self, from: ModuleId, interner: &Interner) -> bool {
        let std_sym = interner.intern("std");
        let i = match self.first_segment(from, std_sym, Namespace::Type, PathMode::Use, interner) {
            PathRes::Done(Target::Extern(i)) => i,
            _ => return false,
        };
        let e = &self.externs[i as usize];
        e.is_std_lib && e.name == "std"
    }

    /// True when the first segment `root` (`std`, `core`, `alloc`) of a
    /// path written in `from` names a std extern (nothing shadows it).
    fn std_root_is_extern(&self, from: ModuleId, root: Sym, interner: &Interner) -> bool {
        match self.first_segment(from, root, Namespace::Type, PathMode::Use, interner) {
            PathRes::Done(Target::Extern(i)) => self.externs[i as usize].is_std_lib,
            _ => false,
        }
    }

    /// Adds a module under a parent and returns its id.
    pub fn add_module(&mut self, parent: ModuleId, name: Sym, vis: VisKind, span: Span) -> ModuleId {
        self.module_index = std::sync::OnceLock::new();
        let mut path = self.modules[parent.0 as usize].path.clone();
        path.push(name);
        let no_prelude = self.modules[parent.0 as usize].no_prelude;
        let krate_root = self.modules[parent.0 as usize].krate_root;
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleInfo { parent: Some(parent), name, path, vis, span, no_prelude, krate_root, macro_use: false });
        self.maps.push(Default::default());
        self.module_defs.push(DefId::PLACEHOLDER);
        id
    }

    /// A module's identity across the resolves of one session: its crate
    /// root (the local root, a dependency by its stable crate hash through
    /// `crate_magic`, std by name) and its name path. Module ids follow
    /// insertion order, so a module inserted before another takes the
    /// other's old id; read keys name modules by this instead
    /// (driver/graph.rs `ModKey`). Never has the top bit set.
    pub fn module_key(&self, m: ModuleId) -> u64 {
        self.module_index().keys.get(m.0 as usize).copied().unwrap_or(u64::MAX >> 1)
    }

    /// The module with key `key` (`module_key`) in these tables.
    pub fn module_by_key(&self, key: u64) -> Option<ModuleId> {
        self.module_index().ids.get(&key).copied().filter(|m| m.0 != u32::MAX)
    }

    fn module_index(&self) -> &ModuleIndex {
        use std::hash::{Hash, Hasher};
        self.module_index.get_or_init(|| {
            let magic: FxMap<ModuleId, Sym> = self.crate_magic.iter().map(|(&s, &m)| (m, s)).collect();
            let mut index = ModuleIndex::default();
            for (i, info) in self.modules.iter().enumerate() {
                let mut h = crate::intern::FxHasher::default();
                "module-key-v1".hash(&mut h);
                match (info.krate_root, magic.get(&info.krate_root)) {
                    (ModuleId(0), _) => 0u8.hash(&mut h),
                    (_, Some(s)) => (1u8, s.0).hash(&mut h),
                    (root, None) => (2u8, self.modules[root.0 as usize].name.0).hash(&mut h),
                }
                info.path.iter().for_each(|s| s.0.hash(&mut h));
                let key = h.finish() >> 1;
                index.keys.push(key);
                index.ids.entry(key).and_modify(|m| *m = ModuleId(u32::MAX)).or_insert(ModuleId(i as u32));
            }
            index
        })
    }

    /// The module at a name path from a crate root, if it exists.
    pub fn module_by_path_in(&self, root: ModuleId, path: &[Sym]) -> Option<ModuleId> {
        self.modules.iter().position(|m| m.krate_root == root && m.path == path).map(|i| ModuleId(i as u32))
    }

    /// The module at a name path from the first crate's root, if it
    /// exists. Kept for single-crate callers.
    pub fn module_by_path(&self, path: &[Sym]) -> Option<ModuleId> {
        self.module_by_path_in(ModuleId(0), path)
    }

    /// True when `m` is `anc` or a descendant of it.
    pub fn is_within(&self, m: ModuleId, anc: ModuleId) -> bool {
        let mut cur = Some(m);
        while let Some(c) = cur {
            if c == anc {
                return true;
            }
            cur = self.modules[c.0 as usize].parent;
        }
        false
    }

    /// The visibility rule of section 1.5: can code in module `from` use
    /// a binding with visibility `vis` defined in `def_module`? Spliced
    /// std source (`STD_MODULE`, no module of these tables) sees all: it
    /// reaches a user item only through generics, as `Option::map(Self)`
    /// calls a user tuple struct constructor, and privacy was checked
    /// where user code named the item.
    pub fn visible(&self, vis: &VisKind, def_module: ModuleId, from: ModuleId, interner: &Interner) -> bool {
        if from == crate::ty::defs::STD_MODULE {
            return true;
        }
        match vis {
            VisKind::Pub => true,
            VisKind::Crate => self.root_of(from) == self.root_of(def_module),
            VisKind::Priv => self.is_within(from, def_module),
            VisKind::Super => match self.modules[def_module.0 as usize].parent {
                Some(p) => self.is_within(from, p),
                None => true, // pub(super) at the root behaves as pub(crate)-ish in rustc (it warns); the root has no parent.
            },
            VisKind::In(path) => match self.resolve_in_path(&VisKind::in_path(*path, interner), def_module, interner) {
                Some(m) => self.is_within(from, m),
                None => false,
            },
        }
    }

    /// True when a written restricted visibility at `module` is one rustc
    /// accepts: `pub(super)` needs a parent module (E0433 at a crate
    /// root), and `pub(in path)` must start with `crate`, `self`, or
    /// `super` and name `module` or one of its ancestors (E0742).
    pub fn restriction_ok(&self, vis: &VisKind, module: ModuleId, interner: &Interner) -> bool {
        match vis {
            VisKind::Super => self.modules[module.0 as usize].parent.is_some(),
            // `pub(in $crate::..)` from another crate's macro starts with a
            // magic segment that `resolve_in_path` does not place; it is
            // not checked here.
            VisKind::In(path) => {
                let path = VisKind::in_path(*path, interner);
                // `pub(in $crate::..)` (see above): its magic first segment.
                path.first().is_some_and(|s| self.crate_magic.contains_key(s))
                    || matches!(path.first().map(|s| interner.get(*s)), Some("crate" | "self" | "super"))
                        && self.resolve_in_path(&path, module, interner).is_some_and(|m| self.is_within(module, m))
            }
            VisKind::Priv | VisKind::Pub | VisKind::Crate => true,
        }
    }

    /// The set of modules a visibility reaches, as a region for the
    /// re-export subset check: everywhere (pub), the whole crate, or one
    /// module subtree.
    pub(super) fn vis_region(&self, vis: &VisKind, def_module: ModuleId, interner: &Interner) -> (u8, Option<ModuleId>) {
        let region = self.vis_region_raw(vis, def_module, interner);
        // A region rooted at a crate root is the whole crate: a private
        // root item reaches as far as `pub(crate)`.
        match region {
            (0, Some(m)) if self.modules[m.0 as usize].parent.is_none() => (1, None),
            _ => region,
        }
    }

    /// `vis_region` before a crate-root region is widened to the crate.
    fn vis_region_raw(&self, vis: &VisKind, def_module: ModuleId, interner: &Interner) -> (u8, Option<ModuleId>) {
        match vis {
            VisKind::Pub => (2, None),
            VisKind::Crate => (1, None),
            VisKind::Priv => (0, Some(def_module)),
            VisKind::Super => match self.modules[def_module.0 as usize].parent {
                Some(p) => (0, Some(p)),
                None => (1, None),
            },
            VisKind::In(path) => match self.resolve_in_path(&VisKind::in_path(*path, interner), def_module, interner) {
                Some(m) => (0, Some(m)),
                None => (0, Some(def_module)),
            },
        }
    }

    /// True when the region of `vis` (at `def_module`) is inside the
    /// region of `outer` (at `outer_module`).
    pub(super) fn vis_within(&self, vis: &VisKind, def_module: ModuleId, outer: &VisKind, outer_module: ModuleId, interner: &Interner) -> bool {
        let (ra, ma) = self.vis_region(vis, def_module, interner);
        let (rb, mb) = self.vis_region(outer, outer_module, interner);
        if rb == 2 {
            return true;
        }
        if ra == 2 {
            return false;
        }
        if rb == 1 {
            return true;
        }
        if ra == 1 {
            return false;
        }
        match (ma, mb) {
            (Some(a), Some(b)) => self.is_within(a, b),
            _ => true,
        }
    }

    /// The re-export rule (rustc E0364): a non-private `use` of an item
    /// whose own visibility reaches less than the `use` would is an
    /// error. Reports and returns false when the import may not bind.
    fn check_reexport(&self, imp: &Import, target: Target, name: &str, interner: &Interner, diags: &mut Vec<Diag>) -> bool {
        if imp.vis == VisKind::Priv {
            return true;
        }
        let (item_vis, item_module) = match target {
            Target::Def(d) | Target::Variant(d, _) => match self.def_info.get(&d) {
                // Macros are textual: `#[macro_export]` puts them at the
                // crate root in public, so re-export rules do not bind
                // there. A macro without it is public only within its
                // crate: a `pub use` of it is rustc E0364 ("only public
                // within the crate"), while `pub(crate) use` is the
                // re-export idiom. An exported macro has a public
                // binding at its crate root.
                Some(info) if info.kind == ResKind::Macro => {
                    if imp.vis != VisKind::Pub {
                        return true;
                    }
                    let root = self.root_of(info.module);
                    let sym = interner.intern(name);
                    let exported = matches!(self.lookup(root, Namespace::Macro, sym),
                        Some(BindState::One(b)) if b.target == target && b.vis == VisKind::Pub);
                    if exported {
                        return true;
                    }
                    diags.push(reexport_diag(name, imp.span));
                    return false;
                }
                Some(info) => (info.vis.clone(), info.module),
                None => return true,
            },
            Target::Module(m) => {
                let info = &self.modules[m.0 as usize];
                (info.vis.clone(), info.parent.unwrap_or(crate::ty::defs::ROOT_MODULE))
            }
            Target::Extern(_) => return true,
        };
        if self.vis_within(&imp.vis, imp.module, &item_vis, item_module, interner) {
            return true;
        }
        diags.push(reexport_diag(name, imp.span));
        false
    }

    /// The visibility and defining module of the binding a one-segment
    /// `use name` reaches when it names extern crate `i`: the module's
    /// own binding of `name` (an `extern crate` item, or a std alias such
    /// as `use std as core;`), else the crate root's `extern crate` item,
    /// which is the extern prelude's entry. None for a plain extern
    /// prelude name.
    fn extern_binding_vis(&self, module: ModuleId, name: Sym, i: u32) -> Option<(VisKind, ModuleId)> {
        let key = (module, ns_index(Namespace::Type) as u8, name);
        if let Some((avis, _)) = self.std_aliases.get(&key) {
            return Some((avis.clone(), self.std_alias_def_module(key)));
        }
        for m in [module, self.root_of(module)] {
            if let Some(BindState::One(b)) = self.lookup(m, Namespace::Type, name)
                && b.target == Target::Extern(i)
            {
                return Some((b.vis.clone(), b.def_module));
            }
        }
        None
    }

    /// The visibility a glob import gives one name, as rustc does: the
    /// `use` visibility when the source binding reaches at least as far,
    /// else the source binding's own narrower visibility at its own
    /// module. So `pub use inner::*` of a `pub(super)` item binds it as
    /// that `pub(super)`, not as `pub`.
    pub(super) fn glob_vis(&self, imp: &Import, vis: &VisKind, def_module: ModuleId, interner: &Interner) -> (VisKind, ModuleId) {
        if self.vis_within(&imp.vis, imp.module, vis, def_module, interner) {
            (imp.vis.clone(), imp.module)
        } else {
            (vis.clone(), def_module)
        }
    }

    /// Resolves a `pub(in path)` path, written relative to the defining
    /// module. The segments are module names (with `crate`, `self`, and
    /// `super` allowed in front), matched by name against module paths.
    pub fn resolve_in_path(&self, path: &[Sym], def_module: ModuleId, interner: &Interner) -> Option<ModuleId> {
        let crate_sym = interner.intern("crate");
        let self_sym = interner.intern("self");
        let super_sym = interner.intern("super");
        let (mut base_path, rest): (Vec<Sym>, &[Sym]) = match path.first() {
            Some(&s) if s == crate_sym => (Vec::new(), &path[1..]),
            Some(&s) if s == self_sym => (self.modules[def_module.0 as usize].path.clone(), &path[1..]),
            Some(&s) if s == super_sym => {
                let mut p = self.modules[def_module.0 as usize].path.clone();
                let mut rest = path;
                while rest.first() == Some(&super_sym) {
                    p.pop()?;
                    rest = &rest[1..];
                }
                (p, rest)
            }
            // A plain path in `pub(in ...)` is read from the crate root's
            // perspective when it names a root descendant chain; Rust
            // reads it relative to the current module, and the written
            // forms in practice start with `crate`/`self`/`super`. Treat
            // a bare path as relative to the defining module.
            _ => (self.modules[def_module.0 as usize].path.clone(), path),
        };
        base_path.extend_from_slice(rest);
        self.module_by_path_in(self.root_of(def_module), &base_path)
    }

    /// Inserts a binding, applying the priority rules. Returns `Changed`
    /// when the table now answers differently, `Dup` when two same-rank
    /// explicit sources name different targets (a user error the caller
    /// reports after the fixpoint).
    pub fn insert(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind) -> InsertOut {
        let out = self.insert_inner(module, ns, name, bind);
        // Any change through here ends a glob source's ownership of
        // the binding (`glob_src`): its later copy refresh must not
        // take an ambiguity another glob's insert made (a variant
        // glob beside a type glob, in the type namespace) for a
        // stale copy of its own and reset it to One. `insert_glob`
        // re-records ownership for its own copies right after.
        if out == InsertOut::Changed && self.glob_src.remove(&(module, ns_index(ns) as u8, name)).is_some() {
            self.touch(module, name);
        }
        out
    }

    fn insert_inner(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind) -> InsertOut {
        // A glob std alias of the name loses to a local item or explicit
        // import, and is ambiguous with a glob binding of a crate item.
        let key = (module, ns_index(ns) as u8, name);
        if !self.std_glob_aliases.is_empty()
            && let Some(alias_def) = self.std_glob_aliases.remove(&key)
        {
            self.touch(module, name);
            let alias = self.std_aliases.remove(&key);
            if bind.rank <= 1 {
                let mut vis: Vec<AmbEntry> = alias.map(|(v, path)| (v, alias_def, AmbItem::Std(path))).into_iter().collect();
                vis.push((bind.vis.clone(), bind.def_module, AmbItem::Item(bind.target)));
                let _ = self.set_ambiguous(module, ns, name, vis);
                return InsertOut::Changed;
            }
        }
        let wider = matches!(self.lookup(module, ns, name),
            Some(BindState::One(old)) if old.target == bind.target && old.rank == 1 && bind.rank == 1 && self.glob_vis_wider(&bind, old));
        let map = &mut self.maps[module.0 as usize][ns_index(ns)];
        let out = match map.get(&name) {
            None => {
                map.insert(name, BindState::One(bind));
                InsertOut::Changed
            }
            Some(BindState::One(old)) => {
                if old.target == bind.target {
                    // The same target bound twice at explicit rank is still
                    // two definitions of one name (rustc E0252/E0255): a
                    // repeated `use`, or a `use` of an item this module
                    // defines. A glob (rank 1) re-binding the same target
                    // is legal and stays `Same`. An explicit import of the
                    // item a glob already brought is legal too, and it
                    // raises the binding to explicit rank: other globs
                    // can then no longer make the name ambiguous here. A
                    // second glob of the item with a wider visibility
                    // widens the binding, as rustc keeps the widest
                    // (`ambiguity_vis_max`; `resolve::order` rejects the
                    // orders where rustc drops it again).
                    if old.rank == 2 && bind.rank == 2 {
                        InsertOut::Dup
                    } else if bind.rank > old.rank {
                        map.insert(name, BindState::One(bind));
                        InsertOut::Changed
                    } else if wider {
                        map.insert(name, BindState::One(bind));
                        InsertOut::Changed
                    } else {
                        InsertOut::Same
                    }
                } else if bind.rank > old.rank {
                    map.insert(name, BindState::One(bind));
                    InsertOut::Changed
                } else if bind.rank < old.rank {
                    InsertOut::Same
                } else if bind.rank <= 1 {
                    let vis = vec![
                        (old.vis.clone(), old.def_module, AmbItem::Item(old.target)),
                        (bind.vis.clone(), bind.def_module, AmbItem::Item(bind.target)),
                    ];
                    let _ = self.set_ambiguous(module, ns, name, vis);
                    InsertOut::Changed
                } else {
                    InsertOut::Dup
                }
            }
            Some(BindState::Ambiguous) => {
                if bind.rank >= 2 {
                    map.insert(name, BindState::One(bind));
                    InsertOut::Changed
                } else {
                    // One more glob item: its visibility can carry
                    // the ambiguity onward too.
                    if self.set_ambiguous(module, ns, name, vec![(bind.vis, bind.def_module, AmbItem::Item(bind.target))]) {
                        InsertOut::Changed
                    } else {
                        InsertOut::Same
                    }
                }
            }
        };
        if out == InsertOut::Changed {
            self.touch(module, name);
        }
        out
    }

    /// True when glob binding `a` reaches strictly more modules than `b`.
    /// A `pub(in path)` visibility compares as neither (lust keeps the
    /// first binding there).
    fn glob_vis_wider(&self, a: &Bind, b: &Bind) -> bool {
        let region = |vis: &VisKind, m: ModuleId| -> Option<(u8, ModuleId)> {
            match vis {
                VisKind::Pub => Some((2, m)),
                VisKind::Crate => Some((1, self.root_of(m))),
                VisKind::Priv => Some((0, m)),
                VisKind::Super => Some(match self.modules[m.0 as usize].parent {
                    Some(p) => (0, p),
                    None => (1, self.root_of(m)),
                }),
                VisKind::In(_) => None,
            }
        };
        let (Some((ra, ma)), Some((rb, mb))) = (region(&a.vis, a.def_module), region(&b.vis, b.def_module)) else { return false };
        match (ra, rb) {
            (2, 2) => false,
            (2, _) => true,
            (1, 1) => false,
            (1, 0) => self.root_of(ma) == self.root_of(mb),
            (0, 0) => ma != mb && self.is_within(mb, ma),
            _ => false,
        }
    }

    /// Records a change of `name` in `module` (`glob_log`).
    pub fn touch(&mut self, module: ModuleId, name: Sym) {
        let i = module.0 as usize;
        if self.glob_log.len() <= i {
            self.glob_log.resize_with(i + 1, Vec::new);
        }
        self.glob_log[i].push(name);
    }

    /// How many changes `module` has logged (`glob_log`).
    pub fn log_len(&self, module: ModuleId) -> usize {
        self.glob_log.get(module.0 as usize).map_or(0, Vec::len)
    }

    /// Marks a name `Ambiguous`, with the visibilities of the bindings
    /// that clash (`ambig_vis`). A name that is already ambiguous adds
    /// them to its list. Returns true when the state or the list changed.
    pub fn set_ambiguous(&mut self, module: ModuleId, ns: Namespace, name: Sym, vis: Vec<AmbEntry>) -> bool {
        let key = (module, ns_index(ns) as u8, name);
        self.ambiguous_keys.insert(key, ());
        let map = &mut self.maps[module.0 as usize][ns_index(ns)];
        let old = map.insert(name, BindState::Ambiguous);
        let was = matches!(old, Some(BindState::Ambiguous));
        let list = self.ambig_vis.entry(key).or_default();
        if !was {
            list.clear();
        }
        // A glob binding the ambiguity replaces still counts.
        let old_vis = match old {
            Some(BindState::One(b)) if b.rank <= 1 => Some((b.vis, b.def_module, AmbItem::Item(b.target))),
            _ => None,
        };
        let mut grew = !was;
        for v in old_vis.into_iter().chain(vis) {
            if !list.contains(&v) {
                list.push(v);
                grew = true;
            }
        }
        if grew {
            self.touch(module, name);
        }
        grew
    }

    /// True when the ambiguity of `name` in `src` is certain in rustc.
    /// With `from` (a glob importer), it must also reach `from`: `from`
    /// sees two different items among the clashing bindings, or a
    /// certain ambiguity of a globbed module. rustc gives a propagated
    /// ambiguity the visibility of the glob it saw first, so with one
    /// visible item it may stay in `src`. Without `from` (an import of
    /// the name from `src`), `src` itself must hold two different items
    /// or a certain ambiguity: rustc reports that import whatever it
    /// sees. A use of an uncertain name still rejects; an import that
    /// read one is not reported for it at the end. No record counts as
    /// certain (that only rejects).
    pub fn ambiguous_certain(&self, src: ModuleId, ns: Namespace, name: Sym, from: Option<ModuleId>, interner: &Interner) -> bool {
        let Some(list) = self.ambig_vis.get(&(src, ns_index(ns) as u8, name)) else { return true };
        let mut items: Vec<&AmbItem> = Vec::new();
        for (v, m, item) in list {
            if let Some(from) = from
                && !self.visible(v, *m, from, interner)
            {
                continue;
            }
            match item {
                AmbItem::Amb { certain: true } => return true,
                AmbItem::Amb { certain: false } => {}
                _ if !items.contains(&item) => items.push(item),
                _ => {}
            }
        }
        items.len() >= 2
    }

    /// True when an importer in `from` can see the ambiguous name
    /// `name` of module `src` (`ambig_vis`): one of the clashing
    /// bindings is visible there. rustc gives the ambiguity the
    /// visibility of the glob it saw first, in its own order; any one
    /// visible binding is the safe reading (it only rejects). A name
    /// with no recorded visibility counts as visible.
    pub fn ambiguous_visible(&self, src: ModuleId, ns: Namespace, name: Sym, from: ModuleId, interner: &Interner) -> bool {
        match self.ambig_vis.get(&(src, ns_index(ns) as u8, name)) {
            Some(list) if !list.is_empty() => list.iter().any(|(v, m, _)| self.visible(v, *m, from, interner)),
            _ => true,
        }
    }

    /// Inserts one glob copy from source module `src` (see `glob_src`).
    /// A binding this same source put here earlier, with a different
    /// target, follows the source's upgrade: it is replaced, not made
    /// ambiguous. A copy from any other source keeps the plain rules.
    pub fn insert_glob(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind, src: ModuleId) -> InsertOut {
        let key = (module, ns_index(ns) as u8, name);
        // The two common cases first, each with the outcome of the general path below in
        // fewer table reads (a glob copy inserts millions of names on tsgo): with no std alias
        // of the name here, a name with no binding and no glob source takes the copy, and a
        // binding that the copy would not change stays.
        if !self.std_glob_aliases.contains_key(&key) {
            match self.maps[module.0 as usize][ns_index(ns)].get(&name) {
                None if !self.glob_src.contains_key(&key) => {
                    self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::One(bind));
                    self.touch(module, name);
                    self.glob_src.insert(key, src);
                    return InsertOut::Changed;
                }
                Some(BindState::One(old))
                    if if old.target == bind.target {
                        bind.rank <= old.rank
                            && !(old.rank == 2 && bind.rank == 2)
                            && !(old.rank == 1 && bind.rank == 1 && self.glob_vis_wider(&bind, old))
                    } else {
                        bind.rank < old.rank && old.rank >= 2
                    } =>
                {
                    return InsertOut::Same;
                }
                _ => {}
            }
        }
        // The name's binding here now, read once: a stale copy of this
        // source (another item at glob rank), an ambiguity it made, or
        // the same item.
        let (stale, ambiguous, same_item) = match self.lookup(module, ns, name) {
            Some(BindState::One(old)) => (old.rank <= 1 && old.target != bind.target, false, old.target == bind.target),
            Some(BindState::Ambiguous) => (false, true, false),
            None => (false, false, false),
        };
        // The mirror case of a stale copy: this source made the name
        // ambiguous here (its own binding was ambiguous, propagated by
        // the glob copy in `try_import`), and its binding has since
        // settled to one item (its explicit import landed). The copy
        // follows it back to that item; any other live glob that still
        // brings a different item re-makes the ambiguity on a later sweep.
        if (stale || ambiguous) && self.glob_src.get(&key) == Some(&src) && !self.std_glob_aliases.contains_key(&key) {
            self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::One(bind));
            self.touch(module, name);
            return InsertOut::Changed;
        }
        // A wider copy of the same item keeps the source it came from first.
        let out = self.insert(module, ns, name, bind);
        match self.lookup(module, ns, name) {
            Some(BindState::One(_)) => {
                if out == InsertOut::Changed && !same_item {
                    self.glob_src.insert(key, src);
                }
            }
            _ => {
                if self.glob_src.remove(&key).is_some() {
                    self.touch(module, name);
                }
            }
        }
        out
    }

    /// One name's binding, without prelude or flat-name fallback. This is
    /// the raw table read; `Program::binding` layers the fallbacks.
    pub fn lookup(&self, module: ModuleId, ns: Namespace, name: Sym) -> Option<&BindState> {
        crate::resolve::mdr::read_key(module, ns_index(ns) as u8, name);
        self.maps.get(module.0 as usize).and_then(|m| m[ns_index(ns)].get(&name))
    }

    /// The macro-namespace binding one import of `name` from module
    /// `src` reads. A `macro_rules!` definition's own binding is
    /// textual only (`macro_textual_binds`), so no import path reads
    /// it. A one-segment relative `use name;` (`one_seg`) reads the
    /// macros textually in scope at the `use` first, as rustc does; a
    /// different macro in the module's namespace makes it ambiguous
    /// (rustc E0659).
    pub fn macro_import_lookup(&self, imp: &Import, src: ModuleId, one_seg: bool, name: Sym) -> Option<BindState> {
        let module_bind = match self.lookup(src, Namespace::Macro, name) {
            Some(BindState::One(b)) if self.is_textual_bind(src, name, b) => None,
            other => other.cloned(),
        };
        if !one_seg || imp.leading_colon {
            return module_bind;
        }
        match self.textual_macro_at(imp, name) {
            None => module_bind,
            // A dependency's macro through `#[macro_use] extern crate`:
            // lust does not import it by path.
            Some(None) => None,
            Some(Some(def)) => match module_bind {
                Some(BindState::One(b)) if b.target != Target::Def(def) => Some(BindState::Ambiguous),
                Some(BindState::Ambiguous) => Some(BindState::Ambiguous),
                _ => Some(BindState::One(Bind { target: Target::Def(def), vis: VisKind::Priv, rank: 2, def_module: imp.module })),
            },
        }
    }

    /// True when `b`, module `module`'s macro binding of `name`, is a
    /// `macro_rules!` definition's textual-only binding.
    pub fn is_textual_bind(&self, module: ModuleId, name: Sym, b: &Bind) -> bool {
        matches!(b.target, Target::Def(d) if self.macro_textual_binds.get(&(module, name)) == Some(&d))
    }

    /// The macro named `name` in textual scope at one import (Some(None)
    /// for a dependency's macro), or None when the import's file has
    /// no recorded scope or no such macro.
    fn textual_macro_at(&self, imp: &Import, name: Sym) -> Option<Option<DefId>> {
        let (file_module, scope) = self.macro_scopes.get(&imp.span.file)?;
        let base = &self.modules[file_module.0 as usize].path;
        let container = self.modules[imp.module.0 as usize].path.strip_prefix(base.as_slice())?;
        scope.at(container, imp.span.lo, name)
    }

    /// True when `module` has an explicit std alias (not a glob one)
    /// under this key.
    pub fn explicit_std_alias(&self, key: (ModuleId, u8, Sym)) -> bool {
        self.std_aliases.contains_key(&key) && !self.std_glob_aliases.contains_key(&key)
    }

    /// The module whose scope defines privacy for one std alias.
    pub fn std_alias_def_module(&self, key: (ModuleId, u8, Sym)) -> ModuleId {
        self.std_glob_aliases.get(&key).copied().unwrap_or(key.0)
    }

    /// The std aliases of one module that code in `from` can see, as
    /// (namespace index, name, vis, defining module, path). A glob of
    /// `module` imports these as it imports the module's bindings.
    pub fn visible_std_aliases(&self, module: ModuleId, from: ModuleId, interner: &Interner) -> Vec<(u8, Sym, VisKind, ModuleId, Vec<Sym>)> {
        crate::resolve::mdr::read(module);
        self.std_aliases
            .range((module, 0, Sym(0))..=(module, u8::MAX, Sym(u32::MAX)))
            .filter_map(|(&key, (vis, path))| {
                let def_module = self.std_alias_def_module(key);
                self.visible(vis, def_module, from, interner).then(|| (key.1, key.2, vis.clone(), def_module, path.clone()))
            })
            .collect()
    }

    /// Binds a std alias at glob rank (`use prelude::*;` of a module
    /// with `pub use std::rc::Rc;`). A local item, an explicit import,
    /// or an explicit std alias of the name wins. A glob binding of a
    /// crate item, or a glob alias of another std item, makes the name
    /// ambiguous (rustc E0659 when used). Returns true on a change.
    pub fn insert_glob_std_alias(&mut self, module: ModuleId, ns: Namespace, name: Sym, vis: VisKind, def_module: ModuleId, path: Vec<Sym>) -> bool {
        let key = (module, ns_index(ns) as u8, name);
        match self.lookup(module, ns, name) {
            Some(BindState::One(b)) if b.rank >= 2 => return false,
            Some(BindState::Ambiguous) => return self.set_ambiguous(module, ns, name, vec![(vis, def_module, AmbItem::Std(path))]),
            Some(BindState::One(b)) => {
                let both = vec![(b.vis.clone(), b.def_module, AmbItem::Item(b.target)), (vis, def_module, AmbItem::Std(path))];
                let _ = self.set_ambiguous(module, ns, name, both);
                return true;
            }
            None => {}
        }
        match self.std_aliases.get(&key) {
            None => {
                self.std_aliases.insert(key, (vis, path));
                self.std_glob_aliases.insert(key, def_module);
                self.touch(module, name);
                true
            }
            Some(_) if !self.std_glob_aliases.contains_key(&key) => false,
            Some((_, old)) if same_std_item(old, &path) => false,
            Some(_) => {
                let (old_vis, old_path) = self.std_aliases.remove(&key).expect("checked above");
                let old_def = self.std_glob_aliases.remove(&key).unwrap_or(module);
                self.touch(module, name);
                let both = vec![(old_vis, old_def, AmbItem::Std(old_path)), (vis, def_module, AmbItem::Std(path))];
                let _ = self.set_ambiguous(module, ns, name, both);
                true
            }
        }
    }

    /// True when some module defines `name` locally (not by import), in
    /// any namespace. The rewrite pass uses it for the lexical-scope
    /// rule: a bare name that only an enclosing or sibling module
    /// defines must error, never fall through to the flat tables.
    pub fn any_local_named(&self, name: Sym) -> bool {
        self.maps.iter().enumerate().any(|(mi, maps)| {
            maps.iter().any(|m| matches!(m.get(&name), Some(BindState::One(b)) if b.rank == 2 && b.def_module.0 as usize == mi))
        })
    }

    /// Every name some module defines locally, as a set (see
    /// `any_local_named`). The rewrite pass builds this once over the
    /// frozen tables instead of rescanning every module map per
    /// unresolved path, which was quadratic in the module count.
    /// The value is a bit set of the namespaces (by `ns_index`) some
    /// module defines the name in. The maps hold every glob copy too
    /// (millions on tsgo, scanned once per crate job), so runs of modules
    /// are scanned on the pool and their sets joined.
    pub fn local_named_set(&self) -> FxMap<Sym, u8> {
        let run = self.maps.len().div_ceil(crate::pool::threads() * 4).max(1);
        let starts: Vec<usize> = (0..self.maps.len()).step_by(run).collect();
        let parts = crate::pool::par_map(&starts, |&lo| {
            let mut out: FxMap<Sym, u8> = FxMap::default();
            for (mi, maps) in self.maps.iter().enumerate().skip(lo).take(run) {
                for (ns, m) in maps.iter().enumerate() {
                    for (name, state) in m {
                        if matches!(state, BindState::One(b) if b.rank == 2 && b.def_module.0 as usize == mi) {
                            *out.entry(*name).or_default() |= 1 << ns;
                        }
                    }
                }
            }
            out
        });
        let mut out: FxMap<Sym, u8> = FxMap::default();
        for (name, bits) in parts.into_iter().flatten() {
            *out.entry(name).or_default() |= bits;
        }
        out
    }

    /// A fingerprint of every fact the path rewrite pass can read:
    /// modules, bindings, def info, associated and field visibility,
    /// variants, flat names, module defs, and the extern prelude.
    /// Spans never hash (a line shift in one file must not move the
    /// epoch of the others). The worklist keys its per-file
    /// rewritten-Ast cache on this value: when it stands, a file
    /// whose text stands rewrites to the same Ast. Accumulation is
    /// order-independent per entry (map iteration order is not a
    /// fact), with entry counts folded in.
    pub fn rewrite_epoch(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        fn vis(h: &mut crate::intern::FxHasher, v: &VisKind) {
            match v {
                VisKind::Priv => h.write_u64(1),
                VisKind::Pub => h.write_u64(2),
                VisKind::Crate => h.write_u64(3),
                VisKind::Super => h.write_u64(4),
                VisKind::In(path) => {
                    h.write_u64(5);
                    h.write_u64(path.0 as u64);
                }
            }
        }
        fn target(h: &mut crate::intern::FxHasher, t: &Target) {
            match t {
                Target::Def(d) => {
                    h.write_u64(1);
                    h.write_u64(d.hash.0);
                    h.write_u64(d.krate.0 as u64);
                }
                Target::Module(m) => {
                    h.write_u64(2);
                    h.write_u64(m.0 as u64);
                }
                Target::Extern(i) => {
                    h.write_u64(3);
                    h.write_u64(*i as u64);
                }
                Target::Variant(d, s) => {
                    h.write_u64(4);
                    h.write_u64(d.hash.0);
                    h.write_u64(d.krate.0 as u64);
                    h.write_u64(s.0 as u64);
                }
            }
        }
        let mut acc: u64 = 0x51_7c_c1_b7_27_22_0a_95;
        let mut n: u64 = 0;
        macro_rules! fold {
            ($tag:expr, $body:expr) => {{
                let mut h = crate::intern::FxHasher::default();
                h.write_u64($tag);
                $body(&mut h);
                acc = acc.wrapping_add(h.finish().wrapping_mul(0x9e_37_79_b9_7f_4a_7c_15));
                n += 1;
            }};
        }
        for (i, m) in self.modules.iter().enumerate() {
            fold!(0x10, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                h.write_u64(m.parent.map_or(u64::MAX, |p| p.0 as u64));
                h.write_u64(m.name.0 as u64);
                h.write_u64(m.no_prelude as u64);
                for s in &m.path {
                    h.write_u64(s.0 as u64);
                }
                vis(h, &m.vis);
            });
        }
        for (mi, maps) in self.maps.iter().enumerate() {
            for (ns, m) in maps.iter().enumerate() {
                for (name, state) in m {
                    fold!(0x20, |h: &mut crate::intern::FxHasher| {
                        h.write_u64(mi as u64);
                        h.write_u64(ns as u64);
                        h.write_u64(name.0 as u64);
                        match state {
                            BindState::Ambiguous => h.write_u64(0),
                            BindState::One(b) => {
                                h.write_u64(1);
                                target(h, &b.target);
                                vis(h, &b.vis);
                                h.write_u64(b.rank as u64);
                                h.write_u64(b.def_module.0 as u64);
                            }
                        }
                    });
                }
            }
        }
        for (i, e) in self.externs.iter().enumerate() {
            fold!(0x30, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                e.name.hash(h);
                h.write_u64(e.def.hash.0);
                h.write_u64(e.def.krate.0 as u64);
                h.write_u64(e.is_std_lib as u64);
                h.write_u64(e.owner.0 as u64);
                h.write_u64(e.root_module.map_or(u64::MAX, |m| m.0 as u64));
                e.unsupported.hash(h);
            });
        }
        for m in &self.alloc_roots {
            fold!(0x49, |h: &mut crate::intern::FxHasher| h.write_u64(m.0 as u64));
        }
        for (name, m) in &self.std_modules {
            fold!(0x48, |h: &mut crate::intern::FxHasher| {
                h.write_u64(name.0 as u64);
                h.write_u64(m.0 as u64);
                h.write_u64(self.std_splice_lo.map_or(u64::MAX, |lo| lo as u64));
            });
        }
        for (magic, root) in &self.crate_magic {
            fold!(0x46, |h: &mut crate::intern::FxHasher| {
                h.write_u64(magic.0 as u64);
                h.write_u64(root.0 as u64);
            });
        }
        for ((module, ns, name), (v, path)) in &self.std_aliases {
            fold!(0x47, |h: &mut crate::intern::FxHasher| {
                h.write_u64(module.0 as u64);
                h.write_u64(*ns as u64);
                h.write_u64(name.0 as u64);
                vis(h, v);
                for s in path {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (module, path) in &self.std_globs {
            fold!(0x48, |h: &mut crate::intern::FxHasher| {
                h.write_u64(module.0 as u64);
                for s in path {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (def, m) in &self.assoc_vis {
            for (name, (v, dm)) in m {
                fold!(0x40, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(dm.0 as u64);
                    vis(h, v);
                });
            }
        }
        for (def, (dm, m)) in &self.field_vis {
            for (name, v) in m {
                fold!(0x41, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(dm.0 as u64);
                    vis(h, v);
                });
            }
        }
        for (def, names) in &self.variants {
            fold!(0x42, |h: &mut crate::intern::FxHasher| {
                h.write_u64(def.hash.0);
                h.write_u64(def.krate.0 as u64);
                for s in names {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (def, info) in &self.def_info {
            fold!(0x43, |h: &mut crate::intern::FxHasher| {
                h.write_u64(def.hash.0);
                h.write_u64(def.krate.0 as u64);
                h.write_u64(match info.kind {
                    ResKind::Fn => 1,
                    ResKind::Adt => 2,
                    ResKind::Const => 3,
                    ResKind::Static => 4,
                    ResKind::Alias => 5,
                    ResKind::Macro => 6,
                    ResKind::Trait => 7,
                });
                h.write_u64(info.flat.0 as u64);
                h.write_u64(info.module.0 as u64);
                vis(h, &info.vis);
            });
        }
        for (&(m, ns, name), set) in &self.order_dep {
            fold!(0x4b, |h: &mut crate::intern::FxHasher| {
                h.write_u64(m.0 as u64);
                h.write_u64(ns as u64);
                h.write_u64(name.0 as u64);
                h.write_u64(set.absent as u64);
                h.write_u64(set.fixed as u64);
                h.write_u64(set.ends.len() as u64);
                for (v, dm, item) in set.ends.iter().chain(&set.all) {
                    vis(h, v);
                    h.write_u64(dm.0 as u64);
                    match item {
                        AmbItem::Item(t) => target(h, t),
                        AmbItem::Std(path) => path.iter().for_each(|s| h.write_u64(s.0 as u64)),
                        AmbItem::Amb { .. } => h.write_u64(7),
                    }
                }
            });
        }
        for (i, d) in self.module_defs.iter().enumerate() {
            fold!(0x44, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                h.write_u64(d.hash.0);
                h.write_u64(d.krate.0 as u64);
            });
        }
        for (ns, m) in self.flat.iter().enumerate() {
            for (name, def) in m {
                fold!(0x45, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(ns as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                });
            }
        }
        let mut h = crate::intern::FxHasher::default();
        h.write_u64(acc);
        h.write_u64(n);
        h.finish()
    }

    /// The answer for the S7 query fns: the module table first, then the
    /// flat-name index (the merged AST's rewritten names, which the
    /// checker asks about in the root module). None means "no answer
    /// here": the caller falls back to builtins and the std prelude.
    pub fn binding(&self, module: ModuleId, ns: Namespace, name: Sym) -> Option<BindingRes> {
        if let Some(state) = self.lookup(module, ns, name) {
            return Some(match state {
                BindState::One(b) => BindingRes::Def(self.target_def(b.target)),
                BindState::Ambiguous => BindingRes::Ambiguous,
            });
        }
        self.flat[ns_index(ns)].get(&name).map(|d| BindingRes::Def(*d))
    }

    /// The DefId a target answers with in a binding query. A module's def
    /// is its module def; an extern's is the extern root def.
    pub fn target_def(&self, target: Target) -> DefId {
        match target {
            Target::Def(d) | Target::Variant(d, _) => d,
            Target::Module(m) => self.module_def(m),
            Target::Extern(i) => self.externs[i as usize].def,
        }
    }

    /// A module's own def, filled by the worklist at registration. The
    /// placeholder answers only before registration runs.
    pub fn module_def(&self, m: ModuleId) -> DefId {
        self.module_defs.get(m.0 as usize).copied().unwrap_or(DefId::PLACEHOLDER)
    }
}

/// The result of one insert, for the fixpoint's change tracking.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InsertOut {
    Changed,
    Same,
    Dup,
}

// ---------- Path resolution ----------

/// How a path's first segment resolves (section 1.3 scope priority).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PathMode {
    /// Lexical paths in bodies and signatures: the current module only,
    /// then the extern prelude, then the std prelude.
    Lexical,
    /// `use` paths (2018 uniform paths): the current module, then the
    /// extern prelude.
    Use,
}

/// The answer of a path resolution. `rest` is the index of the first
/// segment the resolution did not consume: for an Adt, an associated
/// item or variant follows; for an extern, the rest belongs to that
/// crate. `Private` means the name exists but its binding's visibility
/// does not reach the asking module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathRes {
    Done(Target),
    Partial(Target, usize),
    Ambiguous,
    /// The name's binding depends on rustc's glob order
    /// (`ResolvedTables::order_dependent`, L0509).
    OrderDep,
    Private,
    /// The first segment names a std prelude item. Callers leave the
    /// written path to the std compat handling.
    Prelude,
    Absent,
}

/// Type-namespace names in the std prelude (edition 2024). The list is
/// the classification layer of section 1.3: these names are never module
/// bindings, a glob never carries them, and a local def, explicit
/// import, or glob with the same name wins over them.
pub const STD_PRELUDE_TYPES: &[&str] = &[
    "Option",
    "Result",
    "String",
    "Vec",
    "Box",
    "Copy",
    "Clone",
    "Debug",
    "Default",
    "Eq",
    "PartialEq",
    "PartialOrd",
    "Ord",
    "Hash",
    "Iterator",
    "IntoIterator",
    "From",
    "Into",
    "Send",
    "Sync",
    "Sized",
    "Drop",
    "Fn",
    "FnMut",
    "FnOnce",
    "ToString",
    "ToOwned",
    "AsRef",
    "AsMut",
    "Borrow",
    "BorrowMut",
    "Deref",
    "DerefMut",
    "Unpin",
];

/// Value-namespace names in the std prelude.
pub const STD_PRELUDE_VALUES: &[&str] = &["Some", "None", "Ok", "Err"];

/// True when `name` is a std prelude name in namespace `ns`.
pub fn in_std_prelude(name: &str, ns: Namespace) -> bool {
    match ns {
        Namespace::Type => STD_PRELUDE_TYPES.contains(&name),
        Namespace::Value => STD_PRELUDE_VALUES.contains(&name),
        Namespace::Macro => false,
    }
}

/// The canonical path (after the crate root) of one std prelude name:
/// what `std::prelude` re-exports it from. Import resolution reads
/// it to tell a glob-brought re-export of the prelude item itself
/// (`pub use std::option::Option;` globbed in, then `use Option::*;`,
/// which rustc accepts) from a different item of the same name
/// (ambiguous with the prelude, rustc E0659).
pub fn prelude_std_suffix(name: &str) -> Option<&'static [&'static str]> {
    Some(match name {
        "Option" => &["option", "Option"],
        "Result" => &["result", "Result"],
        "String" => &["string", "String"],
        "Vec" => &["vec", "Vec"],
        "Box" => &["boxed", "Box"],
        "Copy" => &["marker", "Copy"],
        "Clone" => &["clone", "Clone"],
        "Debug" => &["fmt", "Debug"],
        "Default" => &["default", "Default"],
        "Eq" => &["cmp", "Eq"],
        "PartialEq" => &["cmp", "PartialEq"],
        "PartialOrd" => &["cmp", "PartialOrd"],
        "Ord" => &["cmp", "Ord"],
        "Hash" => &["hash", "Hash"],
        "Iterator" => &["iter", "Iterator"],
        "IntoIterator" => &["iter", "IntoIterator"],
        "From" => &["convert", "From"],
        "Into" => &["convert", "Into"],
        "Send" => &["marker", "Send"],
        "Sync" => &["marker", "Sync"],
        "Sized" => &["marker", "Sized"],
        "Drop" => &["ops", "Drop"],
        "Fn" => &["ops", "Fn"],
        "FnMut" => &["ops", "FnMut"],
        "FnOnce" => &["ops", "FnOnce"],
        "ToString" => &["string", "ToString"],
        "ToOwned" => &["borrow", "ToOwned"],
        "AsRef" => &["convert", "AsRef"],
        "AsMut" => &["convert", "AsMut"],
        "Borrow" => &["borrow", "Borrow"],
        "BorrowMut" => &["borrow", "BorrowMut"],
        "Deref" => &["ops", "Deref"],
        "DerefMut" => &["ops", "DerefMut"],
        "Unpin" => &["marker", "Unpin"],
        "Some" => &["option", "Option", "Some"],
        "None" => &["option", "Option", "None"],
        "Ok" => &["result", "Result", "Ok"],
        "Err" => &["result", "Result", "Err"],
        _ => return None,
    })
}

/// What one first segment binds to in one scope, for import and
/// macro resolution (rustc E0659): ordinary resolution lets the
/// innermost binding win, but a name a glob import brought into an
/// inner scope does not shadow a different item of the same name in
/// an outer scope (an outer block, the module, the std prelude, or
/// the extern prelude): the two are ambiguous when an import path
/// or a macro call resolves the name.
#[derive(Clone, Debug, PartialEq)]
pub enum SegBind {
    /// Nothing in this scope binds the name.
    None,
    /// Two globs of the scope itself bring different items.
    Ambiguous,
    Target(Target),
    /// A std import alias: the canonical std path it stands for.
    Std(Vec<Sym>),
    /// A std prelude item of this name (`Option`, `Some`, ...).
    Prelude(Sym),
    /// An extern crate root of the extern prelude, by index.
    Extern(u32),
}

/// One scope's answer for a first segment: the binding, and whether
/// it arrived by a glob import (rank 1) instead of a local item or
/// an explicit import.
#[derive(Clone, Debug)]
pub struct SegInfo {
    pub bind: SegBind,
    pub glob: bool,
}

impl ResolvedTables {
    /// The extern prelude index of a crate name in the prelude of the
    /// crate `from` belongs to, if it is one there.
    pub fn extern_by_name(&self, from: ModuleId, name: &str) -> Option<u32> {
        let owner = self.root_of(from);
        self.externs.iter().position(|e| e.owner == owner && e.name == name).map(|i| i as u32)
    }

    /// `extern_by_name` for a path written in `from`: the `alloc` std
    /// extern only counts in a crate whose root has `extern crate
    /// alloc;`, in the shipped platform crate, and in the std source
    /// modules of the splice (rustc E0433 otherwise).
    fn extern_in_scope(&self, from: ModuleId, name: &str) -> Option<u32> {
        let i = self.extern_by_name(from, name)?;
        if name != "alloc" || !self.externs[i as usize].is_std_lib {
            return Some(i);
        }
        let root = self.root_of(from);
        if self.alloc_roots.contains(&root) || self.std_platform.is_some_and(|(r, _)| r == root) {
            return Some(i);
        }
        let mut m = Some(from);
        while let Some(cur) = m {
            if self.std_modules.iter().any(|&(_, sm)| sm == cur) {
                return Some(i);
            }
            m = self.modules[cur.0 as usize].parent;
        }
        None
    }

    /// True when `alloc` is a std extern of `from`'s crate that paths
    /// written in `from` cannot name (no root `extern crate alloc;`).
    pub fn alloc_out_of_scope(&self, from: ModuleId) -> bool {
        self.extern_by_name(from, "alloc").is_some() && self.extern_in_scope(from, "alloc").is_none()
    }

    /// The hidden std source module that segment `seg` names under std
    /// extern `i` (`std::time`), when the std splice defined one
    /// (src/stdmods.rs).
    /// Also says whether the module is the whole std module (`full`) or
    /// an overlay that holds only some of its items.
    pub fn std_module_at(&self, i: u32, seg: Sym, interner: &Interner) -> Option<(ModuleId, bool)> {
        let e = &self.externs[i as usize];
        if !e.is_std_lib || self.std_modules.is_empty() {
            return None;
        }
        let seg = interner.get(seg);
        let row = crate::stdmods::STD_MODULES.iter().find(|m| m.paths.iter().any(|(k, s)| *k == e.name && *s == seg))?;
        self.std_modules.iter().find(|(n, _)| interner.get(*n) == row.name).map(|(_, m)| (*m, row.full))
    }

    /// The std source overlay module of the std module `path` under std
    /// extern `i` (`std::panic`), with the items of it that a glob of
    /// `path` brings: those std 1.99 has at that path (`std_paths.txt`),
    /// so a lust helper (`__lust_run_hook`) or an item of the other
    /// crate's copy (`set_hook` under `core::panic`) stays unbound.
    pub fn std_overlay_items(&self, i: u32, path: &[Sym], interner: &Interner) -> Option<(ModuleId, Vec<(Namespace, Sym)>)> {
        let [_, seg] = path else { return None };
        let (m, false) = self.std_module_at(i, *seg, interner)? else { return None };
        let mut items = Vec::new();
        for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
            crate::resolve::mdr::read(m);
            for &name in self.maps[m.0 as usize][ns_index(ns)].keys() {
                let full = [interner.get(path[0]), interner.get(*seg), interner.get(name)];
                if crate::resolve::stdpaths::std_has(&full).is_some() {
                    items.push((ns, name));
                }
            }
        }
        items.sort_by(|a, b| (ns_index(a.0), interner.get(a.1)).cmp(&(ns_index(b.0), interner.get(b.1))));
        Some((m, items))
    }

    /// The shipped platform crate's module for the std module `path`
    /// (`std::io`, `std::os::unix::fs`; W-SHIM) and the items a glob of
    /// it brings: the ones std 1.99 also has at that path. None when the
    /// platform crate is not loaded or has no such module.
    pub fn std_platform_glob_items(&self, path: &[Sym], from: ModuleId, interner: &Interner) -> Option<(ModuleId, Vec<(Namespace, Sym)>)> {
        let (root, _) = self.std_platform?;
        let [std, first, ..] = path else { return None };
        if interner.get(*std) != "std" || !STD_PLATFORM_MODULES.contains(&interner.get(*first)) {
            return None;
        }
        let mut m = root;
        for &seg in &path[1..] {
            match self.segment_in(m, seg, Namespace::Type, from, interner) {
                PathRes::Done(Target::Module(next)) => m = next,
                _ => return None,
            }
        }
        let mut full: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        let mut items = Vec::new();
        for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
            crate::resolve::mdr::read(m);
            for &name in self.maps[m.0 as usize][ns_index(ns)].keys() {
                full.push(interner.get(name));
                if crate::resolve::stdpaths::std_has(&full).is_some() {
                    items.push((ns, name));
                }
                full.pop();
            }
        }
        items.sort_by(|a, b| (ns_index(a.0), interner.get(a.1)).cmp(&(ns_index(b.0), interner.get(b.1))));
        Some((m, items))
    }

    /// The std items lust knows by path that a glob of the std module
    /// `path` brings, with the namespaces an explicit import of each binds
    /// (`use std::mem::*;` brings `swap`, `use std::collections::*;`
    /// brings `HashSet` and the module `hash_map`), less the names its
    /// overlay module (`std_overlay_items`) defines. Macros stay with
    /// macro resolution.
    pub fn std_glob_alias_items(&self, path: &[Sym], overlay: Option<&(ModuleId, Vec<(Namespace, Sym)>)>, interner: &Interner) -> Vec<(Namespace, Sym)> {
        let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        // `use std::*;` (serde's `mod core { pub use std::*; }`): a crate
        // root's modules and items, as for any std module.
        if path.is_empty() || (path.len() == 1 && !matches!(strs[0], "std" | "core" | "alloc")) {
            return Vec::new();
        }
        let mut out = Vec::new();
        for item in crate::resolve::stdpaths::std_items(&strs) {
            let name = interner.intern(item);
            if overlay.is_some_and(|(_, items)| items.iter().any(|&(_, n)| n == name)) {
                continue;
            }
            let mut full = path.to_vec();
            full.push(name);
            for ns in std_import_namespaces(interner, &full).unwrap_or_default() {
                if ns != Namespace::Macro {
                    out.push((ns, name));
                }
            }
        }
        out
    }

    /// A `use` path written through a module's std alias, continued as
    /// the std path it stands for: `self::core::cell::Cell` where module
    /// `core` binds `cell` to `std::cell` (by `pub use std::cell;` or
    /// `pub use std::*;`) is `std::cell::Cell`. None when no segment
    /// after the first is a std alias visible from `from` (a real
    /// binding of the name wins), or when the path leaves the crate's
    /// own modules first.
    pub fn std_alias_continued(&self, from: ModuleId, path: &[Sym], leading_colon: bool, interner: &Interner) -> Option<Vec<Sym>> {
        for k in 1..path.len() {
            let PathRes::Done(Target::Module(m)) = self.resolve_module_path(from, &path[..k], leading_colon, interner) else {
                return None;
            };
            let last = k + 1 == path.len();
            let namespaces: &[Namespace] = if last { &[Namespace::Type, Namespace::Value, Namespace::Macro] } else { &[Namespace::Type] };
            if namespaces.iter().any(|&ns| self.lookup(m, ns, path[k]).is_some()) {
                continue;
            }
            let alias = namespaces
                .iter()
                .find_map(|&ns| {
                    let key = (m, ns_index(ns) as u8, path[k]);
                    self.std_aliases.get(&key).map(|(vis, p)| ((vis.clone(), p.clone()), self.std_glob_aliases.get(&key).copied().unwrap_or(m)))
                })
                .or_else(|| self.primitive_module_under_std_glob(m, path[k], interner));
            if let Some(((vis, std_path), def_module)) = alias {
                if !self.visible(&vis, def_module, from, interner) {
                    return None;
                }
                let mut full = std_path;
                full.extend_from_slice(&path[k + 1..]);
                return Some(full);
            }
            return None;
        }
        None
    }

    /// A std module named as a primitive type (`f32`) that a glob of a
    /// std crate root in module `m` brings (`pub use std::*;`). Such a
    /// glob binds no alias for it, so the name still reads as the type
    /// in `m`; a path through it (`self::core::f32`) still names the
    /// module. The glob's visibility and module, as for an alias.
    fn primitive_module_under_std_glob(&self, m: ModuleId, name: Sym, interner: &Interner) -> Option<((VisKind, Vec<Sym>), ModuleId)> {
        let n = interner.get(name);
        if !crate::ty::lang::is_primitive_type_name(n) {
            return None;
        }
        self.std_root_globs.iter().find_map(|(gm, vis, root)| {
            let strs = [interner.get(*root), n];
            (*gm == m && crate::resolve::stdpaths::std_has(&strs) == Some(crate::resolve::stdpaths::StdHas::Module))
                .then(|| ((vis.clone(), vec![*root, name]), m))
        })
    }

    /// The std source module a std path walks into at segment `seg`
    /// under std extern `i`, given the segment after it (`next`, read in
    /// `next_ns`): a whole module always, an overlay only when it
    /// defines `next` (other names stay the compiler's std items).
    pub fn std_module_walk(&self, i: u32, seg: Sym, next: Option<(Sym, Namespace)>, interner: &Interner) -> Option<ModuleId> {
        let (m, full) = self.std_module_at(i, seg, interner)?;
        if full {
            return Some(m);
        }
        let (n, ns) = next?;
        self.lookup(m, ns, n).is_some().then_some(m)
    }

    /// A deep std source module (`std::os::unix::net`): a row whose
    /// path has more than one segment, matched against the whole
    /// remaining path `segs`, so sibling paths under the same
    /// first segment (`std::os::unix::fs`) stay the compiler's.
    /// Returns the hidden module and how many segments it eats.
    /// An overlay row matches only when the segment after the deep
    /// path (when there is one) is defined in it.
    pub fn std_deep_module(&self, i: u32, segs: &[Sym], interner: &Interner) -> Option<(ModuleId, usize)> {
        let e = &self.externs[i as usize];
        if !e.is_std_lib || self.std_modules.is_empty() {
            return None;
        }
        for row in crate::stdmods::STD_MODULES {
            for (k, s) in row.paths {
                if *k != e.name || !s.contains("::") {
                    continue;
                }
                let parts: Vec<&str> = s.split("::").collect();
                if segs.len() < parts.len() || !parts.iter().zip(segs.iter()).all(|(p, g)| interner.get(*g) == *p) {
                    continue;
                }
                let m = self.std_modules.iter().find(|(n, _)| interner.get(*n) == row.name).map(|(_, m)| *m)?;
                if !row.full
                    && let Some(next) = segs.get(parts.len())
                    && ![Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| self.lookup(m, ns, *next).is_some())
                {
                    continue;
                }
                return Some((m, parts.len()));
            }
        }
        None
    }

    /// The root module of the dependency the extern prelude names
    /// `name` in `module`'s crate, when lust compiles it from source in
    /// this session (`extern_target`).
    pub fn source_extern_root(&self, module: ModuleId, name: Sym, interner: &Interner) -> Option<ModuleId> {
        let root = self.root_of(module);
        let n = interner.get(name);
        self.externs.iter().find(|e| e.owner == root && e.name == n).and_then(|e| e.root_module)
    }

    /// The path target an extern prelude entry resolves to: the
    /// dependency crate's root module when lust compiles it from
    /// source in this session, else the extern root itself.
    pub fn extern_target(&self, i: u32) -> Target {
        match self.externs[i as usize].root_module {
            Some(m) => Target::Module(m),
            None => Target::Extern(i),
        }
    }

    /// Looks up one first segment and checks visibility from `from`.
    /// Checks `from` itself, then the extern prelude, then the std
    /// prelude. Both modes read only `from`: as in rustc, items of a
    /// parent module are not in scope in a child (`mod a { use x::g; }`
    /// with `x` at the root is E0432), so a user `mod core` at the root
    /// does not shadow the `core` crate in any other module.
    fn first_segment(&self, from: ModuleId, name: Sym, ns: Namespace, _mode: PathMode, interner: &Interner) -> PathRes {
        match self.lookup(from, ns, name) {
            Some(BindState::Ambiguous) => return PathRes::Ambiguous,
            _ if self.order_dependent(from, ns, name, from, interner) => return PathRes::OrderDep,
            Some(BindState::One(b)) => {
                return if self.visible(&b.vis, b.def_module, from, interner) { PathRes::Done(b.target) } else { PathRes::Private };
            }
            None => {}
        }
        let name_str = interner.get(name);
        if let Some(i) = self.extern_in_scope(from, name_str) {
            return PathRes::Done(self.extern_target(i));
        }
        if !self.modules[from.0 as usize].no_prelude && in_std_prelude(name_str, ns) {
            return PathRes::Prelude;
        }
        PathRes::Absent
    }

    /// The binding one first segment has in module `from` alone
    /// (its map, its std aliases, then the extern prelude and the
    /// std prelude), with its glob rank. Import resolution in a fn
    /// body (`Rewrite::import_seg`) layers block frames over this;
    /// `run_imports` reads it for module-level imports. A glob
    /// binding of the module does not shadow a different prelude
    /// or extern-prelude item here: that pair is `Ambiguous`, as
    /// rustc reports for an import path through such a name.
    pub fn module_seg(&self, from: ModuleId, name: Sym, ns: Namespace, interner: &Interner) -> SegInfo {
        let name_str = interner.get(name);
        let own: Option<(SegBind, bool)> = match self.lookup(from, ns, name) {
            Some(BindState::Ambiguous) => return SegInfo { bind: SegBind::Ambiguous, glob: false },
            // An order-dependent glob name (L0509) is no safe answer
            // either; import paths report it as ambiguous.
            _ if self.order_dependent(from, ns, name, from, interner) => return SegInfo { bind: SegBind::Ambiguous, glob: false },
            Some(BindState::One(b)) if self.visible(&b.vis, b.def_module, from, interner) => {
                Some((SegBind::Target(b.target), b.rank <= 1))
            }
            _ => {
                let key = (from, ns_index(ns) as u8, name);
                self.std_aliases.get(&key).map(|(_, p)| (SegBind::Std(p.clone()), self.std_glob_aliases.contains_key(&key)))
            }
        };
        // The outer answers behind the module's own map. A
        // non-glob binding shadows both; a glob binding of a
        // different item is ambiguous with either.
        let outer: Option<SegBind> = if let Some(i) = self.extern_in_scope(from, name_str) {
            Some(SegBind::Extern(i))
        } else if !self.modules[from.0 as usize].no_prelude && in_std_prelude(name_str, ns) {
            Some(SegBind::Prelude(name))
        } else {
            None
        };
        match (own, outer) {
            (Some((bind, glob)), Some(out)) => {
                if glob && !self.same_seg(&bind, &out, interner) {
                    SegInfo { bind: SegBind::Ambiguous, glob: true }
                } else {
                    SegInfo { bind, glob }
                }
            }
            (Some((bind, glob)), None) => SegInfo { bind, glob },
            (None, Some(out)) => SegInfo { bind: out, glob: false },
            (None, None) => SegInfo { bind: SegBind::None, glob: false },
        }
    }

    /// True when two scopes' bindings name the same item, so a
    /// glob in one and any binding in the other are not ambiguous
    /// (the same item reached by two paths never is). An extern
    /// root equals its `Target` spellings; a std prelude item
    /// equals a std alias of its canonical path.
    pub fn same_seg(&self, a: &SegBind, b: &SegBind, interner: &Interner) -> bool {
        match (a, b) {
            (SegBind::Target(x), SegBind::Target(y)) => x == y,
            (SegBind::Std(x), SegBind::Std(y)) => same_std_item(x, y),
            (SegBind::Prelude(x), SegBind::Prelude(y)) => x == y,
            (SegBind::Extern(x), SegBind::Extern(y)) => x == y,
            (SegBind::Extern(i), SegBind::Target(t)) | (SegBind::Target(t), SegBind::Extern(i)) => {
                *t == Target::Extern(*i) || (*t == self.extern_target(*i))
            }
            (SegBind::Extern(i), SegBind::Std(p)) | (SegBind::Std(p), SegBind::Extern(i)) => {
                p.len() == 1 && interner.get(p[0]) == self.externs[*i as usize].name
            }
            (SegBind::Prelude(name), SegBind::Std(p)) | (SegBind::Std(p), SegBind::Prelude(name)) => {
                match prelude_std_suffix(interner.get(*name)) {
                    Some(suffix) => {
                        p.len() > 1 && p[1..].iter().map(|s| interner.get(*s)).collect::<Vec<_>>().as_slice() == suffix
                    }
                    None => false,
                }
            }
            _ => false,
        }
    }

    /// Resolves one segment inside a module target, with visibility.
    fn segment_in(&self, module: ModuleId, name: Sym, ns: Namespace, from: ModuleId, interner: &Interner) -> PathRes {
        match self.lookup(module, ns, name) {
            Some(BindState::Ambiguous) => PathRes::Ambiguous,
            _ if self.order_dependent(module, ns, name, from, interner) => PathRes::OrderDep,
            Some(BindState::One(b)) => {
                if self.visible(&b.vis, b.def_module, from, interner) {
                    PathRes::Done(b.target)
                } else {
                    PathRes::Private
                }
            }
            None => PathRes::Absent,
        }
    }

    /// Resolves a written path from module `from`. Segment names are
    /// already normalized by the caller: `crate`, `self`, and `super`
    /// arrive as those interned names. The walk consumes module
    /// segments in the type namespace and reads the last segment in
    /// `ns`; it stops at an Adt def (an associated item follows) or at
    /// an extern root.
    pub fn resolve_path(
        &self,
        from: ModuleId,
        segs: &[Sym],
        ns: Namespace,
        mode: PathMode,
        leading_colon: bool,
        interner: &Interner,
    ) -> PathRes {
        if segs.is_empty() {
            return PathRes::Absent;
        }
        let crate_sym = interner.intern("crate");
        let self_sym = interner.intern("self");
        let super_sym = interner.intern("super");
        let self_ty = interner.intern("Self");
        // `Self` in type position is a scope name, not a binding.
        if segs[0] == self_ty {
            return PathRes::Prelude;
        }
        let mut idx = 0usize;
        let cur: Target;
        if let Some(&root) = self.crate_magic.get(&segs[0]) {
            // A `$crate` magic segment from a cross-crate macro
            // expansion: the defining crate's root, direct dep or not.
            cur = Target::Module(root);
            idx = 1;
        } else if leading_colon {
            // `::dep::...`: extern prelude only.
            match self.extern_in_scope(from, interner.get(segs[0])) {
                Some(i) => cur = self.extern_target(i),
                None => return PathRes::Absent,
            }
            idx = 1;
        } else if segs[0] == crate_sym {
            cur = Target::Module(self.root_of(from));
            idx = 1;
        } else if segs[0] == self_sym {
            cur = Target::Module(from);
            idx = 1;
        } else if segs[0] == super_sym {
            let mut m = from;
            while idx < segs.len() && segs[idx] == super_sym {
                match self.modules[m.0 as usize].parent {
                    Some(p) => m = p,
                    None => return PathRes::Absent,
                }
                idx += 1;
            }
            cur = Target::Module(m);
        } else {
            match self.first_segment(from, segs[0], ns_or_type(segs, ns), mode, interner) {
                PathRes::Done(t) => cur = t,
                other => return other,
            }
            idx = 1;
        }
        if idx >= segs.len() {
            return PathRes::Done(cur);
        }
        match self.walk_from(from, cur, &segs[idx..], ns, interner) {
            PathRes::Partial(t, rest) => PathRes::Partial(t, idx + rest),
            other => other,
        }
    }

    /// Continues a path walk from an already-resolved target over the
    /// remaining segments. The rewrite pass uses it for paths whose
    /// first segment came from a lexical (function-local) import.
    pub fn walk_from(&self, from: ModuleId, start: Target, segs: &[Sym], ns: Namespace, interner: &Interner) -> PathRes {
        let mut cur = start;
        let mut idx = 0usize;
        if segs.is_empty() {
            return PathRes::Done(cur);
        }
        loop {
            let seg = segs[idx];
            let last = idx + 1 == segs.len();
            let seg_ns = if last { ns } else { Namespace::Type };
            match cur {
                Target::Module(m) => match self.segment_in(m, seg, seg_ns, from, interner) {
                    PathRes::Done(t) => cur = t,
                    other => return other,
                },
                // `std::io::Write` and friends: the item lives in the
                // shipped platform crate (W-SHIM), so walk its tree.
                Target::Extern(i)
                    if self.externs[i as usize].is_std_lib
                        && self.externs[i as usize].name == "std"
                        && self.std_platform_has(&segs[idx..], from, interner) =>
                {
                    cur = Target::Module(self.std_platform.map(|(root, _)| root).unwrap_or(ModuleId(0)));
                    continue;
                }
                // Deep std source modules (`std::os::unix::net`) eat
                // their whole remaining path at the extern (W-CINTEROP2).
                Target::Extern(i)
                    if seg_ns == Namespace::Type
                        && let Some((m, eaten)) = self.std_deep_module(i, &segs[idx..], interner) =>
                {
                    cur = Target::Module(m);
                    idx += eaten;
                    if idx >= segs.len() {
                        return PathRes::Done(cur);
                    }
                    continue;
                }
                // `std::time` and the other std source modules walk into
                // their hidden module (W-STD-C).
                Target::Extern(i)
                    if seg_ns == Namespace::Type
                        && let Some(m) = self.std_module_walk(
                            i,
                            seg,
                            segs.get(idx + 1).map(|&n| (n, if idx + 2 == segs.len() { ns } else { Namespace::Type })),
                            interner,
                        ) =>
                {
                    cur = Target::Module(m);
                }
                Target::Def(_) | Target::Extern(_) | Target::Variant(..) => return PathRes::Partial(cur, idx),
            }
            idx += 1;
            if idx >= segs.len() {
                return PathRes::Done(cur);
            }
        }
    }

    /// Resolves the module part of a `use` path (all of it for a glob,
    /// all but the last segment for a single import). Returns the module
    /// or extern it names.
    pub fn resolve_module_path(&self, from: ModuleId, segs: &[Sym], leading_colon: bool, interner: &Interner) -> PathRes {
        if segs.is_empty() {
            return PathRes::Done(Target::Module(from));
        }
        match self.resolve_path(from, segs, Namespace::Type, PathMode::Use, leading_colon, interner) {
            PathRes::Done(t @ (Target::Module(_) | Target::Extern(_))) => PathRes::Done(t),
            // An extern root with more segments behind it is still the
            // extern: `std::cmp` as a module part resolves as extern.
            PathRes::Partial(Target::Extern(i), _) => PathRes::Done(Target::Extern(i)),
            PathRes::Done(_) => PathRes::Absent,
            other => other,
        }
    }
}

/// The namespace a path's first segment reads in: the type namespace
/// when more segments follow (it must name a module or a type), the
/// asked namespace for a one-segment path.
fn ns_or_type(segs: &[Sym], ns: Namespace) -> Namespace {
    if segs.len() > 1 { Namespace::Type } else { ns }
}

// ---------- The import fixpoint ----------

/// One flattened import from a `use` tree.
#[derive(Clone, Debug)]
pub struct Import {
    pub module: ModuleId,
    pub vis: VisKind,
    pub leading_colon: bool,
    pub span: Span,
    pub kind: ImportKind,
}

#[derive(Clone, Debug)]
pub enum ImportKind {
    /// `use a::b::Name;` or `use a::b::Name as Other;`. `name` is the
    /// binding name in the importing module.
    Single { path: Vec<Sym>, name: Sym },
    /// `use a::b::*;`.
    Glob { path: Vec<Sym> },
    /// The prefix of an empty group (`use a::b::{};`): it binds
    /// nothing, but rustc still resolves the prefix and rejects a bad
    /// one, so the path is checked and only that.
    CheckPath { path: Vec<Sym> },
    /// A leading `::` that is not in start position (`use a::{::b};`).
    /// The fixpoint reports it once and settles.
    BadLeading { path: Vec<Sym> },
}

/// Flattens one `use` tree into imports. Groups distribute their
/// prefix; `self` in a group is a prefix segment like any other here
/// (the import resolution reads a trailing `self` as the module).
pub fn flatten_use(tree: &ast::UseTree, module: ModuleId, vis: VisKind, out: &mut Vec<Import>, interner: &Interner) {
    fn walk(
        tree: &ast::UseTree,
        prefix: &mut Vec<Sym>,
        module: ModuleId,
        vis: &VisKind,
        leading: bool,
        out: &mut Vec<Import>,
        interner: &Interner,
    ) {
        let saved = prefix.len();
        prefix.extend(tree.prefix.iter().map(|s| s.name));
        // A leading `::` is the crate root and belongs in start
        // position only: `use {::std::..}` is a start, `use a::{::b}`
        // is an error (rustc E0433).
        if tree.leading_colon && saved > 0 {
            out.push(Import {
                module,
                vis: vis.clone(),
                leading_colon: true,
                span: tree.span,
                kind: ImportKind::BadLeading { path: prefix.clone() },
            });
            prefix.truncate(saved);
            return;
        }
        let leading = leading || tree.leading_colon;
        match &tree.kind {
            ast::UseKind::Simple { rename } => {
                if let Some(last) = prefix.last().copied() {
                    let name = rename.unwrap_or(last);
                    // `use a::self;` binds the module under its own name
                    // (or the rename); keep the path whole and let the
                    // resolver read the trailing `self`.
                    let _ = interner;
                    out.push(Import {
                        module,
                        vis: vis.clone(),
                        leading_colon: leading,
                        span: tree.span,
                        kind: ImportKind::Single { path: prefix.clone(), name },
                    });
                }
            }
            ast::UseKind::Glob => {
                out.push(Import {
                    module,
                    vis: vis.clone(),
                    leading_colon: leading,
                    span: tree.span,
                    kind: ImportKind::Glob { path: prefix.clone() },
                });
            }
            ast::UseKind::Group(children) => {
                if children.is_empty() {
                    out.push(Import {
                        module,
                        vis: vis.clone(),
                        leading_colon: leading,
                        span: tree.span,
                        kind: ImportKind::CheckPath { path: prefix.clone() },
                    });
                }
                for c in children {
                    walk(c, prefix, module, vis, leading, out, interner);
                }
            }
        }
        prefix.truncate(saved);
    }
    walk(tree, &mut Vec::new(), module, &vis, tree.leading_colon, out, interner);
}

/// Runs the import fixpoint of section 1.3 over the tables. Explicit
/// imports and globs are retried together until a full sweep changes
/// nothing. Returns diagnostics for imports that never resolved and for
/// duplicate explicit imports. An import through an extern crate root
/// (`use std::...`, `use dep::Name`) makes no local binding here: the
/// rewrite pass leaves those paths to the std compat layer, and binding
/// queries for them answer through the extern flat record the worklist
/// adds.
pub fn run_imports(tables: &mut ResolvedTables, imports: &[Import], interner: &Interner) -> Result<Vec<Diag>, String> {
    let self_sym = interner.intern("self");
    let mut diags = Vec::new();
    let mut pending: Vec<(usize, &Import)> = imports.iter().enumerate().collect();
    let mut resolved = vec![false; imports.len()];
    tables.pending_single.clear();
    tables.ambig_single.clear();
    tables.single_binds.clear();
    tables.order_dep.clear();
    tables.import_stall = false;
    for imp in imports {
        if let ImportKind::Single { name, path } = &imp.kind
            && let Some((&last, mod_path)) = path.split_last()
        {
            let p = PendingSingle { span: imp.span, vis: imp.vis.clone(), mod_path: mod_path.to_vec(), leading_colon: imp.leading_colon, last };
            tables.pending_single.entry((imp.module, *name)).or_default().push(p);
        }
    }
    let cap = tables.modules.len() + 2;
    let mut rounds = 0;
    let mut stall_sweep = false;
    // Per module glob import: its source module and the lengths of the
    // source's and the importer's `glob_log` right after its last copy.
    // A later sweep copies only the names logged since then: a name no
    // one changed would copy the same way again. A crate with 1,700
    // globs paid a full copy of each per sweep (5 sweeps at 166k lines).
    // LUST_CHECK_GLOB_SKIP=1 runs the full copy after each short one and
    // panics if it changes anything (tests of this rule).
    let mut last_copy: Vec<Option<(ModuleId, usize, usize)>> = vec![None; imports.len()];
    let check_skip = std::env::var_os("LUST_CHECK_GLOB_SKIP").is_some();
    loop {
        rounds += 1;
        if rounds > cap + imports.len() {
            return Err("internal: import worklist did not settle".to_string());
        }
        let mut changed = false;
        let mut still: Vec<(usize, &Import)> = Vec::new();
        for (i, imp) in pending.drain(..) {
            // The stall sweep retries only single imports: nothing
            // changed since the last sweep, so no glob copies more.
            if stall_sweep && matches!(imp.kind, ImportKind::Glob { .. }) {
                still.push((i, imp));
                continue;
            }
            let src = glob_source(tables, imp, interner);
            if let (Some(src), Some((was, ls, lm))) = (src, last_copy[i])
                && src == was
            {
                // In log order, repeats and all: a repeat copies again as an unchanged name,
                // which costs less than sorting every list (a tenth of the import worklist).
                let mut names: Vec<Sym> = tables.glob_log.get(src.0 as usize).map_or(&[][..], |l| &l[ls..]).to_vec();
                names.extend_from_slice(tables.glob_log.get(imp.module.0 as usize).map_or(&[][..], |l| &l[lm..]));
                if !names.is_empty() {
                    changed |= copy_glob(tables, imp, src, Some(&names), interner);
                }
                if check_skip {
                    let n = diags.len();
                    let again = try_import(tables, imp, self_sym, interner, &mut diags);
                    assert!(
                        matches!(again, TryOut::Stay { changed: false, .. }) && diags.len() == n,
                        "internal: a short glob copy missed a change"
                    );
                }
                last_copy[i] = Some((src, tables.log_len(src), tables.log_len(imp.module)));
                still.push((i, imp));
                continue;
            }
            let out = try_import(tables, imp, self_sym, interner, &mut diags);
            last_copy[i] = match (&out, src) {
                (TryOut::Stay { .. }, Some(src)) => Some((src, tables.log_len(src), tables.log_len(imp.module))),
                _ => None,
            };
            match out {
                TryOut::Done(did_change) => {
                    changed |= did_change;
                    resolved[i] = true;
                    if let ImportKind::Single { name, .. } = &imp.kind {
                        settle_single(tables, imp.module, *name, imp.span);
                        // A glob binding this import hid can now reach
                        // glob importers: another sweep runs.
                        changed |= glob_bound(tables, imp.module, *name);
                    }
                }
                TryOut::Stay { changed: c, resolved: r } => {
                    changed |= c;
                    resolved[i] |= r;
                    still.push((i, imp));
                }
                TryOut::Wait => still.push((i, imp)),
            }
        }
        pending = still;
        stall_sweep = false;
        if !pending.is_empty() && !changed && !tables.import_stall {
            tables.import_stall = true;
            stall_sweep = true;
            continue;
        }
        if pending.is_empty() || !changed {
            break;
        }
    }
    tables.pending_single.clear();
    crate::resolve::order::compute_order_dep(tables, imports, interner);
    // The plain checks first: where they report (L0507, L0510), rustc
    // does too; the order rule (L0509) takes the imports they pass.
    let mut seen = report_ambig_single(tables, interner, &mut diags);
    seen.extend(finalize_singles(tables, interner, &mut diags));
    crate::resolve::order::report_order_imports(tables, imports, interner, &mut diags, &seen);
    for (i, imp) in &pending {
        if resolved[*i] {
            continue;
        }
        let (path, glob) = match &imp.kind {
            ImportKind::Single { path, .. } | ImportKind::CheckPath { path } | ImportKind::BadLeading { path } => (path, false),
            ImportKind::Glob { path } => (path, true),
        };
        let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        // A std path the shipped std source or platform crate lacks
        // (`std::os::unix::fs::OpenOptionsExt`) exists in std all the same.
        if matches!(strs.first(), Some(&("std" | "core" | "alloc")))
            && (imp.leading_colon || tables.std_root_is_extern(imp.module, path[0], interner))
            && crate::resolve::stdpaths::std_has(&strs).is_some()
        {
            diags.push(std_missing_diag(&strs, glob, imp.span));
            continue;
        }
        let what = strs.join("::");
        diags.push(Diag::new(
            "L0506",
            imp.span,
            format!("unresolved import `{what}`"),
            "Check the path: every segment must name a module or item that is visible here.",
        ));
    }
    // Import resolution does not let a glob binding of this module
    // shadow a different std-prelude or extern-prelude item of the
    // same name (rustc E0659, e.g. a glob that brings a user `std`
    // or `Option` next to `use std::vec::Vec;` or `use Option::*;`
    // in the same module), where an ordinary path picks the glob
    // binding. `module_seg` already folds that pair to Ambiguous.
    // The glob's own path counts too: a glob whose first segment
    // it rebinds from the prelude side is the same error. One
    // diagnostic per (use item, name).
    {
        let mut seen: FxMap<(crate::diag::Span, Sym), ()> = FxMap::default();
        for imp in imports {
            if imp.leading_colon {
                continue;
            }
            let path = match &imp.kind {
                ImportKind::Single { path, .. } | ImportKind::CheckPath { path } | ImportKind::Glob { path } => path,
                ImportKind::BadLeading { .. } => continue,
            };
            let Some(&first) = path.first() else { continue };
            if matches!(interner.get(first), "crate" | "self" | "super" | "Self") || tables.crate_magic.contains_key(&first) {
                continue;
            }
            let nss: &[Namespace] = if path.len() == 1 && matches!(imp.kind, ImportKind::Single { .. }) {
                &[Namespace::Type, Namespace::Value, Namespace::Macro]
            } else {
                &[Namespace::Type]
            };
            for &ns in nss {
                let info = tables.module_seg(imp.module, first, ns, interner);
                // Only the glob-vs-prelude pair: plain Ambiguous
                // (two globs of the module) already errors where
                // the import binds or stays unresolved.
                if info.glob && matches!(info.bind, SegBind::Ambiguous) && seen.insert((imp.span, first), ()).is_none() {
                    diags.push(ambiguous_diag(interner.get(first), imp.span));
                }
            }
        }
    }
    Ok(diags)
}

/// The (name, binding) pairs of module `src`'s namespace `ns`, in its map's order, or
/// `only`'s names in their order when given (`copy_glob`).
fn glob_names<'t>(tables: &'t ResolvedTables, src: ModuleId, ns: Namespace, only: Option<&'t [Sym]>) -> impl Iterator<Item = (Sym, &'t BindState)> + 't {
    let map = &tables.maps[src.0 as usize][ns_index(ns)];
    let all = only.is_none().then(|| map.iter().map(|(n, b)| (*n, b)));
    let some = only.map(|o| o.iter().filter_map(move |n| map.get(n).map(|b| (*n, b))));
    all.into_iter().flatten().chain(some.into_iter().flatten())
}

/// Copies the names of module `src` that importer `imp.module` can
/// see into it (a module glob, `use src::*`): bindings, ambiguous
/// names, and std aliases. `only` limits the copy to those names, in any
/// order and with repeats (`run_imports` passes the names changed since
/// the last copy). Each name's copy reads and writes that name alone, so
/// the names go in the source map's order, or `only`'s. Returns true on a
/// change.
fn copy_glob(tables: &mut ResolvedTables, imp: &Import, src: ModuleId, only: Option<&[Sym]>, interner: &Interner) -> bool {
    let mut changed = false;
    let mut entries: Vec<(Namespace, Sym, Bind)> = Vec::new();
    // The source's ambiguous names per namespace, read in the same pass: the copies write
    // the importer only, so the source's states stand as read.
    let mut ambiguous: [Vec<Sym>; 3] = Default::default();
    for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
        for (name, state) in glob_names(tables, src, ns, only) {
            // A `macro_rules!` definition is not in its
            // module's namespace, so no glob copies it.
            // A glob binding a pending single import of
            // the name hides is not copied yet.
            match state {
                BindState::One(b)
                    if (b.rank >= 2 || !tables.pending_single.contains_key(&(src, name)))
                        && tables.visible(&b.vis, b.def_module, imp.module, interner)
                        && !(ns == Namespace::Macro && tables.is_textual_bind(src, name, b)) =>
                {
                    let (vis, def_module) = tables.glob_vis(imp, &b.vis, b.def_module, interner);
                    entries.push((ns, name, Bind { target: b.target, vis, rank: 1, def_module }));
                }
                BindState::Ambiguous => ambiguous[ns_index(ns)].push(name),
                BindState::One(_) => {}
            }
        }
    }
    // The importer's first glob copy (most of the millions of names copied on tsgo): with no
    // glob source and no std alias in the module yet (each std glob alias is a std alias too),
    // a name it does not hold takes the copy as `insert_glob` would, in one table probe.
    let m = imp.module;
    let first = tables.glob_src.none_in(m) && tables.std_aliases.range((m, 0, Sym(0))..=(m, u8::MAX, Sym(u32::MAX))).next().is_none();
    // A full copy brings a source's whole namespace at once (a prelude: thousands of names):
    // the importer's maps get room for the names they lack in one step, where growing by
    // doubling rehashed them again and again (a quarter of the copy's time on tsgo). A first
    // copy meets only the importer's own names (a few), so it counts every name.
    if only.is_none() {
        let mut new = [0usize; 3];
        for (ns, name, _) in &entries {
            let i = ns_index(*ns);
            new[i] += usize::from(first || !tables.maps[m.0 as usize][i].contains_key(name));
        }
        for (i, &n) in new.iter().enumerate() {
            tables.maps[m.0 as usize][i].reserve(n);
        }
        tables.glob_src.reserve(m, new.iter().sum());
    }
    for (ns, name, bind) in entries {
        let took = first
            && match tables.maps[m.0 as usize][ns_index(ns)].entry(name) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(BindState::One(bind.clone()));
                    true
                }
                std::collections::hash_map::Entry::Occupied(_) => false,
            };
        if took {
            tables.touch(m, name);
            tables.glob_src.insert((m, ns_index(ns) as u8, name), src);
            changed = true;
        } else if tables.insert_glob(m, ns, name, bind, src) == InsertOut::Changed {
            changed = true;
        }
    }
    // An ambiguous name in the source is ambiguous
    // through this glob too, as in rustc: copying
    // only its settled names would leave a stale
    // binding from an earlier sweep, or let another
    // glob's item win silently. The source records
    // itself in `glob_src`, so its own later
    // settling (an explicit import there) can undo
    // exactly this poisoning (`insert_glob`). Only
    // an ambiguity this importer can see crosses
    // (`ambig_vis`), and none that a pending single
    // import in the source hides.
    for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
        let mut names = std::mem::take(&mut ambiguous[ns_index(ns)]);
        // A glob of the importer itself (only a std overlay's could be) wrote the source: its
        // ambiguous names are read again, after the copies.
        if src == imp.module {
            names = glob_names(tables, src, ns, only).filter_map(|(name, state)| matches!(state, BindState::Ambiguous).then_some(name)).collect();
        }
        names.retain(|name| !tables.pending_single.contains_key(&(src, *name)) && tables.ambiguous_visible(src, ns, *name, imp.module, interner));
        for name in names {
            let certain = tables.ambiguous_certain(src, ns, name, Some(imp.module), interner);
            let item = AmbItem::Amb { certain };
            let vis = match tables.ambig_vis.get(&(src, ns_index(ns) as u8, name)) {
                Some(list) => list
                    .iter()
                    .filter(|(v, m, _)| tables.visible(v, *m, imp.module, interner))
                    .map(|(v, m, _)| {
                        let (v, m) = tables.glob_vis(imp, v, *m, interner);
                        (v, m, item.clone())
                    })
                    .collect(),
                None => vec![(imp.vis.clone(), imp.module, item)],
            };
            if insert_ambiguous(tables, imp.module, ns, name, vis) {
                tables.glob_src.insert((imp.module, ns_index(ns) as u8, name), src);
                tables.touch(imp.module, name);
                changed = true;
            }
        }
    }
    // The std imports of the source module
    // (`pub use std::rc::Rc;`) bind like its other names. `only` is sorted
    // for them (a few sources have std aliases).
    let aliases = tables.visible_std_aliases(src, imp.module, interner);
    let only_sorted: Option<Vec<Sym>> = only.filter(|_| !aliases.is_empty()).map(|o| {
        let mut v = o.to_vec();
        v.sort_unstable();
        v
    });
    for (ns, name, vis, def_module, path) in aliases {
        if only_sorted.as_ref().is_some_and(|o| o.binary_search(&name).is_err())
            || (tables.pending_single.contains_key(&(src, name)) && tables.std_glob_aliases.contains_key(&(src, ns, name)))
        {
            continue;
        }
        let (vis, def_module) = tables.glob_vis(imp, &vis, def_module, interner);
        let ns = [Namespace::Type, Namespace::Value, Namespace::Macro][ns as usize];
        changed |= tables.insert_glob_std_alias(imp.module, ns, name, vis, def_module, path);
    }
    changed
}

/// The module a glob import copies from, as `try_import` resolves it
/// now, or None when it is no module glob (an enum's variants, a std or
/// extern path, an unresolved or private path, or the module itself).
fn glob_source(tables: &ResolvedTables, imp: &Import, interner: &Interner) -> Option<ModuleId> {
    let ImportKind::Glob { path } = &imp.kind else { return None };
    if path.is_empty() {
        return None;
    }
    if let PathRes::Done(Target::Def(adt)) = tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner)
        && tables.variants.contains_key(&adt)
    {
        return None;
    }
    match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
        PathRes::Done(Target::Module(src)) if src != imp.module => Some(src),
        _ => None,
    }
}

enum TryOut {
    Done(bool),
    /// Keep this import for the next sweep (a live glob).
    Stay {
        changed: bool,
        resolved: bool,
    },
    Wait,
}

/// The namespaces an explicit import of a canonical std path
/// binds, or None when the path is not a std item (or module)
/// lust knows by full path. `std::vec` is both a module (type
/// namespace) and a macro (macro namespace), so it binds in both.
pub fn std_import_namespaces(interner: &Interner, path: &[Sym]) -> Option<Vec<Namespace>> {
    use crate::ty::lang::{StdPathKind, std_is_module_path, std_path_kind};
    let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
    let mut out = match std_path_kind(&strs) {
        Some(StdPathKind::Type | StdPathKind::Trait) => vec![Namespace::Type],
        Some(StdPathKind::Fn | StdPathKind::Variant) => vec![Namespace::Value],
        Some(StdPathKind::Macro) => vec![Namespace::Macro],
        None if std_is_module_path(&strs) => vec![Namespace::Type],
        // A std platform module (W-SHIM): its items resolve through the
        // alias into the platform crate.
        None if strs.len() == 2 && strs[0] == "std" && STD_PLATFORM_MODULES.contains(&strs[1]) => vec![Namespace::Type],
        // Any other std module (`std::net`, a source overlay): the alias
        // lets a path through it go on (`std_alias_continued`). A module
        // named as a primitive type (`std::f32`) binds nothing, so the
        // name still reads as the type.
        None if crate::resolve::stdpaths::std_has(&strs) == Some(crate::resolve::stdpaths::StdHas::Module)
            && !strs.last().is_some_and(|l| crate::ty::lang::is_primitive_type_name(l)) =>
        {
            vec![Namespace::Type]
        }
        None => return None,
    };
    if std_is_module_path(&strs) && !out.contains(&Namespace::Type) {
        out.push(Namespace::Type);
    }
    Some(out)
}

/// The reject for a std import (`glob`: a glob) that binds nothing in
/// lust's std tables, or None when std 1.99 has the path (a module or
/// enum for a glob). An import of a real std item lust does not model
/// stays accepted: it is valid Rust, and a use of the name still
/// rejects where lust lacks it (ts-rust imports `std::alloc::Layout`).
/// Module-level and fn-body imports both call it.
pub fn std_unbound_diag(path: &[Sym], glob: bool, span: Span, interner: &Interner) -> Option<Diag> {
    use crate::resolve::stdpaths::{StdHas, std_has};
    use crate::ty::lang::{std_enum_variants, std_is_module_path};
    let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
    if glob && (std_is_module_path(&strs) || !std_enum_variants(&strs).is_empty()) {
        return None;
    }
    match std_has(&strs) {
        Some(StdHas::Module | StdHas::Enum) => None,
        Some(_) if !glob => None,
        _ => Some(std_missing_diag(&strs, glob, span)),
    }
}

/// The reject for a std path as the parent of an empty group or of
/// `{self}` (`use std::x::{};`, `use std::cmp::Ord::{self};`): std must
/// have a module, enum, or trait there (rustc E0432 otherwise).
pub fn std_group_parent_diag(path: &[Sym], span: Span, interner: &Interner) -> Option<Diag> {
    use crate::resolve::stdpaths::{StdHas, std_has};
    let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
    if matches!(std_has(&strs), Some(StdHas::Module | StdHas::Enum | StdHas::Trait)) {
        return None;
    }
    std_unbound_diag(path, true, span, interner)
}

/// The reject for a std import path lust has no binding for: L0505
/// when std 1.99 has the path (an item a shipped platform module
/// lacks), L0506 when it does not (rustc E0432; an unused import of a
/// missing path is an error in rustc too). With `glob`, the path must
/// be a module or an enum.
fn std_missing_diag(path: &[&str], glob: bool, span: Span) -> Diag {
    use crate::resolve::stdpaths::{StdHas, std_has};
    let full = path.join("::");
    match std_has(path) {
        Some(StdHas::Item | StdHas::Trait) if glob => {
            Diag::new("L0506", span, format!("unresolved import `{full}`: not a module or enum"), "A glob import needs a module or an enum.")
        }
        Some(_) => Diag::new(
            "L0505",
            span,
            format!("std path `{full}` is not supported yet"),
            "lust does not ship this std item yet: build with Cargo, or use a std item lust supports (see README).",
        ),
        None => Diag::new("L0506", span, format!("unresolved import `{full}`"), "std 1.99 has no such item: check the path."),
    }
}

/// Records one std import alias in the tables, with the same
/// duplicate rules as a local explicit import: a name already
/// bound explicitly in the module (a local item, an earlier
/// import, or an earlier std alias) reports `dup_diag` and the
/// first binding keeps the name. `as _` binds no usable name: it is
/// stored under a synthetic name keyed by the path (never a
/// duplicate), so a std trait imported that way is in scope for its
/// methods (`use std::fmt::Write as _;` for `write!` into a String).
fn record_std_alias(tables: &mut ResolvedTables, imp: &Import, path: &[Sym], name: Sym, interner: &Interner, diags: &mut Vec<Diag>) -> bool {
    let Some(namespaces) = std_import_namespaces(interner, path) else {
        diags.extend(std_unbound_diag(path, false, imp.span, interner));
        return false;
    };
    let anon = interner.get(name) == "_";
    let name = if anon {
        let full: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        interner.intern(&format!("$lust$anon$std${}", full.join("::")))
    } else {
        name
    };
    let mut dup = false;
    let mut inserted = false;
    for ns in namespaces {
        let key = (imp.module, ns_index(ns) as u8, name);
        if anon && tables.std_aliases.contains_key(&key) {
            continue;
        }
        if explicit_exists(tables, imp, ns, name) || tables.explicit_std_alias(key) {
            dup = true;
            continue;
        }
        // An explicit alias replaces a glob one of the same name.
        tables.std_glob_aliases.remove(&key);
        tables.std_aliases.insert(key, (imp.vis.clone(), path.to_vec()));
        tables.touch(imp.module, name);
        inserted = true;
    }
    if dup {
        diags.push(dup_diag(imp, name, interner));
    }
    inserted
}

/// Tries one import against the current tables.
fn try_import(tables: &mut ResolvedTables, imp: &Import, self_sym: Sym, interner: &Interner, diags: &mut Vec<Diag>) -> TryOut {
    // `use std::io::Write;`: an item of the shipped platform crate
    // (W-SHIM) imports from that crate's module tree.
    if let ImportKind::Single { path, name } = &imp.kind
        && tables.std_platform.is_some()
        && let Some(redirected) = tables.std_platform_path(path, imp.module, interner)
        && (imp.leading_colon || tables.std_is_extern(imp.module, interner))
    {
        let imp2 = Import { kind: ImportKind::Single { path: redirected, name: *name }, leading_colon: false, ..imp.clone() };
        return try_import(tables, &imp2, self_sym, interner, diags);
    }
    // `use self::core::cell::Cell;` where module `core` has `pub use
    // std::*;` (or `pub use std::cell;`): the path goes on through the
    // std alias, as `use std::cell::Cell;` (serde's `crate::lib`).
    let redirect = |path: &[Sym]| tables.std_alias_continued(imp.module, path, imp.leading_colon, interner);
    let kind = match &imp.kind {
        ImportKind::Single { path, name } => redirect(path).map(|path| ImportKind::Single { path, name: *name }),
        ImportKind::Glob { path } => redirect(path).map(|path| ImportKind::Glob { path }),
        ImportKind::CheckPath { path } => redirect(path).map(|path| ImportKind::CheckPath { path }),
        ImportKind::BadLeading { .. } => None,
    };
    if let Some(kind) = kind {
        let imp2 = Import { kind, leading_colon: true, ..imp.clone() };
        return try_import(tables, &imp2, self_sym, interner, diags);
    }
    match &imp.kind {
        ImportKind::BadLeading { .. } => {
            diags.push(Diag::new(
                "L0506",
                imp.span,
                "the crate root in a `use` path can only be used in start position",
                "Move the leading `::` to the start of the whole import, or remove it.",
            ));
            TryOut::Done(false)
        }
        ImportKind::CheckPath { path } => {
            // An empty group binds nothing, but its prefix must still
            // name a module (or an enum, like a glob prefix).
            if path.is_empty() {
                return TryOut::Done(false);
            }
            match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                // `use std::nosuch::{};` still names a module.
                PathRes::Done(Target::Extern(i)) if tables.externs[i as usize].is_std_lib => {
                    diags.extend(std_group_parent_diag(path, imp.span, interner));
                    TryOut::Done(false)
                }
                PathRes::Done(_) => TryOut::Done(false),
                PathRes::Private => {
                    diags.push(private_diag("that module", imp.span));
                    TryOut::Done(false)
                }
                _ => match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                    PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => TryOut::Done(false),
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                },
            }
        }
        ImportKind::Glob { path } => {
            if path.is_empty() {
                // `use *;` and `use ::*;` name no module at all.
                diags.push(Diag::new(
                    "L0506",
                    imp.span,
                    "cannot glob-import all possible crates",
                    "Name the module before the `*`, such as `use a::*;`.",
                ));
                return TryOut::Done(false);
            }
            match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                // `use a::E::*` imports the enum's variants.
                PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => {
                    let mut changed = false;
                    // Variants take the enum's visibility.
                    let (vis, def_module) = match tables.def_info.get(&adt) {
                        Some(info) => tables.glob_vis(imp, &info.vis, info.module, interner),
                        None => (imp.vis.clone(), imp.module),
                    };
                    for v in tables.variants[&adt].clone() {
                        // Variants bind in both namespaces (rustc): a
                        // glob of another module that brings a type
                        // of the variant's name makes a path head
                        // ambiguous, not silently the type's.
                        for ns in [Namespace::Value, Namespace::Type] {
                            let bind = Bind { target: Target::Variant(adt, v), vis: vis.clone(), rank: 1, def_module };
                            if tables.insert(imp.module, ns, v, bind) == InsertOut::Changed {
                                changed = true;
                            }
                        }
                    }
                    TryOut::Done(changed)
                }
                _ => match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                    PathRes::Done(Target::Module(src)) => {
                        if src == imp.module {
                            // `use self::*;` (or a longer path back to
                            // this module): rustc E0432.
                            diags.push(Diag::new(
                                "L0506",
                                imp.span,
                                "cannot glob-import a module into itself",
                                "Remove the import: the module's own items are already in scope.",
                            ));
                            return TryOut::Done(false);
                        }
                        let changed = copy_glob(tables, imp, src, None, interner);
                        // A glob stays live: new names in the source module can
                        // appear as other imports settle. It stays pending until
                        // a no-change sweep; the caller drops a resolved glob
                        // without error at the end.
                        TryOut::Stay { changed, resolved: true }
                    }
                    PathRes::Done(Target::Extern(i)) => {
                        if let Some(why) = &tables.externs[i as usize].unsupported {
                            diags.push(unsupported_diag(why, imp.span));
                            return TryOut::Done(false);
                        }
                        // `use std::cmp::Ordering::*;`: the std enum's
                        // variants bind as std aliases (value namespace),
                        // below any binding the module already has.
                        let mut changed = false;
                        if tables.externs[i as usize].is_std_lib {
                            let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                            // A glob binds nothing here, so a module or
                            // enum lust does not know (or a missing path)
                            // would import silently.
                            if let Some(d) = std_unbound_diag(path, true, imp.span, interner) {
                                diags.push(d);
                                return TryOut::Done(false);
                            }
                            for v in crate::ty::lang::std_enum_variants(&strs) {
                                let name = interner.intern(v);
                                let mut full = path.clone();
                                full.push(name);
                                // Both namespaces, like a user enum's variants.
                                changed |= tables.insert_glob_std_alias(imp.module, Namespace::Value, name, imp.vis.clone(), imp.module, full.clone());
                                changed |= tables.insert_glob_std_alias(imp.module, Namespace::Type, name, imp.vis.clone(), imp.module, full);
                            }
                            // `use std::panic::*;`: the items of the std
                            // source overlay module (AssertUnwindSafe) or of
                            // the platform crate's module (`std::io::*`
                            // brings io's own `Result`), then the std items
                            // lust knows by path (catch_unwind, mem::swap,
                            // HashSet) bind at glob rank, as their explicit
                            // imports would.
                            let overlay = tables.std_overlay_items(i, path, interner).or_else(|| tables.std_platform_glob_items(path, imp.module, interner));
                            if let Some((m, items)) = &overlay {
                                let mut only: Vec<Sym> = items.iter().map(|&(_, n)| n).collect();
                                only.sort();
                                only.dedup();
                                changed |= copy_glob(tables, imp, *m, Some(&only), interner);
                            }
                            if path.len() == 1 && !tables.std_root_globs.iter().any(|(m, _, r)| *m == imp.module && *r == path[0]) {
                                tables.std_root_globs.push((imp.module, imp.vis.clone(), path[0]));
                            }
                            for (ns, name) in tables.std_glob_alias_items(path, overlay.as_ref(), interner) {
                                let mut full = path.clone();
                                full.push(name);
                                changed |= tables.insert_glob_std_alias(imp.module, ns, name, imp.vis.clone(), imp.module, full);
                            }
                            if overlay.is_some() {
                                return TryOut::Stay { changed, resolved: true };
                            }
                        }
                        TryOut::Done(changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                },
            }
        }
        ImportKind::Single { path, name } => {
            // `use a::E::V` imports one enum variant.
            if let PathRes::Partial(Target::Def(adt), rest) =
                tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner)
                && rest + 1 == path.len()
                && tables.variants.get(&adt).is_some_and(|vs| vs.contains(&path[rest]))
            {
                if !tables.check_reexport(imp, Target::Variant(adt, path[rest]), interner.get(path[rest]), interner, diags) {
                    return TryOut::Done(false);
                }
                // Both namespaces, as a glob of the enum binds them.
                let bind_name = import_bind_name(*name, Target::Variant(adt, path[rest]), interner);
                let mut dup = false;
                let mut changed = false;
                for ns in [Namespace::Value, Namespace::Type] {
                    dup |= explicit_exists(tables, imp, ns, *name);
                    let out = tables.insert(
                        imp.module,
                        ns,
                        bind_name,
                        Bind { target: Target::Variant(adt, path[rest]), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                    );
                    changed |= out == InsertOut::Changed;
                    if !dup {
                        report_dup(out, imp, *name, interner, diags);
                    }
                }
                if dup {
                    diags.push(dup_diag(imp, *name, interner));
                }
                return TryOut::Done(changed);
            }
            let (mod_path, last) = path.split_at(path.len() - 1);
            let last = last[0];
            let crate_sym = interner.intern("crate");
            let super_sym = interner.intern("super");
            let self_ty = interner.intern("Self");
            let kw = |s: Sym| s == crate_sym || s == self_sym || s == super_sym;
            // `use crate as x;`, `use super::super as x;`: the whole path
            // is module keywords and the rename is the binding name.
            // Without a rename these keep the plain lookup below, which
            // finds no such name and reports the import unresolved.
            if last != self_sym && *name != last && path.iter().all(|&s| kw(s)) {
                return match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                    PathRes::Done(target) => {
                        if !tables.check_reexport(imp, target, interner.get(*name), interner, diags) {
                            return TryOut::Done(false);
                        }
                        let bind_name = import_bind_name(*name, target, interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target, vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        TryOut::Done(out == InsertOut::Changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                };
            }
            if last == self_sym {
                // `use a::b::{self}`: bind the module itself. The binding
                // name is the segment before `self`, or the rename (the
                // parser keeps an `as` name in `name`). When there is no
                // rename and no plain segment to take the name from
                // (`use self;`, `use crate::self;`), rustc rejects the
                // import: it needs to be explicitly named.
                if *name == self_sym && !matches!(mod_path.last(), Some(&c) if !kw(c) && c != self_ty) {
                    diags.push(Diag::new(
                        "L0506",
                        imp.span,
                        "this import needs to be explicitly named",
                        "Add a rename, such as `use self as here;`.",
                    ));
                    return TryOut::Done(false);
                }
                // A std module (`use std::rc::{self, Rc}`) binds as the
                // std alias `use std::rc;` records, not as the crate root.
                if mod_path.len() > 1
                    && let PathRes::Done(Target::Extern(i)) | PathRes::Partial(Target::Extern(i), _) =
                        tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner)
                {
                    if let Some(why) = &tables.externs[i as usize].unsupported {
                        diags.push(unsupported_diag(why, imp.span));
                        return TryOut::Done(false);
                    }
                    if tables.externs[i as usize].is_std_lib {
                        // `{self}` needs a module, enum, or trait
                        // (`use std::rc::Rc::{self};` is rustc E0432).
                        if let Some(d) = std_group_parent_diag(mod_path, imp.span, interner) {
                            diags.push(d);
                            return TryOut::Done(false);
                        }
                        let bind_name = if *name == self_sym { *mod_path.last().unwrap() } else { *name };
                        return TryOut::Done(record_std_alias(tables, imp, mod_path, bind_name, interner, diags));
                    }
                }
                // The prefix names a module, or an enum whose own name
                // `self` binds (`use a::E::{self, V}`).
                let target = match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                    PathRes::Done(target) => Some(target),
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        return TryOut::Done(false);
                    }
                    _ => match tables.resolve_path(imp.module, mod_path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                        PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => Some(Target::Def(adt)),
                        PathRes::Private => {
                            diags.push(private_diag("that module", imp.span));
                            return TryOut::Done(false);
                        }
                        _ => None,
                    },
                };
                let Some(target) = target else { return TryOut::Wait };
                if !tables.check_reexport(imp, target, interner.get(*name), interner, diags) {
                    return TryOut::Done(false);
                }
                let bind_name = if *name == self_sym { mod_path.last().copied().unwrap_or(*name) } else { *name };
                let store_name = import_bind_name(bind_name, target, interner);
                let dup = explicit_exists(tables, imp, Namespace::Type, store_name);
                let out = tables.insert(
                    imp.module,
                    Namespace::Type,
                    store_name,
                    Bind { target, vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                );
                if dup && interner.get(bind_name) != "_" {
                    diags.push(dup_diag(imp, bind_name, interner));
                } else {
                    report_dup(out, imp, bind_name, interner, diags);
                }
                return TryOut::Done(out == InsertOut::Changed);
            }
            // `use ::name;`: with a leading colon the one segment reads
            // in the extern prelude only, never in this module.
            if imp.leading_colon && mod_path.is_empty() {
                return match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, true, interner) {
                    PathRes::Done(Target::Extern(i)) => {
                        if let Some(why) = &tables.externs[i as usize].unsupported {
                            diags.push(unsupported_diag(why, imp.span));
                        }
                        TryOut::Done(false)
                    }
                    PathRes::Done(Target::Module(src)) => {
                        let bind_name = import_bind_name(*name, Target::Module(src), interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target: Target::Module(src), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        TryOut::Done(out == InsertOut::Changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                };
            }
            // `pub use dep as kit;` and `use dep;`: with no binding of
            // its own here, the one segment is the extern prelude entry
            // of a dependency lust compiles from source, whose root is a
            // module of these tables. The use binds that module, as
            // `use ::dep as kit;` does.
            if path.len() == 1
                && !imp.leading_colon
                && tables.lookup(imp.module, Namespace::Type, path[0]).is_none()
                && let Some(src) = tables.source_extern_root(imp.module, path[0], interner)
            {
                let bind_name = import_bind_name(*name, Target::Module(src), interner);
                let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                let out = tables.insert(
                    imp.module,
                    Namespace::Type,
                    bind_name,
                    Bind { target: Target::Module(src), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                );
                if dup && interner.get(*name) != "_" {
                    diags.push(dup_diag(imp, *name, interner));
                } else {
                    report_dup(out, imp, *name, interner, diags);
                }
                return TryOut::Done(out == InsertOut::Changed);
            }
            // `use std;` and `use std as s;`: the one segment names
            // the extern crate root itself, so there is no module
            // part to split off.
            if path.len() == 1
                && let PathRes::Done(Target::Extern(i)) =
                    tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner)
            {
                // `extern crate core; pub use core as c;` and `use std as
                // core; pub use core as c;`: the one segment is a binding
                // (an `extern crate` item or a use) that cannot be
                // re-exported wider than it is (rustc E0365). With no
                // binding in the module, the extern prelude answers, and a
                // root `extern crate` item is that prelude entry.
                if imp.vis != VisKind::Priv
                    && let Some((bvis, bmod)) = tables.extern_binding_vis(imp.module, path[0], i)
                    && !tables.vis_within(&imp.vis, imp.module, &bvis, bmod, interner)
                {
                    diags.push(reexport_diag(interner.get(path[0]), imp.span));
                    return TryOut::Done(false);
                }
                let mut inserted = false;
                if let Some(why) = &tables.externs[i as usize].unsupported {
                    diags.push(unsupported_diag(why, imp.span));
                } else if tables.externs[i as usize].is_std_lib {
                    inserted = record_std_alias(tables, imp, path, *name, interner, diags);
                }
                return TryOut::Done(inserted);
            }
            let modres = match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                // `use std::marker::PhantomData;`: an item of a std
                // source overlay module imports from it (W-STD-C).
                PathRes::Done(Target::Extern(i))
                    if mod_path.len() == 2
                        && let Some((m, false)) = tables.std_module_at(i, mod_path[1], interner)
                        && [Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| tables.lookup(m, ns, last).is_some()) =>
                {
                    PathRes::Done(Target::Module(m))
                }
                other => other,
            };
            match modres {
                PathRes::Done(Target::Module(src)) => {
                    // The source's glob binding of the name may still be
                    // replaced by its own pending single import.
                    let explicit_here = [Namespace::Type, Namespace::Value, Namespace::Macro]
                        .iter()
                        .any(|&ns| matches!(tables.lookup(src, ns, last), Some(BindState::One(b)) if b.rank >= 2));
                    if src != imp.module && !explicit_here && single_pending_for(tables, src, last, imp.module, interner) {
                        return TryOut::Wait;
                    }
                    // An ambiguous glob name can still settle (the
                    // source's explicit import lands): wait for the stall.
                    let ambiguous_here = [Namespace::Type, Namespace::Value].iter().any(|&ns| {
                        matches!(tables.lookup(src, ns, last), Some(BindState::Ambiguous))
                            && tables.ambiguous_visible(src, ns, last, imp.module, interner)
                    });
                    if ambiguous_here && !tables.import_stall {
                        return TryOut::Wait;
                    }
                    // Bind the name in every namespace that has it.
                    let mut any = false;
                    let mut changed = false;
                    let mut saw_private = false;
                    // A re-export of an import binding reaches no further
                    // than that binding (rustc E0364); `check_reexport`
                    // below checks the item's own visibility.
                    let mut narrower = false;
                    let mut found: Vec<(Namespace, Bind)> = Vec::new();
                    let mut alias_paths: Vec<Vec<Sym>> = Vec::new();
                    for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                        let state = match ns {
                            Namespace::Macro => tables.macro_import_lookup(imp, src, mod_path.is_empty(), last),
                            _ => tables.lookup(src, ns, last).cloned(),
                        };
                        match state {
                            Some(BindState::One(b)) => {
                                if tables.visible(&b.vis, b.def_module, imp.module, interner) {
                                    any = true;
                                    let is_macro = matches!(b.target, Target::Def(d) if tables.def_info.get(&d).is_some_and(|i| i.kind == ResKind::Macro));
                                    // An `extern crate` item is a binding like any
                                    // other: a private one cannot be re-exported
                                    // wider (rustc E0365, deny-by-default lint
                                    // pub_use_of_private_extern_crate).
                                    narrower |= imp.vis != VisKind::Priv
                                        && !is_macro
                                        && !tables.vis_within(&imp.vis, imp.module, &b.vis, b.def_module, interner);
                                    found.push((ns, Bind { target: b.target, vis: imp.vis.clone(), rank: 2, def_module: imp.module }));
                                } else {
                                    saw_private = true;
                                }
                            }
                            Some(BindState::Ambiguous) if !tables.ambiguous_visible(src, ns, last, imp.module, interner) => {
                                saw_private = true;
                            }
                            Some(BindState::Ambiguous) => {
                                // An explicit import of an ambiguous name
                                // cannot settle it; it stays ambiguous,
                                // and the import itself is an error if
                                // the source is still ambiguous at the end.
                                any = true;
                                let certain = tables.ambiguous_certain(src, ns, last, None, interner);
                                let entry = (imp.vis.clone(), imp.module, AmbItem::Amb { certain });
                                let out = insert_ambiguous(tables, imp.module, ns, *name, vec![entry]);
                                changed |= out;
                                tables.ambig_single.push((imp.clone(), ns, src, last));
                            }
                            // A std import in the source module binds
                            // no target; importing it onward copies
                            // the alias under this import's name.
                            None => {
                                let key = (src, ns_index(ns) as u8, last);
                                if let Some((avis, apath)) = tables.std_aliases.get(&key).cloned() {
                                    let adef = tables.std_alias_def_module(key);
                                    if tables.visible(&avis, adef, imp.module, interner) {
                                        any = true;
                                        narrower |= imp.vis != VisKind::Priv && !tables.vis_within(&imp.vis, imp.module, &avis, adef, interner);
                                        if !alias_paths.contains(&apath) {
                                            alias_paths.push(apath);
                                        }
                                    } else {
                                        saw_private = true;
                                    }
                                }
                            }
                        }
                    }
                    if !any {
                        if saw_private {
                            diags.push(private_diag(interner.get(last), imp.span));
                            return TryOut::Done(false);
                        }
                        // A std item the shipped platform module does
                        // not define keeps the std compat handling of
                        // the extern branch below (fx-stdos): a
                        // partial platform module (`std::os::unix::fs`
                        // holds only `MetadataExt`) must not hide the
                        // items that resolved before it existed.
                        if tables.std_platform_compat_fallback(path, src, imp.module, imp.leading_colon, interner) {
                            return TryOut::Done(record_std_alias(tables, imp, path, *name, interner, diags));
                        }
                        return TryOut::Wait;
                    }
                    // One re-export check per distinct target: a name in
                    // two namespaces usually names two items, a struct
                    // names the same def in type and value position.
                    let mut seen_targets: Vec<Target> = Vec::new();
                    for (_, bind) in &found {
                        if seen_targets.contains(&bind.target) {
                            continue;
                        }
                        seen_targets.push(bind.target);
                        if !tables.check_reexport(imp, bind.target, interner.get(last), interner, diags) {
                            return TryOut::Done(false);
                        }
                    }
                    if narrower {
                        diags.push(reexport_diag(interner.get(last), imp.span));
                        return TryOut::Done(false);
                    }
                    let mut dup_reported = false;
                    for (ns, bind) in found {
                        let bind_name = import_bind_name(*name, bind.target, interner);
                        // The macro self re-export idiom: `macro_rules! m`
                        // plus one `use m;` in the defining module is one
                        // binding in rustc, and the `use` sets how far the
                        // macro name reaches. A definition's own binding
                        // is textual only (rustc has none), so any `use`
                        // that binds the name replaces it instead of
                        // duplicating it; a second `use` is a duplicate.
                        let is_macro_self_use = ns == Namespace::Macro && tables.macro_textual_binds.contains_key(&(imp.module, bind_name));
                        if is_macro_self_use {
                            // The binding turns real even with the same
                            // target and visibility, so imports waiting
                            // on it must retry.
                            tables.macro_textual_binds.remove(&(imp.module, bind_name));
                            tables.maps[imp.module.0 as usize][ns_index(ns)].insert(bind_name, BindState::One(bind));
                            tables.touch(imp.module, bind_name);
                            changed = true;
                            continue;
                        }
                        // An earlier std alias of the same name in the
                        // same namespace is an explicit binding too.
                        let dup = explicit_exists(tables, imp, ns, bind_name)
                            || tables.explicit_std_alias((imp.module, ns_index(ns) as u8, bind_name));
                        if ns != Namespace::Macro {
                            tables.single_binds.push((imp.span, imp.module, src, last, ns, bind.target));
                        }
                        let out = tables.insert(imp.module, ns, bind_name, bind);
                        if dup && interner.get(*name) != "_" {
                            if !dup_reported {
                                diags.push(dup_diag(imp, *name, interner));
                                dup_reported = true;
                            }
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        changed |= out == InsertOut::Changed;
                    }
                    for apath in &alias_paths {
                        changed |= record_std_alias(tables, imp, apath, *name, interner, diags);
                    }
                    TryOut::Done(changed)
                }
                PathRes::Done(Target::Extern(i)) => {
                    // `use dep::Name` where the path did not enter a
                    // source dependency's module tree: a canonical
                    // `std` path records an alias the rewrite pass
                    // expands back to the full path (renames bind,
                    // and a plain imported fn or module name works
                    // the same way). An unsupported dependency
                    // (adapter, shim, or other crate with no lust
                    // form yet) rejects at the import with L0508
                    // naming the crate, since its item names are
                    // unknown and a later plain use could not be
                    // told from a typo.
                    let mut inserted = false;
                    if let Some(why) = &tables.externs[i as usize].unsupported {
                        diags.push(unsupported_diag(why, imp.span));
                    } else if mod_path.len() == 1
                        && let Some((m, true)) = tables.std_module_at(i, last, interner)
                    {
                        // `use std::time;`: a std source module binds
                        // like a local module (W-STD-C).
                        let bind_name = import_bind_name(*name, Target::Module(m), interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target: Target::Module(m), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        inserted = out == InsertOut::Changed;
                    } else if tables.externs[i as usize].is_std_lib {
                        inserted = record_std_alias(tables, imp, path, *name, interner, diags);
                    }
                    TryOut::Done(inserted)
                }
                PathRes::Done(_) => TryOut::Wait,
                PathRes::Private => {
                    diags.push(private_diag("that module", imp.span));
                    TryOut::Done(false)
                }
                _ => TryOut::Wait,
            }
        }
    }
}

/// True when two canonical std paths name one item: equal, or equal
/// after the crate segment (`core::cell::RefCell` is `std::cell::RefCell`).
/// Other spellings of one item count as two (an ambiguity, which only
/// rejects).
fn same_std_item(a: &[Sym], b: &[Sym]) -> bool {
    a == b || (a.len() > 1 && a.len() == b.len() && a[1..] == b[1..])
}

/// L0507 for each single import that read an ambiguous name
/// (`ambig_single`) whose source is still ambiguous now, L0510 when the
/// source settled to an item the import cannot see; once per import.
/// Returns the imports reported.
fn report_ambig_single(tables: &mut ResolvedTables, interner: &Interner, diags: &mut Vec<Diag>) -> Vec<Span> {
    let mut seen: Vec<Span> = Vec::new();
    for (imp, ns, src, last) in std::mem::take(&mut tables.ambig_single) {
        let state = match (ns, &imp.kind) {
            (Namespace::Macro, ImportKind::Single { path, .. }) => tables.macro_import_lookup(&imp, src, path.len() == 1, last),
            _ => tables.lookup(src, ns, last).cloned(),
        };
        if seen.contains(&imp.span) {
            continue;
        }
        // A source that settled to an item the import cannot see is
        // a private import, as rustc reports it from the final tables.
        let diag = match state {
            Some(BindState::Ambiguous) if tables.ambiguous_certain(src, ns, last, None, interner) => {
                ambiguous_diag(interner.get(last), imp.span)
            }
            Some(BindState::One(f)) if !tables.visible(&f.vis, f.def_module, imp.module, interner) => {
                private_diag(interner.get(last), imp.span)
            }
            _ => continue,
        };
        seen.push(imp.span);
        diags.push(diag);
    }
    seen
}

/// True when `module` binds `name` at glob rank in some namespace (an
/// ambiguous name or a glob std alias included).
fn glob_bound(tables: &ResolvedTables, module: ModuleId, name: Sym) -> bool {
    [Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| {
        matches!(tables.lookup(module, ns, name), Some(BindState::Ambiguous) | Some(BindState::One(Bind { rank: 0..=1, .. })))
            || tables.std_glob_aliases.contains_key(&(module, ns_index(ns) as u8, name))
    })
}

/// Marks the single import at `span` (of `name` in `module`) as
/// settled (`pending_single`).
fn settle_single(tables: &mut ResolvedTables, module: ModuleId, name: Sym, span: Span) {
    if let Some(list) = tables.pending_single.get_mut(&(module, name)) {
        list.retain(|p| p.span != span);
        if list.is_empty() {
            tables.pending_single.remove(&(module, name));
        }
        tables.touch(module, name);
    }
}

/// True when module `src` has a pending single import of `name` that
/// code in `from` can see and that could still bind the name: a glob
/// binding of the name in `src` may yet be replaced, so a single import
/// from `from` waits (rustc's `single_imports` check in
/// `resolve_ident_in_module`). The pending import could bind it when
/// its module path is not resolved yet, when its source module has a
/// binding of the name the pending import's module can see, or, until
/// the fixpoint stalls (`import_stall`), when the source has no
/// binding of the name yet (a glob may still bring one).
fn single_pending_for(tables: &ResolvedTables, src: ModuleId, name: Sym, from: ModuleId, interner: &Interner) -> bool {
    let Some(list) = tables.pending_single.get(&(src, name)) else { return false };
    list.iter().any(|p| {
        tables.visible(&p.vis, src, from, interner)
            && !p.mod_path.is_empty()
            && match tables.resolve_module_path(src, &p.mod_path, p.leading_colon, interner) {
                PathRes::Done(Target::Module(m)) => [Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| {
                    match tables.lookup(m, ns, p.last) {
                        Some(BindState::One(b)) => tables.visible(&b.vis, b.def_module, src, interner),
                        Some(BindState::Ambiguous) => tables.ambiguous_visible(m, ns, p.last, src, interner),
                        // A glob may still bring it until the stall.
                        None => !tables.import_stall,
                    }
                }),
                PathRes::Done(_) => false,
                _ => true,
            }
    })
}

/// Checks each single import binding again against the final tables,
/// as rustc does (`finalize_import`). The fixpoint can bind an import
/// to the source's glob binding before the source's own explicit
/// import replaces it (an import cycle the pending rule does not
/// order). The final source binding decides: private is L0510,
/// ambiguous is L0507, and another item is a reject, never a pick.
/// Returns the imports reported.
fn finalize_singles(tables: &mut ResolvedTables, interner: &Interner, diags: &mut Vec<Diag>) -> Vec<Span> {
    let mut seen: Vec<Span> = Vec::new();
    for (span, module, src, last, ns, target) in std::mem::take(&mut tables.single_binds) {
        if seen.contains(&span) {
            continue;
        }
        let diag = match tables.lookup(src, ns, last) {
            Some(BindState::One(f)) if !tables.visible(&f.vis, f.def_module, module, interner) => private_diag(interner.get(last), span),
            Some(BindState::One(f)) if f.target != target => Diag::new(
                "L0505",
                span,
                format!(
                    "this import of `{}` read a binding that a later import replaced; that import order is not supported yet",
                    interner.get(last)
                ),
                "Import the item from the module that defines it.",
            ),
            Some(BindState::Ambiguous) if tables.ambiguous_certain(src, ns, last, None, interner) => {
                ambiguous_diag(interner.get(last), span)
            }
            _ => continue,
        };
        seen.push(span);
        diags.push(diag);
    }
    seen
}

/// Marks a name ambiguous in `module`: through a glob of a module
/// where it is ambiguous, or an explicit import of such a name. `vis`
/// is the visibility the name gets here (`ambig_vis`). Returns true on
/// a change, a wider visibility included.
fn insert_ambiguous(tables: &mut ResolvedTables, module: ModuleId, ns: Namespace, name: Sym, vis: Vec<AmbEntry>) -> bool {
    match tables.lookup(module, ns, name) {
        Some(BindState::One(Bind { rank: 2, .. })) => false,
        _ => tables.set_ambiguous(module, ns, name, vis),
    }
}

/// True when `name` in `ns` is already bound in the importing module
/// by a local item or by an earlier explicit import. Rust rejects a
/// second explicit binding even for the same target (E0252, E0255),
/// which the rank rules in `insert` alone treat as `Same`, so callers
/// check this before they insert and report `dup_diag` once.
fn explicit_exists(tables: &ResolvedTables, imp: &Import, ns: Namespace, name: Sym) -> bool {
    matches!(tables.lookup(imp.module, ns, name), Some(BindState::One(b)) if b.rank >= 2)
}

/// The L0106 diagnostic for a name bound more than once in one module.
fn dup_diag(imp: &Import, name: Sym, interner: &Interner) -> Diag {
    Diag::new(
        "L0106",
        imp.span,
        format!("`{}` is defined more than once", interner.get(name)),
        "Rename one of the imports with `as`, or remove one.",
    )
}

/// The binding name for one explicit import. `as _` binds no usable
/// name, so it is stored under a synthetic name keyed by its target:
/// several `as _` imports of different items (the usual trait imports)
/// then coexist, and a repeat of one item lands on the same key. The
/// synthetic name is not a legal Rust identifier, so source text can
/// never name it.
pub fn import_bind_name(name: Sym, target: Target, interner: &Interner) -> Sym {
    if interner.get(name) != "_" {
        return name;
    }
    let key = match target {
        Target::Def(d) => d.hash.0 ^ ((d.krate.0 as u64) << 1),
        Target::Module(m) => (m.0 as u64) ^ 0x9e37_79b9,
        Target::Extern(i) => (i as u64) ^ 0x51f_15e,
        Target::Variant(d, s) => d.hash.0 ^ (s.0 as u64).rotate_left(17),
    };
    interner.intern(&format!("$lust$anon${key:x}"))
}

/// Reports a duplicate explicit import (two sources, one binding name).
/// An `as _` import binds no name and is never a duplicate.
fn report_dup(out: InsertOut, imp: &Import, name: Sym, interner: &Interner, diags: &mut Vec<Diag>) {
    if out == InsertOut::Dup && interner.get(name) != "_" {
        diags.push(dup_diag(imp, name, interner));
    }
}

/// The L0508 diagnostic for a use of a dependency crate that has no
/// lust source, adapter, or shim form yet. `why` names the crate.
pub fn unsupported_diag(why: &str, span: Span) -> Diag {
    Diag::new("L0508", span, why.to_string(), "Build this crate with Cargo, or remove the dependency from the lust dev build.")
}

/// The L0510 diagnostic for a name that exists but is not visible. The
/// fix names the smallest widening that would work, and never applies it.
pub fn private_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("`{name}` is private"),
        "Make the item `pub(crate)` (the smallest widening that works), or add a public re-export.",
    )
}

/// The L0510 diagnostic for a re-export that reaches further than the
/// item or binding it re-exports (rustc E0364).
fn reexport_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("`{name}` is private, and cannot be re-exported"),
        "Make the item `pub`, or lower the visibility of the `use` to match.",
    )
}

/// The L0507 diagnostic for a use of a glob-ambiguous name.
/// L0505 for a name a std glob import may bring or shadow: lust does
/// not know every name a std module exports.
pub fn std_glob_name_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0505",
        span,
        format!("`{name}` next to a std glob import is not supported yet: the glob may also bring `{name}`"),
        "Import the std items you use by name instead of with `*`, or import this name explicitly.",
    )
}

pub fn ambiguous_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0507",
        span,
        format!("`{name}` is ambiguous: two glob imports bring different items with this name"),
        "Import the one you mean explicitly: an explicit import wins over globs.",
    )
}
