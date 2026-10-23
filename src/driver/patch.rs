// The body patch (docs/ARCH.md 8.3, step 4; W-INCR2): a warm request on
// the resolver path whose edits all sit inside fn bodies edits the
// merged Ast in place instead of resolving the crate again.
//
// A full resolve costs work in proportion to the crate: the std splice
// and its second resolve, discovery, expansion, the import fixpoint,
// rewrite, flatten, and the Ast scan. A body edit changes none of what
// those phases decide outside the edited body: module tree, bindings,
// flat names, item scans, and std needs all stand. So the patch
// re-reads the files the last resolve read, finds the one fn body each
// changed file's edit sits in, lexes and parses that body alone, moves
// the spans after the edit (driver/span_shift.rs), rewrites the body's
// paths against the last resolve's frozen tables, and rescans that one
// item. The shared tail then runs as for any bodies-mode request.
//
// Rule zero: the patched state must be the state a full resolve of the
// new text builds, up to arena order. Every condition below that cannot
// be proven from the edit alone gives up (`None`), and the caller
// resolves in full, which is always correct. It gives up when:
// - the crate selection inputs, the client view, or an expansion's
//   outside inputs changed, or an expansion read a position;
// - the root file changed and carries a std splice its text no longer
//   ends with (the splice moves with an edit in the root text: its byte
//   ranges in the base, the resolver tables, and the Ast);
// - an edit is not strictly inside one top-level fn or method body, or
//   inside cfg-disabled code the expander dropped (`find_inactive_edit`);
// - the old or new body holds a `$`, an item keyword other than `fn`,
//   `static`, `const`, `use`, `struct`, `enum`, `type`, and `impl`, a
//   macro the expander owns, or a parser macro while a user macro may
//   take its name; or its items (`stmt_items`, and the body impls flatten
//   hoisted to the module items) are not the old ones in the old blocks
//   (`same_items`). A block type item is part of its holder's item scan
//   (`ast_hash::item_scan`), so the scan must stand too; the methods of
//   body impls check again (`body_impl_hashes`).
//   Attributes and the pure builtin macros (`PURE_MACROS`) patch when no
//   user or dependency macro can take a builtin's name: the new body
//   passes the cfg name check and expands alone, as the resolver checks
//   and expands its file; the expansion must read nothing outside the
//   body (no `Dep` but the cfg-disabled nodes it drops);
// - the fn's parameter patterns or signature expressions are not
//   provably moved ahead of the new body (`sig_nodes.rs`). A fn that
//   returns `impl Trait` patches, but its body decides the hidden type,
//   so its item scan folds the body hash in (`ast_hash::item_scan`): the
//   patch rescans the item as a full resolve would (`Front::items`,
//   `env_hash`), and the tail keeps the program only when the new body
//   reveals the same hidden type (`opaque::hidden_stands`); else it
//   collects and walks every passing body's reads (`Front::rpit_edit`),
//   so only the users of the opaque type check again. A `const fn` patches, but
//   `const` values bake its body in, so when a const evaluation may run it
//   (`const_reach.rs`) the request then collects and walks reads as a cold
//   resolve of a const fn body edit does (`Patched::const_fn`);
// - the file's std needs or std platform mention moved;
// - the new body does not lex, parse, or rewrite cleanly, or its item
//   scan moved (errors then come from the full path, in cold order);
// - the last full resolve's tables are shared, or patches grew the Ast
//   arenas past twice their resolved size.
//
// The item patch (sigedit P1.3, path "item"): an edit strictly inside a
// free fn or inherent method that touches its header re-parses and
// rewrites that fn whole (`find_item_edit`), when its outline stands
// (driver/item_outline.rs: everything name resolution reads from it) and
// so do its `impl Trait` params (collect lowers the same ones to the same
// synthetic generics). A body that calls a user macro and whose text
// stands takes its stored expansion (`kept_body`), so only the header is
// new; a change in the body or the macro resolves in full. The
// item rescans, and the compile tail runs the resolve path's slot update
// in signatures mode with the fn's name as the changed name. A kept
// program stands when the signature delta redoes each edited header on it
// (`reuse_kept`, driver/kept_delta.rs); else the tail collects in full. A
// method is only ever called by name, so a method's header edit also
// takes signatures mode (P1.5). An edit of only the names in a struct's
// or enum's `#[derive(..)]` lists (P1.4, `find_derive_edit`) patches the
// item's attributes and derives the same way, in full mode: any body may
// read the derives (`ReadKey::Derives`). In a check the kept program
// stands when the derive delta takes the edit (driver/kept_derive.rs).
use super::compile::{fn_def_at, fn_text_hash};
use super::session::{Caches, Front};
use super::span_shift::{self, Edit, FileRanges};
use crate::ast::{Ast, BlockId, FnDef, ItemKind, TyExpr};
use crate::diag::{CtxtId, FileId, SourceMap};
use crate::intern::{FxMap, Sym};
use crate::lexer::{self, Tok};
use crate::resolve::imports::ResolvedTables;
use crate::ty::lang::{ShippedCrate, StdFnDef, StdNeeds};
use std::sync::Arc;
use std::time::SystemTime;

/// A file's stat when its text entered the map: modification time and
/// size. Trusted only when the file was already older than the request
/// that read it, so a write in the same clock tick is never missed.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Stamp {
    mtime: SystemTime,
    len: u64,
}

impl PatchBase {
    /// For `main::census`: the base's resolved tables, when no one else holds them.
    pub(crate) fn tables_mut(&mut self) -> Option<&mut ResolvedTables> {
        Arc::get_mut(&mut self.tables)
    }

    /// For `main::census` (LUST_FRONT_CENSUS=1, a probe of a front image): drops one part
    /// (1 file ranges and extras, 2 item scans, 3 dropped, 4 the rest of its lists; what is
    /// left after them is mostly the tables).
    pub(crate) fn drop_part(&mut self, part: usize) {
        use std::mem::take;
        match part {
            1 => {
                drop(self.ranges.take());
                drop(self.extras.take());
            }
            2 => drop(take(&mut self.item_scans)),
            3 => drop(take(&mut self.dropped)),
            4 => {
                drop(take(&mut self.fns_by_file));
                drop(take(&mut self.body_hashes));
                drop(take(&mut self.fn_lines));
                drop(take(&mut self.live_slots));
                drop(take(&mut self.root_unspliced));
                drop(self.local_names.take());
            }
            _ => {}
        }
    }
}

/// What the last full resolve left for the next request's patch. The
/// merged Ast, source map, item scans, and slot state live in `Front`.
pub(crate) struct PatchBase {
    /// Fingerprint of the crate selection inputs (`inputs_fingerprint`).
    inputs: u64,
    /// The root file's text before any std splice.
    root_unspliced: String,
    /// True when the std splice follows the root text in file 0.
    spliced: bool,
    /// Per map file: the std needs and std platform mention of its own
    /// text (the root's before the splice); none for a file of the std
    /// platform crate. The std plan folds only the other files' asks
    /// (`ResolvedCrate::std_asks`), and the platform crate's files always
    /// name platform modules, so counting them would hide a root that
    /// stops naming one (a cold resolve then drops the platform crate).
    needs: Vec<(StdNeeds, bool)>,
    /// Per map file: the stat that proves its text unchanged, if any.
    stamps: Vec<Option<Stamp>>,
    /// Some file of the session defines a macro (`macro_rules`): tokens
    /// of one file can then sit in another file's nodes (no `ranges`).
    user_macros: bool,
    /// Some file can make a user macro answer to a parser macro's name
    /// (`shadows_parser_macro`): a `println!` in a body may then be the
    /// user's macro, which the expander owns.
    shadowed: bool,
    tables: Arc<ResolvedTables>,
    /// Per crate root module: the crate's cfg environment and name, for
    /// expanding a body of that crate alone, when no user or dependency
    /// macro can take a builtin's name there (the caller decides: with no
    /// dependency crate, no file `shadows_builtin`; else per crate,
    /// driver/macro_scope.rs). A crate that is not here resolves in full.
    expand: FxMap<crate::ty::defs::ModuleId, (crate::resolve::cfg::CfgEnv, String)>,
    /// `ResolvedTables::local_named_set`, for the patch's path rewrites.
    local_names: Option<FxMap<Sym, u8>>,
    /// The thread that builds `local_names` right after the full resolve
    /// (sigedit P1.2), so the first patch does not wait for it. It holds
    /// a share of `tables`; `find_edits` joins it first.
    local_names_job: Option<std::thread::JoinHandle<FxMap<Sym, u8>>>,
    std_ranges: Vec<(u32, u32, ShippedCrate)>,
    std_routes: Vec<&'static StdFnDef>,
    std_methods: (u32, u32),
    fn_lines: Vec<u32>,
    body_hashes: Vec<u64>,
    /// Expression arena length after the full resolve.
    arena_base: usize,
    /// Per map file, where its nodes sit (`span_shift::ranges_by_file`).
    /// Set at the full resolve when no macro or include can put a file's
    /// spans in another file's nodes; with macros or includes, the first
    /// patch probes the Ast (`span_shift::probe_extras`) and sets both
    /// this and `extras`. None walks the whole Ast for each edit.
    ranges: Option<Vec<FileRanges>>,
    /// Per map file, the probed extra nodes an edit in that file must
    /// also visit (`span_shift::ExtraNodes`); None until probed, and
    /// never when the resolve could prove ranges on its own.
    extras: Option<Vec<span_shift::ExtraNodes>>,
    /// Per map file, the fns whose name span is in it (`Front::fn_loc`
    /// indexes): an edit that adds lines renumbers only its own file's.
    fns_by_file: Vec<Vec<u32>>,
    /// True per slot an AST fn of this resolve holds, for the slot
    /// update's dead-slot rule. Slot assignment does not move while a
    /// base lives, so this is built once here, not per patch.
    live_slots: Vec<bool>,
    /// Per item index, its fns' raw body hashes from the item's last
    /// full rescan in a patch (which also proved no method of the item
    /// holds a body item): a later edit in the same impl rescans only
    /// the edited method and reuses these for the rest.
    item_scans: FxMap<usize, Vec<u64>>,
    /// The cfg-disabled nodes the expander dropped (`Dep::Dropped`), by
    /// file and start, with the spans of this text.
    dropped: Vec<Dropped>,
    /// What const evaluation may reach (`const_reach.rs`), built at the full
    /// resolve (compile.rs; else on the first const fn body or header edit)
    /// and kept up to date by later patches.
    pub(super) reach: Option<super::const_reach::ConstReach>,
    /// Under the patch oracle (`item_oracle.rs`): the cold resolve input.
    pub(super) oracle_input: Option<super::item_oracle::ColdInput>,
    /// `ResolveCache::expansions` at the full resolve: while it stands,
    /// a file's stored expansion is the one this Ast was parsed from
    /// (a failed resolve after it can store another; see `kept_body`).
    expansions: u64,
    /// The bodies the last patch's item edits took from a stored
    /// expansion, at their new places (`kept_body`). Only the last
    /// patch's: any other edit since may have moved what their contexts
    /// name (a macro definition in another file).
    kept_bodies: Vec<KeptBody>,
    /// The files patches edited since the full resolve: a stored
    /// expansion whose tokens or contexts name one may hold spans the
    /// patches moved since (`kept_body`).
    edited: Vec<FileId>,
    /// The full resolve's per-file expander (`expand_by_file`).
    file_exp: Option<Arc<crate::resolve::worklist::FileExpander>>,
}

/// One cfg-disabled node the last full resolve dropped (`Dep::Dropped`).
#[derive(Clone, Copy)]
struct Dropped {
    file: u32,
    lo: u32,
    hi: u32,
    item: bool,
    brace: bool,
}

/// The crate selection inputs a patch must see unchanged: anything that
/// steers discovery, cfg, crate identity, or what expansions show.
pub(super) fn inputs_fingerprint(parts: &dyn std::fmt::Debug) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&format!("{parts:?}"), &mut h);
    std::hash::Hasher::finish(&h)
}

/// True when every delimiter in a patch's lexed range is balanced. A
/// patch that sees an unbalanced range falls back to the full path,
/// which reports the delimiter error as a cold compile does.
fn balanced(l: &lexer::Lexed) -> bool {
    crate::expand::delimiter_error(&l.tokens).is_none()
}

/// True when `text` may define a macro named like a parser macro
/// (`macro_rules! println`) or import one under such a name (`as vec`).
/// A text scan: a match in a comment or string only costs the patch for
/// bodies that call parser macros.
fn shadows_parser_macro(text: &str) -> bool {
    shadows(text, &|name| crate::expand::builtin::is_passthrough(name))
}

/// `shadows_parser_macro` for every builtin macro (parser and expander
/// owned), and for a macro whose name a macro supplies
/// (`macro_rules! $name`, read as an empty name).
pub(super) fn shadows_builtin(text: &str) -> bool {
    use crate::expand::builtin::{is_passthrough, is_token_builtin};
    shadows(text, &|name| name.is_empty() || is_passthrough(name) || is_token_builtin(name))
}

/// True when `text` may define a macro whose name `named` takes, or
/// import one under such a name (`as name` that ends a use tree: then
/// `;`, `,`, or `}`). `as $name` is a cast in a macro, not an import.
fn shadows(text: &str, named: &dyn Fn(&str) -> bool) -> bool {
    let ident_after = |rest: &str| -> String { rest.trim_start().chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect() };
    let word_before = |i: usize| i == 0 || !text.as_bytes()[i - 1].is_ascii_alphanumeric() && text.as_bytes()[i - 1] != b'_';
    let defines = text.match_indices("macro_rules").any(|(i, m)| {
        let rest = text[i + m.len()..].trim_start();
        rest.strip_prefix('!').is_some_and(|r| named(&ident_after(r)))
    });
    let renames = text.match_indices("as").any(|(i, m)| {
        let rest = &text[i + m.len()..];
        if !word_before(i) || !rest.starts_with(char::is_whitespace) {
            return false;
        }
        let rest = rest.trim_start();
        let name = ident_after(rest);
        !name.is_empty() && rest[name.len()..].trim_start().starts_with([';', ',', '}']) && named(&name)
    });
    defines || renames
}

/// The std needs and platform mention of one file's own text.
fn file_needs(text: &str) -> (StdNeeds, bool) {
    (crate::ty::lang::std_needs(text), crate::resolve::worklist::mentions_std_platform(text))
}

fn stamp_of(path: &str, request_start: SystemTime) -> Option<Stamp> {
    let md = std::fs::metadata(path).ok()?;
    let mtime = md.modified().ok()?;
    // A file modified within two seconds of the request that read it may
    // change again without its stat moving: never trust that stat.
    let old = request_start.duration_since(mtime).is_ok_and(|age| age.as_secs() >= 2);
    old.then_some(Stamp { mtime, len: md.len() })
}

impl PatchBase {
    /// The base a successful full resolve leaves (`resolved_setup`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        front: &Front,
        inputs: u64,
        root_unspliced: String,
        spliced: bool,
        tables: Arc<ResolvedTables>,
        std_out: (&[(u32, u32, ShippedCrate)], &[&'static StdFnDef], (u32, u32)),
        fn_lines: Vec<u32>,
        body_hashes: Vec<u64>,
        request_start: SystemTime,
        expand: FxMap<crate::ty::defs::ModuleId, (crate::resolve::cfg::CfgEnv, String)>,
    ) -> PatchBase {
        let map = &front.map;
        let n = map.file_count();
        let texts: Vec<(usize, &str)> =
            (0..n).map(|k| (k, if k == 0 { root_unspliced.as_str() } else { map.text(FileId(k as u32)).unwrap_or("") })).collect();
        let platform = crate::resolve::worklist::std_platform_root();
        let platform = platform.parent().unwrap_or(&platform);
        let needs = super::compile::par_map(&texts, |&(k, t)| {
            if k > 0 && std::path::Path::new(map.path(FileId(k as u32))).starts_with(platform) { Default::default() } else { file_needs(t) }
        });
        // The stamps (a stat per file) and the shadow scan (every file's text) on the pool.
        let stamps = super::compile::par_map(&texts, |&(k, _)| {
            let path = map.path(FileId(k as u32));
            if path.is_empty() { None } else { stamp_of(path, request_start) }
        });
        let user_macros = texts.iter().any(|(_, t)| t.contains("macro_rules"));
        let shadowed = user_macros && super::compile::par_map(&texts, |(_, t)| shadows_parser_macro(t)).into_iter().any(|s| s);
        let includes = front.chunks.iter().any(|c| c.expand_deps.iter().any(|d| matches!(d, crate::expand::Dep::File { .. })));
        let ranges = (!user_macros && !includes).then(|| span_shift::ranges_by_file(&front.ast, n));
        let mut fns_by_file: Vec<Vec<u32>> = vec![Vec::new(); n];
        // Nested fns too (`(usize::MAX, Some(stmt item))`): an edit above
        // one in its file moves its line as well.
        for (i, &(item, sub)) in front.fn_loc.iter().enumerate() {
            let known = if item == usize::MAX { sub.is_some_and(|k| k < front.ast.stmt_items.len()) } else { item < front.ast.items.len() };
            if !known {
                continue;
            }
            let file = fn_def_at(&front.ast, item, sub).name_span.file;
            if let Some(v) = fns_by_file.get_mut(file.0 as usize) {
                v.push(i as u32);
            }
        }
        let mut live_slots = vec![false; front.slot_of.len()];
        for &s in front.fn_slot.iter().take(front.ast_fn_count) {
            if let Some(l) = live_slots.get_mut(s as usize) {
                *l = true;
            }
        }
        let mut dropped: Vec<Dropped> = front
            .chunks
            .iter()
            .flat_map(|c| &c.expand_deps)
            .filter_map(|d| match *d {
                crate::expand::Dep::Dropped { file, lo, hi, item, brace } => Some(Dropped { file, lo, hi, item, brace }),
                _ => None,
            })
            .collect();
        dropped.sort_unstable_by_key(|d| (d.file, d.lo));
        PatchBase {
            inputs,
            root_unspliced,
            spliced,
            needs,
            stamps,
            user_macros,
            shadowed,
            expand,
            local_names_job: {
                let t = tables.clone();
                crate::pool::thread("lust-patch-base").spawn(move || t.local_named_set()).ok()
            },
            tables,
            local_names: None,
            std_ranges: std_out.0.to_vec(),
            std_routes: std_out.1.to_vec(),
            std_methods: std_out.2,
            fn_lines,
            body_hashes,
            arena_base: front.ast.exprs.len(),
            ranges,
            extras: None,
            fns_by_file,
            live_slots,
            item_scans: FxMap::default(),
            dropped,
            reach: None,
            oracle_input: None,
            expansions: front.resolve_cache.expansions(),
            kept_bodies: Vec::new(),
            edited: Vec::new(),
            file_exp: front.resolve_cache.file_expander(),
        }
    }

    /// The std splice ranges and routes of the patched text.
    pub(super) fn std_ranges(&self) -> &[(u32, u32, ShippedCrate)] {
        &self.std_ranges
    }

    pub(super) fn std_routes(&self) -> &[&'static StdFnDef] {
        &self.std_routes
    }
}

/// A patched request's setup results, in `resolved_setup`'s shape.
pub(super) struct Patched {
    pub map: SourceMap,
    pub changed: Vec<usize>,
    pub fn_count: usize,
    pub fn_lines: Vec<u32>,
    pub body_hashes: Vec<u64>,
    pub tables: Arc<ResolvedTables>,
    pub std_ranges: Vec<(u32, u32, ShippedCrate)>,
    pub std_routes: Vec<&'static StdFnDef>,
    pub std_methods: (u32, u32),
    /// Some edited body is a `const fn`'s that a const evaluation may
    /// run (see the module docs).
    pub const_fn: bool,
    /// Some edited const fn's result can reach const and static values
    /// only (`ConstReach::revaluable`): they must evaluate again.
    pub revalue: bool,
    /// The edited const fns (`Front::fn_loc` indexes).
    pub const_edits: Vec<usize>,
    /// With an item edit (path "item"): the new item scans, which the
    /// compile tail's slot update takes in signatures mode with
    /// `item_names` as the changed names.
    pub item_scans: Option<Vec<crate::scan::ItemScan>>,
    pub item_names: Vec<Sym>,
    /// The fns whose header an item edit replaced (`Front::fn_loc`
    /// indexes): only their heads moved (`compile::slot_update`).
    pub item_fns: Vec<usize>,
    /// A derive list or trait impl method edit came with it: the slot
    /// update runs in full mode.
    pub item_full: bool,
    /// Every edit is a derive list edit (no body or header edit): the
    /// compile tail may take the keyed dirty walk (sigedit P3.2).
    pub derive_only: bool,
    /// Files whose text changed, Ast nodes the patch built, bodies
    /// re-parsed, and spans moved.
    pub files: usize,
    pub nodes: usize,
    pub bodies: usize,
    pub spans: usize,
    /// Files read from disk to prove unchanged (a stat the patch could
    /// not trust), beyond the changed ones.
    pub reads: usize,
}

/// One edit proven to sit inside one fn body (`find_body_edit`), or
/// inside cfg-disabled code (`find_inactive_edit`, no `body`).
struct BodyEdit {
    file: FileId,
    text: String,
    edit: Edit,
    needs: (StdNeeds, bool),
    /// The new fn body; None when no Ast node changes.
    body: Option<NewBody>,
    /// The new fn or method, when the edit touches its header
    /// (`find_item_edit`); `body` is then None.
    item: Option<NewItem>,
    /// The new derive lists of a struct or enum (`find_derive_edit`).
    derive: Option<NewDerive>,
}

/// The derive side of a `BodyEdit` (sigedit P1.4): one top-level struct
/// or enum whose `#[derive(..)]` lists changed and nothing else.
struct NewDerive {
    item: usize,
    /// The item's new attributes (their derive lists are new, the rest
    /// token for token the old ones) and derive names, parsed at the new
    /// positions.
    attrs: Vec<crate::ast::Attr>,
    derives: Vec<(Sym, crate::diag::Span)>,
    /// The `derive` name.
    derive: Sym,
}


/// The item side of a `BodyEdit` (the item patch, sigedit P1.3): one
/// free fn or inherent method whose header changed and whose outline
/// (`item_outline.rs`) stands, parsed and rewritten whole.
struct NewItem {
    /// The fn's index in `Front::fn_loc` order and its location.
    fn_index: usize,
    item: usize,
    sub: Option<usize>,
    /// The old `stmt_items` indexes of the body's items, in parse order
    /// (`same_items`): each new one takes its old index.
    items: Vec<u32>,
    /// The old fn's byte range (its first attribute through its body).
    old: (u32, u32),
    /// The new fn, parsed and rewritten into an Ast of its own: a free
    /// fn's item, or a method inside a placeholder impl (`apply` takes
    /// the method and blanks the placeholder's self type).
    item_ast: Ast,
    /// The written name of a method, for the changed-name list.
    name: Sym,
    /// The old fn's expression range (`FnDef::exprs`).
    old_exprs: (u32, u32),
    /// The tail runs in full mode: a trait impl's method (operators,
    /// `for` loops and generic callers reach it without naming it,
    /// sigedit R10), or a const fn (const and static values that call
    /// it move, and the bodies that read them need not name it; R5).
    full: bool,
    /// The body's stored expansion at its new place, when the body is a
    /// user macro's unchanged one (`kept_body`; the next request's header
    /// edit of the same fn takes it from `PatchBase::kept_bodies`).
    kept: Option<KeptBody>,
}

/// The fn body side of a `BodyEdit`.
struct NewBody {
    /// The fn's index in `Front::fn_loc` order and its location.
    fn_index: usize,
    item: usize,
    sub: Option<usize>,
    /// The old body's byte range in the file.
    old_body: (u32, u32),
    /// The new body, parsed and rewritten into an Ast of its own
    /// (`apply` appends it to the merged Ast): its block and its
    /// expression and pattern ranges there.
    body_ast: Ast,
    body: BlockId,
    exprs: (u32, u32),
    pats: (u32, u32),
    /// Neither body holds a closure or a token collect's whole-Ast scans
    /// look for (`plain_body`).
    plain: bool,
    /// The old body's expression range (`FnDef::exprs`).
    old_exprs: (u32, u32),
    /// The old body's items (`same_items`), where the new body's go.
    items: Vec<u32>,
    /// The old body's impls in the module items, where the new body's go,
    /// and per new body item whether it is one (`SameItems`).
    impls: Vec<usize>,
    is_impl: Vec<bool>,
    /// The methods of those impls, in `Front::fn_loc` order.
    hoisted: Vec<usize>,
    /// The signature nodes copied ahead of the new body (`sig_nodes.rs`).
    sig: Option<super::sig_nodes::SigNodes>,
    /// The nested fn or body impl method whose own body the edit changed
    /// (`same_items`), in `Front::fn_loc` order.
    nested: Option<usize>,
    /// For a fn that returns `impl Trait`: the old body's raw hash, which
    /// its item scan folds in (`rescan_edited` proves the rest stands).
    rpit: Option<u64>,
}

/// A collected program kept for later requests (W-INCR3), one per mode
/// (`Front::kept`: check, build). It shares the front's merged Ast and
/// resolver tables (`Program::ast`, `Program::resolved`) until a body
/// patch detaches it; from then on every patch records its edits, until
/// `reuse_kept` moves its spans and takes it in place of a fresh collect
/// (when every edit allows it). Any other change to the Ast drops it.
pub(crate) struct KeptProgram {
    pub(crate) program: crate::check::collect::Program,
    /// The edits patches made since the program was detached, in order;
    /// None while the program shares the front's Ast.
    edits: Option<Vec<KeptEdit>>,
    bases: Vec<KeptBase>,
    /// Put back by `reuse_kept` after a header delta that failed with the
    /// program as it was: this request's collect may succeed and still give
    /// an error answer, and its program (whose callers hold error outputs,
    /// or no hidden type for an edited fn) would refuse the fix, so
    /// `keep_err` leaves this one in place. A clean answer's program
    /// replaces it (`keep`).
    prefer: bool,
    /// Templates whose last check in this program had errors (an error
    /// answer that kept it, `Front::template_recheck`): every later patch
    /// checks them again, as a collect would, until they pass.
    recheck: Vec<usize>,
}

impl PatchBase {
    /// Joins the `local_names` side thread now (a front image save: no
    /// thread may outlive the process that wrote the image).
    pub(crate) fn settle(&mut self) {
        if let Some(job) = self.local_names_job.take() {
            self.local_names = job.join().ok();
        }
    }

    /// The cfg environment and crate name a body of `module`'s crate
    /// expands under alone, if it may (`PatchBase::expand`).
    fn expand_env(&self, module: crate::ty::defs::ModuleId) -> Option<&(crate::resolve::cfg::CfgEnv, String)> {
        self.expand.get(&self.tables.root_of(module))
    }

    /// Probes the Ast once for the nodes that can hold another file's spans
    /// (`span_shift::probe_extras`) and sets `ranges` and `extras`, when the
    /// resolve could not prove ranges alone. The full resolve calls it while
    /// its Ast is not shared (compile.rs), so the first patch need not;
    /// `apply` calls it when that did not happen.
    pub(super) fn probe(&mut self, ast: &mut Ast, n_files: usize) {
        if self.ranges.is_none() {
            self.extras = Some(span_shift::probe_extras(ast, n_files));
            self.ranges = Some(span_shift::ranges_by_file(ast, n_files));
        }
    }
}

impl KeptProgram {
    /// True when every edit since the program was kept is a derive list
    /// edit (a program put back after a refused derive delta; the next
    /// derive delta then moves every key those edits can move).
    pub(crate) fn derive_edits_only(&self) -> bool {
        self.edits.as_ref().is_some_and(|e| !e.is_empty() && e.iter().all(|x| x.derive.is_some()))
    }
}

/// Drops the kept programs. The type store of the build mode's (else the
/// check mode's) seeds the next collect (`ty::TypePool`, B1-PLAN.md): every
/// place that drops kept programs comes here, so a session whose programs
/// do not ride to the next request (the chunk path, an image save that keeps
/// none) still starts its next collect from the last store.
pub(crate) fn drop_kept(front: &mut Front, caches: &mut Caches) {
    let [check, build] = std::mem::take(&mut front.kept);
    if let Some(k) = build.or(check) {
        pool_from(caches, k.program);
    }
}

/// `drop_kept` for each session whose kept programs do not ride in the front
/// image (`Front::image_keeps_kept`).
pub(crate) fn drop_unkept(sessions: &mut [Box<super::Session>]) {
    for s in sessions.iter_mut().filter(|s| !s.front.image_keeps_kept()) {
        let s = &mut **s;
        drop_kept(&mut s.front, &mut s.caches);
    }
}

/// `program`'s type store as the session's type pool (`ty::TypePool::of`).
fn pool_from(caches: &mut Caches, program: crate::check::collect::Program) {
    let interner = program.interner.clone();
    caches.gen_reuse.type_pool = crate::ty::TypePool::of(program.tys, program.krate, program.stable_crate, &interner);
}

/// Keeps `program` for later requests, in its mode's slot.
pub(crate) fn keep(front: &mut Front, mut program: crate::check::collect::Program) {
    let slot = usize::from(program.gx.walk_instances);
    // The request is done: every entry stored so far agrees with the
    // program (its collect stored or replayed it, `kept_delta`).
    program.reuse_stamp = crate::driver::gen_reuse::stamp_now();
    let recheck = std::mem::take(&mut front.template_recheck);
    front.kept[slot] = Some(KeptProgram { program, edits: None, bases: Vec::new(), prefer: false, recheck });
}

/// `keep` for a request that answers with errors: a program `reuse_kept`
/// put back (`KeptProgram::prefer`) stays. False when it stayed (the
/// caller gives the read sets that program's marks back).
pub(crate) fn keep_err(front: &mut Front, program: crate::check::collect::Program) -> bool {
    if front.kept[usize::from(program.gx.walk_instances)].as_ref().is_some_and(|k| k.prefer) {
        return false;
    }
    keep(front, program);
    true
}

/// One patch edit under a detached kept program.
#[derive(Clone)]
struct KeptEdit {
    edit: Edit,
    /// The fresh expansion contexts the Ast's span walk chose.
    ctxts: FxMap<u32, CtxtId>,
    /// The edited fn, in `Front::fn_loc` order (its `LocalDefId`); None
    /// for an edit inside cfg-disabled code.
    fn_index: Option<usize>,
    plain: bool,
    /// The body's items (`stmt_items` indexes; see `reuse_kept`).
    items: Vec<u32>,
    /// The nested fn or body impl method whose own body changed (`NewBody::nested`).
    nested: Option<usize>,
    /// The methods of the body's impls (`NewBody::hoisted`): new nodes, as
    /// the body items' (see `reuse_kept`).
    hoisted: Vec<usize>,
    /// The old body's expression range (a template's picks key on it).
    old_exprs: (u32, u32),
    /// The fn returns `impl Trait` (`reuse_kept` compares hidden types).
    rpit: bool,
    /// An item patch edit of the fn's header (`kept_delta::apply_headers`
    /// redoes it on the program).
    header: bool,
    /// A derive list edit of this struct or enum (its `ast.items` index):
    /// the derive delta applies it (driver/kept_derive.rs).
    derive: Option<usize>,
    /// The program's spans already moved for it (`reuse_kept` kept the
    /// program after a refused header delta).
    shifted: bool,
}

/// One edited fn's discovery output as the kept program was built with
/// it, taken at the fn's first edit since (`GenReuse::out_copy`); None
/// when the cache held none.
type KeptBase = (usize, Option<crate::driver::gen_reuse::OutCopy>);

/// Tries the body patch for this request (see the module docs). `root`
/// is the root file's text before any std splice. On `Err` the caller
/// resolves in full; the reason names the first condition that failed
/// (the `why=` of `lust-visits:`). `front.patch` is then cleared if the
/// patch had started to edit the front state.
pub(super) fn try_patch(
    front: &mut Front,
    caches: &mut Caches,
    inputs: u64,
    root: &str,
    request_start: SystemTime,
) -> Result<Patched, &'static str> {
    let (edits, reads) = find_edits(front, inputs, root, request_start)?;
    let edits_in: Vec<KeptEdit> = edits
        .iter()
        .map(|e| KeptEdit {
            edit: e.edit,
            ctxts: FxMap::default(),
            fn_index: e.body.as_ref().map(|b| b.fn_index).or(e.item.as_ref().map(|i| i.fn_index)),
            // A header edit counts as not plain: the delta needs user generics.
            plain: e.item.is_none() && e.body.as_ref().is_none_or(|b| b.plain),
            items: e.body.as_ref().map(|b| b.items.clone()).or_else(|| e.item.as_ref().map(|i| i.items.clone())).unwrap_or_default(),
            nested: e.body.as_ref().and_then(|b| b.nested),
            hoisted: e.body.as_ref().map_or_else(Vec::new, |b| b.hoisted.clone()),
            old_exprs: e.body.as_ref().map(|b| b.old_exprs).or(e.item.as_ref().map(|i| i.old_exprs)).unwrap_or((0, 0)),
            rpit: e.body.as_ref().is_some_and(|b| b.rpit.is_some()),
            header: e.item.is_some(),
            derive: e.derive.as_ref().map(|d| d.item),
            shifted: false,
        })
        .collect();
    // Everything above only read; from here the front state changes, and
    // a failure must drop the base so no later request patches on it.
    // A kept program that shares this Ast lets go of it and of the
    // resolver tables, so the patch edits both in place; it records the
    // edits (see `KeptProgram`). With no edit it stays as it is.
    let mut kept: [Option<KeptProgram>; 2] = if edits.is_empty() { Default::default() } else { std::mem::take(&mut front.kept) };
    for slot in &mut kept {
        *slot = slot.take().filter(|k| k.edits.is_some() || Arc::ptr_eq(&k.program.ast, &front.ast));
        if let Some(k) = slot {
            k.program.ast = Arc::default();
            k.program.resolved = None;
            let edits = k.edits.get_or_insert_with(Vec::new);
            // Each edited fn's discovery output as the program has it, the
            // nested fn whose body changed too (`reuse_kept` compares).
            for fn_index in edits_in.iter().flat_map(|e| e.fn_index.into_iter().chain(e.nested)) {
                if !edits.iter().any(|x| x.fn_index == Some(fn_index) || x.nested == Some(fn_index)) && !k.bases.iter().any(|b| b.0 == fn_index) {
                    let def = k.program.def_id(crate::def::LocalDefId(fn_index as u32));
                    k.bases.push((fn_index, caches.gen_reuse.out_copy(def)));
                }
            }
        }
    }
    // An item edit keeps the kept programs too: `reuse_kept` redoes its
    // headers (`kept_delta::apply_headers`) or the tail collects.
    let mut ctxts: Vec<FxMap<u32, CtxtId>> = Vec::new();
    let out = apply(front, caches, edits, reads, &mut ctxts);
    if out.is_err() {
        front.patch = None;
    } else {
        for (slot, k) in kept.into_iter().enumerate() {
            if let Some(mut k) = k {
                let new = edits_in.iter().zip(&ctxts).map(|(e, c)| KeptEdit { ctxts: c.clone(), ..e.clone() });
                k.edits.get_or_insert_with(Vec::new).extend(new);
                front.kept[slot] = Some(k);
            }
        }
    }
    out
}

/// The changed files and the body each edit sits in, with the number of
/// unchanged files read from disk because their stat was not trusted,
/// or why some edit is not a provable body edit. Reads only.
fn find_edits(front: &mut Front, inputs: u64, root: &str, request_start: SystemTime) -> Result<(Vec<BodyEdit>, usize), &'static str> {
    // The side thread's share of the tables ends with it.
    if let Some(b) = front.patch.as_mut()
        && let Some(job) = b.local_names_job.take()
    {
        b.local_names = job.join().ok();
    }
    let base = front.patch.as_ref().ok_or("no base")?;
    if base.inputs != inputs {
        return Err("inputs");
    }
    // The tables are this base's own, or shared with the kept program only.
    let kept_tables = front.kept.iter().flatten().filter(|k| k.program.resolved.as_ref().is_some_and(|t| Arc::ptr_eq(t, &base.tables))).count();
    if front.env_hash.is_none() || front.chunks.len() != 1 || Arc::strong_count(&base.tables) != 1 + kept_tables {
        return Err("state");
    }
    if front.ast.exprs.len() > base.arena_base.saturating_mul(2) + 65_536 {
        return Err("arena");
    }
    let deps = &front.chunks[0].expand_deps;
    if deps.iter().any(|d| matches!(d, crate::expand::Dep::Position)) || crate::expand::deps_stale(deps, &front.client) {
        return Err("expansion inputs");
    }
    let mut changed: Vec<(FileId, String)> = Vec::new();
    if root != base.root_unspliced {
        // The std splice follows the root text in file 0. It stands while
        // the std needs do (checked below), so the new file text is the
        // new root text and the same splice.
        let text = match splice_of(front, base) {
            Some(splice) => format!("{root}{splice}"),
            None if base.spliced => return Err("spliced root"),
            None => root.to_string(),
        };
        changed.push((FileId(0), text));
    }
    let mut fresh_stamps: Vec<(usize, Option<Stamp>)> = Vec::new();
    let mut reads = 0usize;
    for k in 1..front.map.file_count() {
        let file = FileId(k as u32);
        let path = front.map.path(file);
        if path.is_empty() {
            continue;
        }
        // An overlay text (`lust test`'s harness shims) can change while its file's stamp
        // stands: the shims of a module name the tests of the modules below it. Compare it.
        if let Some(text) = crate::driver::overlay_text(std::path::Path::new(path)) {
            if front.map.text(file) != Some(text.as_str()) {
                changed.push((file, text));
            }
            continue;
        }
        let md = std::fs::metadata(path).map_err(|_| "file gone")?;
        if let (Some(st), Ok(mtime)) = (base.stamps.get(k).copied().flatten(), md.modified())
            && st == (Stamp { mtime, len: md.len() })
        {
            continue;
        }
        let text = std::fs::read_to_string(path).map_err(|_| "file gone")?;
        if front.map.text(file) == Some(text.as_str()) {
            reads += 1;
            fresh_stamps.push((k, stamp_of(path, request_start)));
            continue;
        }
        changed.push((file, text));
    }
    // Each `mod name;` stands while the file it did not take stays absent
    // (`ResolvedTables::module_alts`): with both, a cold resolve rejects it.
    if base.tables.module_alts.iter().any(|p| p.is_file()) {
        return Err("module file added");
    }
    if !changed.is_empty() {
        let base = front.patch.as_mut().ok_or("no base")?;
        if base.local_names.is_none() {
            base.local_names = Some(base.tables.local_named_set());
        }
    }
    let mut edits = Vec::with_capacity(changed.len());
    for (file, text) in changed {
        let old = front.map.text(file).ok_or("no text")?;
        let (p, s) = super::compile::common_ends(old.as_bytes(), text.as_bytes());
        let edit = Edit { file, a: p as u32, b: (old.len() - s) as u32, d: text.len() as i64 - old.len() as i64 };
        let (body, item, derive) = match find_body_edit(front, &text, edit) {
            Ok(body) => (Some(body), None, None),
            // No fn body holds the edit: it may sit in a fn's header (the
            // item patch), in a derive list, or in code the expander dropped.
            Err(why @ ("not in a fn body" | "no active item")) => match find_item_edit(front, &text, edit) {
                Ok(item) => (None, Some(item), None),
                Err(Some(item_why)) => return Err(item_why),
                Err(None) => match find_derive_edit(front, &text, edit) {
                    Ok(derive) => (None, None, Some(derive)),
                    Err(Some(derive_why)) => return Err(derive_why),
                    Err(None) => {
                        find_inactive_edit(front, &text, edit).map_err(|inactive| inactive.unwrap_or(why))?;
                        (None, None, None)
                    }
                },
            },
            Err(why) => return Err(why),
        };
        // The root's own needs: its text before the splice.
        let own = if file == FileId(0) { splice_of(front, front.patch.as_ref().ok_or("no base")?).map_or(text.len(), |sp| text.len() - sp.len()) } else { text.len() };
        edits.push(BodyEdit { file, needs: file_needs(&text[..own]), text, edit, body, item, derive });
    }
    // The std splice and the platform crate follow every file's needs;
    // they stand when the union over files does. The new union folds
    // the edits over the base needs in place, no copy of the table.
    let base = front.patch.as_ref().ok_or("no base")?;
    let fold = |(a, p): (StdNeeds, bool), (n, q): (StdNeeds, bool)| {
        (StdNeeds { fns: a.fns || n.fns, methods: a.methods || n.methods, modules: a.modules | n.modules }, p || q)
    };
    let old_union = base.needs.iter().copied().fold((StdNeeds::default(), false), fold);
    let new_union = base
        .needs
        .iter()
        .enumerate()
        .map(|(k, &n)| edits.iter().find(|e| e.file.0 as usize == k).map_or(n, |e| e.needs))
        .fold((StdNeeds::default(), false), fold);
    if new_union != old_union {
        return Err("std needs");
    }
    if edits.len() > 1 && edits.iter().any(|e| e.item.as_ref().is_some_and(|i| i.kept.is_some())) {
        return Err("item: body macro");
    }
    let base = front.patch.as_mut().ok_or("no base")?;
    for (k, st) in fresh_stamps {
        base.stamps[k] = st;
    }
    Ok((edits, reads))
}

/// The std splice text after the root text in file 0, when the base
/// spliced one and the file still starts with the root text it read.
fn splice_of<'a>(front: &'a Front, base: &PatchBase) -> Option<&'a str> {
    if !base.spliced {
        return None;
    }
    front.map.text(FileId(0))?.strip_prefix(base.root_unspliced.as_str())
}

/// Proves that `edit` (the map's text of its file to `text`) sits
/// strictly inside one top-level fn or method body, and lexes, parses,
/// and rewrites the new body.
fn find_body_edit(front: &Front, text: &str, edit: Edit) -> Result<NewBody, &'static str> {
    let base = front.patch.as_ref().ok_or("no base")?;
    let file = edit.file;
    let old = front.map.text(file).ok_or("no text")?;
    let (a, b, d) = (edit.a as usize, edit.b as usize, edit.d);
    let ast = &front.ast;
    let (fn_index, &(item, sub)) = front
        .fn_loc
        .iter()
        .enumerate()
        .find(|&(_, &(item, sub))| {
            item != usize::MAX && {
                let def = fn_def_at(ast, item, sub);
                def.body.is_some_and(|bl| {
                    let sp = ast.blocks[bl.0 as usize].span;
                    sp.file == file && (sp.lo as usize) < a && b < sp.hi as usize
                })
            }
        })
        .ok_or_else(|| outside_fn_reason(ast, file, a, b))?;
    let def = fn_def_at(ast, item, sub);
    let rpit = def.ret.is_some_and(|t| matches!(ast.ty(t), TyExpr::ImplTrait { .. })).then(|| super::ast_hash::body_scan(ast, def, None).0);
    if !matches!(ast.items[item].kind, ItemKind::Fn(_) | ItemKind::Impl(_)) {
        return Err("not in a fn body");
    }
    // A hoisted body impl's method resolves with its block's items; the
    // body rewrite here sees module scope only.
    if matches!(&ast.items[item].kind, ItemKind::Impl(imp) if imp.in_body) {
        return Err("body impl");
    }
    let span = ast.blocks[def.body.ok_or("not in a fn body")?.0 as usize].span;
    // A fn's expression and pattern ranges (`FnDef::exprs`, closure
    // numbering reads them) start at its first parameter: parameter
    // patterns and expressions in the signature's types sit there, before
    // the body's nodes. They move ahead of the new body (`sig_nodes.rs`),
    // in the new body's own Ast from index 0, so the ranges keep the cold
    // shape.
    let mut body_ast = Ast::default();
    let sig = super::sig_nodes::copy(ast, def, span, &mut body_ast)?;
    let (lo, hi) = (span.lo as usize, span.hi as usize);
    let new_hi = (hi as i64 + d) as usize;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, lo as u32, &front.interner).ok().filter(balanced)).ok_or("body lex");
    let (old_body, new_body) = (lex(old.get(lo..hi))?, lex(text.get(lo..new_hi))?);
    let (old_ok, new_ok) = (body_tokens_ok(&old_body, lo, hi, &front.interner), body_tokens_ok(&new_body, lo, new_hi, &front.interner));
    // A user macro (or a builtin that is not pure) is the last reason:
    // any other refusal of either body wins.
    for r in [&old_ok, &new_ok] {
        if let Err(why) = r
            && *why != "body macro"
        {
            return Err(why);
        }
    }
    // Parse and rewrite the new body on its own: an error there (a
    // half-typed edit) gives up before any state changes, so the base
    // stands for the next request. Its pure builtin macros expand first,
    // and a static's init closure hoists into a hidden fn, as the
    // resolver's token passes do. A body with other macros takes its
    // expansion from its whole file's (`expand_by_file`).
    let module = *base.tables.fn_module.get(fn_index).ok_or("state")?;
    let raw = lexer::Lexed { tokens: new_body.tokens.clone(), strings: new_body.strings.clone() };
    let hoisted = match (old_ok, new_ok) {
        (Ok((old_calls, old_pure)), Ok((new_calls, new_pure))) => {
            if (old_calls || new_calls) && base.shadowed || (old_pure || new_pure) && base.expand_env(module).is_none() {
                return Err("macro in body");
            }
            match new_pure {
                true => expand_pure(front, base, file, text, module, raw)?,
                false => crate::expand::lazy::hoist_static_closures(raw, &front.interner),
            }
        }
        _ => expand_by_file(front, base, text, edit, (lo as u32, new_hi as u32), &raw)?,
    };
    let toks = &hoisted.tokens[..hoisted.tokens.len() - 1];
    // A whole parse seeds each nested fn's attributes with the enclosing
    // scopes' `allow`s: for a top-level fn, its attributes after its
    // item's own. A method's own attributes are not kept apart, so a
    // method with attributes and a nested fn resolves in full.
    let seed: &[crate::ast::Attr] = match sub {
        None => def.attrs.get(ast.items[item].attrs.len()..).unwrap_or(&[]),
        Some(_) => &[],
    };
    let nested_fn = |t: &[lexer::Token]| t.windows(2).any(|w| w[0].tok == Tok::Fn && matches!(w[1].tok, Tok::Ident(_)));
    if sub.is_some() && !def.attrs.is_empty() && (nested_fn(&old_body.tokens) || nested_fn(&new_body.tokens)) {
        return Err("body items");
    }
    let (body, mut exprs, mut pats) =
        crate::parser::parse_body_seeded(toks, &hoisted.strings, &mut body_ast, &front.interner, &front.known, seed)
            .map_err(|_| "body parse")?;
    let same = same_items(ast, old, text, (item, span), &body_ast, (&old_body.tokens, &new_body.tokens), edit)?;
    let nested = match same.inner {
        Some(loc) => Some(front.fn_loc.iter().position(|&l| l == loc).ok_or("body items")?),
        None => None,
    };
    // The methods of the body's impls (`Front::fn_loc` order): they fold the
    // holder's content into their body hashes (`ast_hash::assemble`).
    let impl_fns: Vec<usize> = match same.impls.is_empty() {
        true => Vec::new(),
        false => front.fn_loc.iter().enumerate().filter(|(_, l)| same.impls.contains(&l.0)).map(|(j, _)| j).collect(),
    };
    let mut scratch = def.clone();
    scratch.body = Some(body);
    if let Some(sig) = &sig {
        (exprs.0, pats.0) = (0, 0);
        for p in &mut scratch.params {
            p.pat = p.pat.map(|q| sig.pat(q));
        }
    }
    let outer = match &ast.items[item].kind {
        ItemKind::Impl(imp) => Some(&imp.generics),
        _ => None,
    };
    let diags = crate::resolve::worklist::rewrite_fn_body(
        &base.tables,
        &front.interner,
        base.local_names.as_ref().ok_or("state")?,
        moved_splice_lo(base, edit),
        &mut body_ast,
        &scratch,
        outer,
        module,
    );
    if !diags.is_empty() {
        return Err("body rewrite");
    }
    let old_closures = ast.exprs[def.exprs.0 as usize..def.exprs.1 as usize].iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let new_closures = body_ast.exprs.iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let plain = !old_closures
        && !new_closures
        && plain_body(&old_body, &front.interner)
        && plain_body(&new_body, &front.interner)
        && plain_body(&hoisted, &front.interner);
    let SameItems { items, impls, is_impl, .. } = same;
    Ok(NewBody { fn_index, item, sub, old_body: (span.lo, span.hi), body_ast, body, exprs, pats, plain, old_exprs: def.exprs, items, impls, is_impl, hoisted: impl_fns, sig, nested, rpit })
}

/// The byte range of one top-level fn or method: from its first token
/// (attributes and doc comments included) through its body. A method's
/// start is the first token after the member before it in its impl.
fn fn_range(ast: &Ast, item: usize, sub: Option<usize>, old: &str, interner: &crate::intern::Interner) -> Option<(u32, u32)> {
    let it = &ast.items[item];
    let def = fn_def_at(ast, item, sub);
    let hi = ast.blocks[def.body?.0 as usize].span.hi;
    let Some(_) = sub else { return Some((it.span.lo, hi)) };
    let lexed = lexer::lex(old.get(it.span.lo as usize..it.span.hi as usize)?, it.span.file, it.span.lo, interner).ok()?;
    let name = lexed.tokens.iter().position(|t| t.span == def.name_span)?;
    // Walk back to the boundary at the impl's own depth: its `{`, the
    // end of the member before (`}` or `;`).
    let mut depth = 0i32;
    for k in (0..name).rev() {
        match lexed.tokens[k].tok {
            Tok::RBrace | Tok::RParen | Tok::RBracket => depth += 1,
            Tok::LBrace | Tok::LParen | Tok::LBracket if depth > 0 => depth -= 1,
            Tok::LBrace => return Some((lexed.tokens[k + 1].span.lo, hi)),
            Tok::Semi if depth == 0 => return Some((lexed.tokens[k + 1].span.lo, hi)),
            _ => {}
        }
        if depth == 1 && lexed.tokens[k].tok == Tok::RBrace {
            // The previous member's body ends here.
            return Some((lexed.tokens[k + 1].span.lo, hi));
        }
    }
    None
}

/// The derive-list patch (sigedit P1.4): proves that `edit` changes only
/// the names inside the `#[derive(..)]` lists of one top-level struct or
/// enum (the item's other tokens stand, so its outline does; resolve
/// never reads derive lists), and parses the item's new attributes.
/// `Err(None)` when no struct or enum holds the edit.
fn find_derive_edit(front: &Front, text: &str, edit: Edit) -> Result<NewDerive, Option<&'static str>> {
    let file = edit.file;
    let old = front.map.text(file).ok_or(Some("no text"))?;
    let ast = &front.ast;
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let item = ast
        .items
        .iter()
        .position(|it| {
            let adt = matches!(it.kind, ItemKind::Struct(_) | ItemKind::Enum(_));
            adt && it.span.file == file && it.span.ctxt == CtxtId::ROOT && it.span.lo < a && b < it.span.hi
        })
        .ok_or(None)?;
    let (lo, hi) = (ast.items[item].span.lo, ast.items[item].span.hi);
    let new_hi = (hi as i64 + d) as u32;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, lo, &front.interner).ok().filter(balanced)).ok_or(Some("derive lex"));
    let (old_lx, new_lx) = (lex(old.get(lo as usize..hi as usize))?, lex(text.get(lo as usize..new_hi as usize))?);
    let (ot, nt) = (&old_lx.tokens[..old_lx.tokens.len() - 1], &new_lx.tokens[..new_lx.tokens.len() - 1]);
    if nt.first().is_none_or(|t| t.span.lo != lo) || nt.last().is_none_or(|t| t.span.hi != new_hi) {
        return Err(Some("derive lex"));
    }
    // Each version's tokens with the derive lists' contents taken out;
    // the contents may hold names, `,` and `::` only.
    let derive = front.interner.intern("derive");
    let outline = |toks: &[lexer::Token], t: &str| -> Option<Vec<String>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < toks.len() {
            let tok = &toks[i];
            out.push(t.get(tok.span.lo as usize..tok.span.hi as usize)?.to_owned());
            let opens = i >= 2
                && toks[i - 2].tok == Tok::LBracket
                && toks[i - 1].tok == Tok::Ident(derive)
                && tok.tok == Tok::LParen
                && toks.get(i.wrapping_sub(3)).is_some_and(|t| t.tok == Tok::Pound);
            i += 1;
            if opens {
                while i < toks.len() && toks[i].tok != Tok::RParen {
                    if !matches!(toks[i].tok, Tok::Ident(_) | Tok::Comma | Tok::PathSep) {
                        return None;
                    }
                    i += 1;
                }
            }
        }
        Some(out)
    };
    match (outline(ot, old), outline(nt, text)) {
        (Some(x), Some(y)) if x == y => {}
        (Some(_), Some(_)) => return Err(Some("derive: outline")),
        _ => return Err(Some("derive: tokens")),
    }
    if crate::expand::needs_expansion(nt, &front.interner) || nt.iter().any(|t| matches!(t.tok, Tok::Bang | Tok::Dollar)) {
        return Err(Some("derive: attrs"));
    }
    let mut toks = nt.to_vec();
    toks.push(lexer::Token { tok: Tok::Eof, span: crate::diag::Span { file, lo: new_hi, hi: new_hi, ctxt: CtxtId::ROOT } });
    let lexed = lexer::Lexed { tokens: toks, strings: new_lx.strings.clone() };
    let mut parsed =
        crate::parser::parse_items(&lexed, 0..lexed.tokens.len(), &front.interner, &front.known).map_err(|_| Some("derive parse"))?;
    let it = parsed.items.pop().filter(|_| parsed.items.is_empty()).ok_or(Some("derive parse"))?;
    // The derive attributes hold names only (no node of the parse's Ast).
    let is_derive = |x: &crate::ast::Attr| x.path.len() == 1 && x.path[0].name == derive;
    let names_only = |x: &crate::ast::Attr| match &x.input {
        crate::ast::AttrInput::List(_, trees) => trees.iter().all(|t| matches!(t, lexer::TokenTree::Token(_))),
        _ => false,
    };
    if it.attrs.iter().any(|x| is_derive(x) && !names_only(x)) {
        return Err(Some("derive: attrs"));
    }
    let derives = match it.kind {
        ItemKind::Struct(s) => s.derives,
        ItemKind::Enum(e) => e.derives,
        _ => return Err(Some("derive parse")),
    };
    Ok(NewDerive { item, attrs: it.attrs, derives, derive })
}

/// The item patch (sigedit P1.3): proves that `edit` sits strictly
/// inside one free fn or method, touches its header, and
/// leaves its outline (`item_outline::fn_outline`) as it was, then
/// parses and rewrites the new fn whole against the frozen tables.
/// `Err(None)` when no fn holds the edit; `Err(Some(why))` when one
/// does but the patch cannot prove the edit (the caller resolves).
/// Refused (R2, R5, and v1 limits): a header with a macro call, `$`,
/// an attribute after `fn`, or an APIT list that changed (the same list
/// keeps collect's synthetic params); attributes the expander acts on;
/// a body that needs more than pure builtin macros, or holds items; a fn
/// from a macro expansion. A trait impl's method and a const fn take the patch
/// with `NewItem::full`.
fn find_item_edit(front: &Front, text: &str, edit: Edit) -> Result<NewItem, Option<&'static str>> {
    let base = front.patch.as_ref().ok_or(Some("no base"))?;
    let file = edit.file;
    let old = front.map.text(file).ok_or(Some("no text"))?;
    let ast = &front.ast;
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let holds = |&(item, sub): &(usize, Option<usize>)| {
        if item == usize::MAX || item >= ast.items.len() || ast.items[item].span.file != file {
            return false;
        }
        let it = &ast.items[item];
        let in_item = it.span.lo < a && b < it.span.hi;
        in_item && matches!((&it.kind, sub), (ItemKind::Fn(_), None) | (ItemKind::Impl(_), Some(_)))
    };
    // The item that holds the edit, then the fn in it.
    let cands: Vec<(usize, (usize, Option<usize>))> = front.fn_loc.iter().copied().enumerate().filter(|(_, l)| holds(l)).collect();
    let mut found = None;
    let root = |s: crate::diag::Span| s.ctxt == CtxtId::ROOT && s.file == file;
    for (fn_index, (item, sub)) in cands {
        // A method an impl-level macro call made has no written range of
        // its own; an edit in that call is in no written fn.
        let def = fn_def_at(ast, item, sub);
        if !root(def.name_span) || !def.body.is_some_and(|bl| root(ast.blocks[bl.0 as usize].span)) {
            continue;
        }
        let (lo, hi) = fn_range(ast, item, sub, old, &front.interner).ok_or(Some("item range"))?;
        if lo < a && b < hi {
            found = Some((fn_index, item, sub, lo, hi));
            break;
        }
    }
    let (fn_index, item, sub, lo, hi) = found.ok_or(None)?;
    if matches!(&ast.items[item].kind, ItemKind::Impl(imp) if imp.in_body) {
        return Err(Some("item: body impl"));
    }
    let def = fn_def_at(ast, item, sub);
    // The outline holds the qualifiers, so the new fn is const too.
    let full = def.qual.is_const || matches!(&ast.items[item].kind, ItemKind::Impl(imp) if imp.trait_ref.is_some());
    // Body items in the old fn: the header edit keeps them when the body's
    // text stands (checked below, and `same_items` after the parse).
    let has_items = ast.stmt_items.iter().any(|it| it.span.file == file && lo <= it.span.lo && it.span.hi <= hi);
    let new_hi = (hi as i64 + d) as u32;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, lo, &front.interner).ok().filter(balanced)).ok_or(Some("item lex"));
    let (old_lx, new_lx) = (lex(old.get(lo as usize..hi as usize))?, lex(text.get(lo as usize..new_hi as usize))?);
    let (ot, nt) = (&old_lx.tokens[..old_lx.tokens.len() - 1], &new_lx.tokens[..new_lx.tokens.len() - 1]);
    // The new range starts and ends on a token edge, so no text outside
    // it lexes another way (the edit is strictly inside).
    if nt.first().is_none_or(|t| t.span.lo != lo) || nt.last().is_none_or(|t| t.span.hi != new_hi || t.tok != Tok::RBrace) {
        return Err(Some("item lex"));
    }
    let outline = |toks: &[lexer::Token], t: &str| super::item_outline::fn_outline(toks, t);
    match (outline(ot, old), outline(nt, text)) {
        (Some(x), Some(y)) if x == y => {}
        (Some(_), Some(_)) => return Err(Some("item: outline")),
        _ => return Err(Some("item: header macro")),
    }
    // Header checks: from `fn` to the body's `{` at depth 0.
    let open = |toks: &[lexer::Token]| {
        let mut depth = 0i32;
        toks.iter().position(|t| {
            match t.tok {
                Tok::LParen | Tok::LBracket => depth += 1,
                Tok::RParen | Tok::RBracket => depth -= 1,
                _ => {}
            }
            depth == 0 && t.tok == Tok::LBrace
        })
    };
    let (oo, no) = (open(ot).ok_or(Some("item lex"))?, open(nt).ok_or(Some("item lex"))?);
    let at_fn = nt.iter().position(|t| t.tok == Tok::Fn).ok_or(Some("item lex"))?;
    if nt[at_fn..no].iter().any(|t| matches!(t.tok, Tok::Pound | Tok::DocStr(_))) {
        return Err(Some("item: header"));
    }
    // APITs stand: collect lowers them to the same synthetic params.
    let apits = |toks: &[lexer::Token], t: &str| super::item_outline::apit_params(toks, t);
    match (apits(&ot[..=oo], old), apits(&nt[..=no], text)) {
        (Some(x), Some(y)) if x == y => {}
        _ => return Err(Some("item: apit")),
    }
    if crate::expand::needs_expansion(&nt[..no], &front.interner) {
        return Err(Some("item: attrs"));
    }
    // The body: the body patch's token rules, and no expander work.
    let body_lx = |lx: &lexer::Lexed, k: usize| lexer::Lexed { tokens: lx.tokens[k..].to_vec(), strings: lx.strings.clone() };
    let (ob, nb) = (body_lx(&old_lx, oo), body_lx(&new_lx, no));
    // For `same_items` after the parse (the expander takes `nb`).
    let nb_tokens = if has_items { nb.tokens.clone() } else { Vec::new() };
    // A body with pure builtin macros or attributes expands as the body
    // patch's does (`expand_pure`). A body the patch cannot expand alone
    // (a user macro) takes its stored expansion when its text stands.
    let same_body = old.get(ot[oo].span.lo as usize..hi as usize) == text.get(nt[no].span.lo as usize..new_hi as usize);
    // A method's attributes seed its nested fns' (see `NewBody`); body
    // items also need their body as it was.
    if has_items && (!same_body || sub.is_some() && !def.attrs.is_empty()) {
        return Err(Some("item: body items"));
    }
    let module = *base.tables.fn_module.get(fn_index).ok_or(Some("state"))?;
    let plain = body_tokens_ok(&ob, ot[oo].span.lo as usize, hi as usize, &front.interner).and_then(|(oc, op)| {
        let (nc, np) = body_tokens_ok(&nb, nt[no].span.lo as usize, new_hi as usize, &front.interner)?;
        if (oc || nc) && base.shadowed || (op || np) && base.expand_env(module).is_none() { Err("item: body macro") } else { Ok(np) }
    });
    let kept = match plain {
        Err("body macro" | "item: body macro") if same_body => Some(kept_body(front, base, fn_index, edit, (ot[oo].span.lo, hi)).map_err(Some)?),
        Err(why) => return Err(Some(why)),
        Ok(_) => None,
    };
    // Parse: a free fn as an item, a method inside a placeholder impl.
    let mut toks: Vec<lexer::Token> = Vec::with_capacity(nt.len() + 5);
    let edge = crate::diag::Span { file, lo, hi: lo, ctxt: CtxtId::ROOT };
    let placeholder = front.interner.intern("__LustItemPatch");
    if sub.is_some() {
        for tok in [Tok::Impl, Tok::Ident(placeholder), Tok::LBrace] {
            toks.push(lexer::Token { tok, span: edge });
        }
    }
    // The expander keeps the input's string table and appends to it, so
    // the header's tokens index the expanded strings as before.
    let (body, strings) = match (&kept, plain) {
        (Some(k), _) => {
            // The body's strings follow the header's.
            let off = new_lx.strings.len() as u32;
            let mut toks = k.tokens.clone();
            toks.iter_mut().for_each(|t| t.tok.shift_strings(off));
            (toks, new_lx.strings.iter().chain(&k.strings).cloned().collect())
        }
        (None, Ok(true)) => {
            let out = expand_pure(front, base, file, text, module, nb).map_err(Some)?;
            (out.tokens[..out.tokens.len() - 1].to_vec(), out.strings)
        }
        // A static's init closure hoists into a hidden fn, as the body
        // patch's tokens do (both are body items, `same_items`).
        _ => {
            let out = crate::expand::lazy::hoist_static_closures(nb, &front.interner);
            (out.tokens[..out.tokens.len() - 1].to_vec(), out.strings)
        }
    };
    toks.extend_from_slice(&nt[..no]);
    toks.extend(body);
    if sub.is_some() {
        toks.push(lexer::Token { tok: Tok::RBrace, span: crate::diag::Span { lo: new_hi, hi: new_hi, ..edge } });
    }
    toks.push(lexer::Token { tok: Tok::Eof, span: crate::diag::Span { lo: new_hi, hi: new_hi, ..edge } });
    let lexed = lexer::Lexed { tokens: toks, strings };
    let mut item_ast =
        crate::parser::parse_items(&lexed, 0..lexed.tokens.len(), &front.interner, &front.known).map_err(|_| Some("item parse"))?;
    if item_ast.items.len() != 1 || item_ast.stmt_items.is_empty() == has_items || !item_ast.inner_attrs.is_empty() {
        return Err(Some("item: body items"));
    }
    // The body's items are the old ones at their moved places, each takes
    // its old index (`same_items`, as the body patch's); no body impl.
    let items = match has_items {
        true => {
            let span = ast.blocks[def.body.ok_or(Some("item range"))?.0 as usize].span;
            let same = same_items(ast, old, text, (item, span), &item_ast, (&ob.tokens, &nb_tokens), edit).map_err(Some)?;
            if same.inner.is_some() || !same.impls.is_empty() || same.is_impl.iter().any(|&i| i) {
                return Err(Some("item: body items"));
            }
            same.items
        }
        false => Vec::new(),
    };
    // The new fn takes the old one's flat name and the scope's allows
    // the whole parse seeded after its own attributes.
    let own_old = match sub {
        None => ast.items[item].attrs.len(),
        Some(_) => 0,
    };
    let mut new_item = item_ast.items.pop().ok_or(Some("item parse"))?;
    let name;
    {
        let new_def: &mut FnDef = match (&mut new_item.kind, sub) {
            (ItemKind::Fn(f), None) => f,
            (ItemKind::Impl(imp), Some(_)) if imp.fns.len() == 1 && imp.consts.is_empty() && imp.types.is_empty() => &mut imp.fns[0],
            _ => return Err(Some("item parse")),
        };
        name = new_def.name;
        let own = if sub.is_some() { new_def.attrs.len() } else { own_old };
        if own > def.attrs.len() || sub.is_none() && new_item.attrs.len() != own_old {
            return Err(Some("item: attrs"));
        }
        // A free fn's parse seeded its own allows after its attributes;
        // the old fn's tail holds the scope's and those, in cold order.
        new_def.attrs.truncate(own);
        new_def.attrs.extend_from_slice(&def.attrs[own..]);
        new_def.name = def.name;
        let outer = match &ast.items[item].kind {
            ItemKind::Impl(imp) => Some(&imp.generics),
            _ => None,
        };
        let mut scratch = std::mem::replace(new_def, def.clone());
        let diags = crate::resolve::worklist::rewrite_fn_item(
            &base.tables,
            &front.interner,
            base.local_names.as_ref().ok_or(Some("state"))?,
            moved_splice_lo(base, edit),
            &mut item_ast,
            &mut scratch,
            outer,
            module,
        );
        if !diags.is_empty() {
            return Err(Some("item rewrite"));
        }
        *new_def = scratch;
    }
    item_ast.items.push(new_item);
    let old_exprs = def.exprs;
    let kept = kept.map(|body| KeptBody { fn_index, file, span: (nt[no].span.lo, new_hi), body });
    Ok(NewItem { fn_index, item, sub, old: (lo, hi), item_ast, name, old_exprs, full, kept, items })
}

/// Where the std splice starts in the new text: the new body or fn is
/// lexed at its new positions, and the rewrite tells std code from user
/// code by this offset. An edit in the root file before the splice moves
/// it (a fn just before the splice grew past the old offset, and its
/// paths rewrote as std code: the patch oracle found it on tsrust-all4).
fn moved_splice_lo(base: &PatchBase, edit: Edit) -> Option<u32> {
    base.tables.std_splice_lo.map(|lo| if edit.file == FileId(0) && lo >= edit.b { (lo as i64 + edit.d) as u32 } else { lo })
}

/// The old fn body's items matched to the new body's (`same_items`).
struct SameItems {
    /// The old `stmt_items` indexes of the new body's items that stay
    /// body items, in parse order: each new one takes its old index.
    items: Vec<u32>,
    /// The `ast.items` indexes of the old body's impls, which flatten
    /// hoisted to the module items (`ImplDef::in_body`), in parse order:
    /// each new body impl takes its old item's place.
    impls: Vec<usize>,
    /// Per new body item (`body_ast.stmt_items` order): true for an impl.
    is_impl: Vec<bool>,
    /// The fn whose own body the edit changed, as a `Front::fn_loc` entry:
    /// a nested fn (`(usize::MAX, Some(stmt index))`) or a method of a body
    /// impl (`(item, Some(method))`).
    inner: Option<(usize, Option<usize>)>,
}

/// The items of the old fn body at `span` (the body of `ast.items[item]`),
/// when the new body (`body_ast`, parsed from `text`) holds the same ones:
/// as many of each kind, each with the same source text at its old place
/// moved by the edit, and in the changed tokens of the body (`toks`: old
/// and new) no brace, or only braces that close among them where no item
/// overlaps them, so each item sits in the same block as before and sees
/// the same items and `use`s. Resolve and collect then make the same
/// defs of them, with the same indexes once `apply` puts each new item at
/// its old index. The body's impls sit in the module items after `item`
/// (flatten hoists them); the new body's take their places.
/// One exception (`SameItems::inner`): an edit strictly inside the body of
/// a nested fn or of a body impl's method, where that body holds no item,
/// changes that fn's body only (the item's text before the body's brace
/// stands, its end moves by the edit). Braces may change there: no item
/// sits in that body, and every other item still matches its text.
fn same_items(
    ast: &Ast,
    old: &str,
    text: &str,
    (item, span): (usize, crate::diag::Span),
    body_ast: &Ast,
    toks: (&[lexer::Token], &[lexer::Token]),
    edit: Edit,
) -> Result<SameItems, &'static str> {
    let inside = |s: crate::diag::Span| s.file == span.file && span.lo <= s.lo && s.hi <= span.hi;
    let olds: Vec<u32> = (0..ast.stmt_items.len() as u32).filter(|&i| inside(ast.stmt_items[i as usize].span)).collect();
    let hoisted = |it: &crate::ast::Item| matches!(&it.kind, ItemKind::Impl(imp) if imp.in_body);
    let impls: Vec<usize> = (item + 1..ast.items.len()).take_while(|&i| hoisted(&ast.items[i]) && inside(ast.items[i].span)).collect();
    let is_impl: Vec<bool> = body_ast.stmt_items.iter().map(|it| matches!(it.kind, ItemKind::Impl(_))).collect();
    // A body impl that flatten keeps in the body (one a macro made) is L0820 there.
    let root = |it: &crate::ast::Item| it.span.ctxt == CtxtId::ROOT;
    if olds.iter().any(|&i| matches!(ast.stmt_items[i as usize].kind, ItemKind::Impl(_)))
        || body_ast.stmt_items.iter().zip(&is_impl).any(|(it, &imp)| imp && !root(it))
    {
        return Err("body items");
    }
    let n_impls = is_impl.iter().filter(|&&x| x).count();
    if olds.len() + impls.len() != body_ast.stmt_items.len() || impls.len() != n_impls {
        return Err("body items");
    }
    if olds.is_empty() && impls.is_empty() {
        return Ok(SameItems { items: olds, impls, is_impl, inner: None });
    }
    // The new body's items in old order: (old item, new item) per kind.
    let news: Vec<&crate::ast::Item> = body_ast.stmt_items.iter().zip(&is_impl).filter(|(_, x)| !**x).map(|(it, _)| it).collect();
    let new_impls: Vec<&crate::ast::Item> = body_ast.stmt_items.iter().zip(&is_impl).filter(|(_, x)| **x).map(|(it, _)| it).collect();
    let pairs: Vec<(&crate::ast::Item, &crate::ast::Item)> =
        olds.iter().map(|&i| &ast.stmt_items[i as usize]).zip(news).chain(impls.iter().map(|&i| &ast.items[i]).zip(new_impls)).collect();
    // The bodies of an item's own fns: a fn's, an impl's methods'.
    let fn_bodies = |it: &crate::ast::Item, a: &Ast| -> Vec<crate::diag::Span> {
        match &it.kind {
            ItemKind::Fn(f) => f.body.iter().map(|b| a.blocks[b.0 as usize].span).collect(),
            ItemKind::Impl(imp) => imp.fns.iter().filter_map(|f| f.body).map(|b| a.blocks[b.0 as usize].span).collect(),
            _ => Vec::new(),
        }
    };
    let strictly = |b: &crate::diag::Span| b.lo < edit.a && edit.b < b.hi;
    let holders: Vec<(usize, usize)> =
        pairs.iter().enumerate().flat_map(|(k, (o, _))| fn_bodies(o, ast).iter().position(strictly).map(|m| (k, m))).collect();
    let inner = match holders[..] {
        [] => None,
        [(k, m)] => Some((k, m)),
        _ => return Err("body items"),
    };
    if let Some((k, m)) = inner {
        let b = fn_bodies(pairs[k].0, ast)[m];
        let holds = |s: crate::diag::Span| b.lo <= s.lo && s.hi <= b.hi;
        if pairs.iter().enumerate().any(|(j, (o, _))| j != k && holds(o.span)) {
            return Err("body items");
        }
    } else {
        // Braces in the changed tokens are fine when they close in the
        // window in both versions and no item overlaps it: every item then
        // sits inside the same braces as before.
        let (pre, post) = token_window(toks.0, toks.1, edit);
        let (ow, nw) = (&toks.0[pre..toks.0.len() - post], &toks.1[pre..toks.1.len() - post]);
        let balanced = |w: &[lexer::Token]| {
            let mut depth = 0i32;
            w.iter().all(|t| {
                depth += match t.tok {
                    Tok::LBrace => 1,
                    Tok::RBrace => -1,
                    _ => 0,
                };
                depth >= 0
            }) && depth == 0
        };
        let clear = |w: &[lexer::Token], spans: Vec<crate::diag::Span>| match (w.first(), w.last()) {
            (Some(f), Some(l)) => spans.iter().all(|s| s.hi <= f.span.lo || l.span.hi <= s.lo),
            _ => true,
        };
        let braces = ow.iter().chain(nw).any(|t| matches!(t.tok, Tok::LBrace | Tok::RBrace));
        if braces
            && !(balanced(ow)
                && balanced(nw)
                && clear(ow, pairs.iter().map(|(o, _)| o.span).collect())
                && clear(nw, pairs.iter().map(|(_, n)| n.span).collect()))
        {
            return Err("body items");
        }
    }
    // Same text at the same place: span keys of the resolver tables
    // (`const_init_module`) move with the edit.
    let src = |t: &str, s: crate::diag::Span| t.get(s.lo as usize..s.hi as usize).map(str::to_owned);
    for (k, (o, n)) in pairs.iter().enumerate() {
        let (os, ns) = (o.span, n.span);
        if let Some((_, m)) = inner.filter(|i| i.0 == k) {
            // The text up to the body's brace stands (the edit is after it).
            let (b, nb) = (fn_bodies(o, ast).get(m).copied(), fn_bodies(n, body_ast).get(m).copied());
            let head = b.zip(nb).is_some_and(|(b, nb)| {
                b.lo == nb.lo && src(old, crate::diag::Span { hi: b.lo, ..os }) == src(text, crate::diag::Span { hi: b.lo, ..ns })
            });
            if edit.plain(os) != ns || !head {
                return Err("body items");
            }
            continue;
        }
        if edit.plain(os) != ns || src(old, os).is_none() || src(old, os) != src(text, ns) {
            return Err("body items");
        }
    }
    let inner = inner.map(|(k, m)| if k < olds.len() { (usize::MAX, Some(olds[k] as usize)) } else { (impls[k - olds.len()], Some(m)) });
    Ok(SameItems { items: olds, impls, is_impl, inner })
}

/// The changed tokens of one edit: how many tokens of `old` (lexed from
/// the old text) and `new` (the same range of the new text) lie wholly
/// before the edit at the same spans, and how many lie wholly after it at
/// the same spans moved by the edit. Those are the same text at the same
/// boundaries, so the same tokens; the rest of each is the window.
fn token_window(old: &[lexer::Token], new: &[lexer::Token], edit: Edit) -> (usize, usize) {
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let span_eq = |x: &lexer::Token, y: &lexer::Token, shift: i64| {
        (x.span.lo as i64 + shift, x.span.hi as i64 + shift) == (y.span.lo as i64, y.span.hi as i64)
    };
    let pre = old.iter().zip(new).take_while(|(x, y)| x.span.hi <= a && span_eq(x, y, 0)).count();
    let post = old[pre..].iter().rev().zip(new[pre..].iter().rev()).take_while(|(x, y)| x.span.lo >= b && span_eq(x, y, d)).count();
    (pre, post)
}

/// Proves that `edit` (the map's text of its file to `text`) sits inside
/// a cfg-disabled node the expander dropped at the last full resolve
/// (`Dep::Dropped`), in a way a cold resolve of `text` answers the same
/// up to spans: the node lexes alone to the same tokens outside the
/// edit, the changed tokens sit in one brace group inside the node and
/// outside any macro call or attribute, they hold nothing the expander's
/// prescan, the module outline, or the cfg name check reads (`$`, `#`,
/// item keywords, `cfg`, `macro_rules`), and the new node passes the
/// expander's own grammar check (`parser::check_cfg_syntax`). The file's
/// text scans (`macro_rules`, parser macro shadowing) must stand too.
/// `Err(None)` when no dropped node holds the edit.
fn find_inactive_edit(front: &Front, text: &str, edit: Edit) -> Result<(), Option<&'static str>> {
    let base = front.patch.as_ref().ok_or(Some("no base"))?;
    let file = edit.file;
    let old = front.map.text(file).ok_or(Some("no text"))?;
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let node = base.dropped.iter().find(|n| n.file == file.0 && n.lo < a && b < n.hi).ok_or(None)?;
    // The node sits in an item list (a module's, an impl's, a trait's),
    // in no active item's own text: an edit inside an active body would
    // move positions inside it, and only the patch's fns rehash their
    // text (`fn_text_hash`).
    let ast = &front.ast;
    let holds = |s: crate::diag::Span| s.file == file && s.lo <= node.lo && node.hi <= s.hi;
    let fn_holds = |f: &FnDef| holds(f.name_span) || f.body.is_some_and(|bl| holds(ast.blocks[bl.0 as usize].span));
    for it in ast.items.iter().filter(|it| holds(it.span)) {
        let inside = match &it.kind {
            ItemKind::Impl(imp) => imp.fns.iter().any(fn_holds) || imp.consts.iter().any(|c| holds(c.span)),
            ItemKind::Trait(tr) => tr.fns.iter().any(fn_holds) || tr.consts.iter().any(|c| holds(c.span)),
            _ => true,
        };
        if inside {
            return Err(Some("inactive in item"));
        }
    }
    let new_hi = (node.hi as i64 + d) as usize;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, node.lo, &front.interner).ok().filter(balanced)).ok_or(Some("inactive lex"));
    let (old_toks, new_lexed) = (lex(old.get(node.lo as usize..node.hi as usize))?, lex(text.get(node.lo as usize..new_hi))?);
    let (ot, nt) = (&old_toks.tokens[..old_toks.tokens.len() - 1], &new_lexed.tokens[..new_lexed.tokens.len() - 1]);
    // Both end where the node ends, on a token that cannot run into the
    // text after it.
    let ends = |toks: &[lexer::Token], hi: usize| {
        toks.last().is_some_and(|t| {
            t.span.hi as usize == hi && matches!(t.tok, Tok::RBrace | Tok::Semi | Tok::RParen | Tok::RBracket | Tok::Comma)
        })
    };
    if !ends(ot, node.hi as usize) || !ends(nt, new_hi) {
        return Err(Some("inactive lex"));
    }
    let (pre, post) = token_window(ot, nt, edit);
    let (ow, nw) = (&ot[pre..ot.len() - post], &nt[pre..nt.len() - post]);
    // The groups around the window: open before it and closed after it,
    // in both versions (each version must balance).
    let closes = |toks: &[lexer::Token]| -> Option<Vec<usize>> {
        let (mut stack, mut close) = (Vec::new(), vec![usize::MAX; toks.len()]);
        for (i, t) in toks.iter().enumerate() {
            match t.tok {
                Tok::LBrace | Tok::LParen | Tok::LBracket => stack.push(i),
                Tok::RBrace | Tok::RParen | Tok::RBracket => close[stack.pop()?] = i,
                _ => {}
            }
        }
        stack.is_empty().then_some(close)
    };
    let (oc, nc) = (closes(ot).ok_or(Some("inactive lex"))?, closes(nt).ok_or(Some("inactive lex"))?);
    let (oend, nend) = (ot.len() - post, nt.len() - post);
    let chain: Vec<usize> =
        (0..pre).filter(|&i| oc[i] != usize::MAX && oc[i] >= oend && nc[i] >= nend && oc[i] - oend == nc[i] - nend).collect();
    let (macro_rules, cfg, union) = (front.interner.intern("macro_rules"), front.interner.intern("cfg"), front.interner.intern("union"));
    // Tokens the expander's prescan, the module outline, or the cfg name
    // check acts on: none may change.
    let read = |t: &lexer::Token| {
        matches!(
            t.tok,
            Tok::Pound
                | Tok::Dollar
                | Tok::DocStr(_)
                | Tok::Fn
                | Tok::Struct
                | Tok::Enum
                | Tok::Impl
                | Tok::Trait
                | Tok::Mod
                | Tok::Use
                | Tok::Extern
                | Tok::Static
                | Tok::Const
                | Tok::Type
        ) || matches!(t.tok, Tok::Ident(s) if s == macro_rules || s == cfg || s == union)
    };
    // A construct those passes read starts with one of those tokens: one
    // that starts just before the window (`#` + `[cfg_attr(..)]`, `cfg` +
    // `!(..)`, `macro_rules` + `! m {..}`) would take window tokens.
    if chain.is_empty() || ow.iter().chain(nw).any(read) || ot[pre.saturating_sub(4)..pre].iter().any(read) {
        return Err(Some("inactive tokens"));
    }
    // No group around the window is an attribute's (`#[`, `#![`) or a
    // macro definition's body (`macro_rules! m {`; the prescan defines
    // macros even in disabled code), and the window is in no `use` or
    // `extern` item of any group around it (the prescan reads the `use`
    // items of module lists).
    let before = |i: usize, k: usize| i.checked_sub(k).map(|j| ot[j].tok);
    if chain.iter().any(|&i| {
        matches!(before(i, 1), Some(Tok::Pound))
            || matches!((before(i, 2), before(i, 1)), (Some(Tok::Bang), Some(Tok::Ident(_))) | (Some(Tok::Pound), Some(Tok::Bang)))
    }) {
        return Err(Some("inactive macro"));
    }
    for (k, &g) in chain.iter().enumerate() {
        // This group's own tokens from its open up to the next group in
        // the chain (or the window): an item still open there holds it.
        let upto = chain.get(k + 1).copied().unwrap_or(pre);
        let mut i = g + 1;
        let mut open_item = false;
        while i < upto {
            match ot[i].tok {
                Tok::Semi => open_item = false,
                // `use<..>` is a precise-capturing bound, not a `use` item.
                Tok::Use if ot.get(i + 1).map(|t| t.tok) == Some(Tok::Lt) => {}
                Tok::Use | Tok::Extern => open_item = true,
                _ => {}
            }
            i = if oc[i] != usize::MAX { oc[i] + 1 } else { i + 1 };
        }
        if open_item {
            return Err(Some("inactive tokens"));
        }
    }
    let hint = if node.item { crate::parser::CfgSyntaxHint::Item } else { crate::parser::CfgSyntaxHint::Node };
    crate::parser::check_cfg_syntax(nt, &new_lexed.strings, &front.interner, &front.known, hint, node.brace).map_err(|_| Some("inactive syntax"))?;
    if old.contains("macro_rules") != text.contains("macro_rules")
        || shadows_parser_macro(old) != shadows_parser_macro(text)
        || shadows_builtin(old) != shadows_builtin(text)
    {
        return Err(Some("inactive text"));
    }
    Ok(())
}

/// Why an edit at `a..b` of `file` is in no top-level fn body: it sits
/// in some other item of the merged Ast (a nested fn, a trait method, a
/// const), or in no item at all (cfg-disabled code, or between items).
fn outside_fn_reason(ast: &Ast, file: FileId, a: usize, b: usize) -> &'static str {
    let inside = |sp: crate::diag::Span| sp.file == file && (sp.lo as usize) <= a && b <= sp.hi as usize;
    if ast.items.iter().any(|it| inside(it.span)) { "not in a fn body" } else { "no active item" }
}

/// True when a lexed body has no token that collect's whole-Ast scans
/// look for: `dyn` (a `dyn` type turns on the generic machinery) and
/// the names of `generics::flag_scan_name` (one list for the scans and
/// this check). Closure expressions are checked on the nodes
/// (`find_body_edit`).
fn plain_body(lexed: &lexer::Lexed, interner: &crate::intern::Interner) -> bool {
    lexed.tokens.iter().all(|t| match t.tok {
        Tok::Dyn => false,
        Tok::Ident(s) => !crate::check::generics::flag_scan_name(interner.get(s)),
        _ => true,
    })
}

/// Expands the pure builtin macros and attributes of `raw` (a body, or
/// a whole fn item whose header needs no expander) as the resolver's
/// token pass does, in `module` of `file` (new text `text`). Gives up
/// on a crate with no expander state, an unknown cfg name, or an
/// expansion that reads a file or env value (a dep other than a
/// cfg-dropped node): the request then resolves in full.
fn expand_pure(
    front: &Front,
    base: &PatchBase,
    file: FileId,
    text: &str,
    module: crate::ty::defs::ModuleId,
    raw: lexer::Lexed,
) -> Result<lexer::Lexed, &'static str> {
    // The cfg and crate name of the fn's own crate: a path dependency
    // shares the session, and its features and cfgs are its own.
    let Some((env, crate_name)) = base.expand_env(module) else { return Err("macro in body") };
    let path = front.map.path(file);
    let shown = front.display_root.as_deref().and_then(|r| std::path::Path::new(path).strip_prefix(r).ok());
    let ctx = crate::expand::ExpandCtx {
        interner: &front.interner,
        known: &front.known,
        file_path: shown.map_or_else(|| path.to_string(), |rel| rel.to_string_lossy().to_string()),
        real_path: std::path::PathBuf::from(path),
        // No Cargo env on the patch path: a body that reads one (`env!`,
        // an include) records a non-`Dropped` dep and the patch gives up.
        cargo_env: Vec::new(),
        src: text,
        cfg: crate::resolve::worklist::expand_cfg(env),
        module_path: base.tables.modules[module.0 as usize].path.clone(),
        crate_name: Some(crate_name.clone()),
        // No dependency macro expands on this path (a user macro gives up).
        extern_crates: Vec::new(),
        client: &front.client,
    };
    // Unknown cfg names reject before expansion, as in the resolver.
    if crate::resolve::worklist::check_cfg_names(&raw, env, &front.interner).is_err() {
        return Err("body macro");
    }
    match crate::expand::expand_lexed_seeded_with_deps(raw, &ctx, &[]) {
        Ok((out, deps)) if deps.iter().all(|d| matches!(d, crate::expand::Dep::Dropped { .. })) => Ok(out),
        _ => Err("body macro"),
    }
}

/// The expanded tokens (`{` through `}`, then `Eof`) of a new fn body at
/// bytes `body` of `text` that the patch cannot expand alone (a user macro,
/// or a builtin that is not pure): the whole new text of the file expands
/// under the last full resolve's macro environment (`FileExpander`), as a
/// cold resolve expands it, and the body's tokens are cut out of the
/// result. A body edit defines no macro and no module (`body_tokens_ok`),
/// so that environment stands. Gives up (the request resolves in full) on
/// no expander for the file, the crate root file (std splice), a
/// `#[macro_use]` module after the edit, a `static` (its init closure
/// would hoist out of the body), a cfg name error, an expansion error, or
/// a dependency other than a cfg-dropped node.
fn expand_by_file(front: &Front, base: &PatchBase, text: &str, edit: Edit, body: (u32, u32), raw: &lexer::Lexed) -> Result<lexer::Lexed, &'static str> {
    let file = edit.file;
    let fx = base.file_exp.as_ref().ok_or("body macro: no expander")?;
    if file == FileId(0) || fx.splices_after(file, edit.a) || raw.tokens.iter().any(|t| t.tok == Tok::Static) {
        return Err("body macro: shape");
    }
    if crate::resolve::worklist::check_cfg_names(raw, fx.env(), &front.interner).is_err() {
        return Err("body macro: cfg");
    }
    // The other written fn bodies of the file, at their new places.
    let ast = &front.ast;
    let at = |s: crate::diag::Span| if s.lo >= edit.b { ((s.lo as i64 + edit.d) as u32, (s.hi as i64 + edit.d) as u32) } else { (s.lo, s.hi) };
    let mut blank: Vec<(u32, u32)> = base
        .fns_by_file
        .get(file.0 as usize)
        .into_iter()
        .flatten()
        .filter_map(|&i| {
            let (item, sub) = *front.fn_loc.get(i as usize)?;
            if item == usize::MAX || item >= ast.items.len() {
                return None;
            }
            let span = ast.blocks[fn_def_at(ast, item, sub).body?.0 as usize].span;
            (span.file == file && span.ctxt == CtxtId::ROOT && span.lo != body.0).then(|| at(span))
        })
        .collect();
    blank.sort_unstable();
    blank.dedup();
    // A range that would cover the edited body never blanks.
    blank.retain(|&(lo, hi)| !(lo <= body.0 && body.1 <= hi));
    if blank.windows(2).any(|w| w[0].1 > w[1].0) {
        blank.clear();
    }
    let (out, deps) = match fx.expand(file, text, &blank, &front.interner, &front.known, &front.client) {
        Some(Ok(x)) => x,
        Some(Err(_)) => return Err("body macro: expand error"),
        None => return Err("body macro: no file"),
    };
    if !deps.iter().all(|d| matches!(d, crate::expand::Dep::Dropped { .. })) {
        return Err("body macro: deps");
    }
    // The expander gives both delimiters of a group the group's span.
    let span = crate::diag::Span { file, lo: body.0, hi: body.1, ctxt: CtxtId::ROOT };
    let i0 = out.tokens.iter().position(|t| t.tok == Tok::LBrace && t.span == span).ok_or("body macro: cut open")?;
    let n = out.tokens[i0..].iter().position(|t| t.tok == Tok::RBrace && t.span == span).ok_or("body macro: cut close")?;
    let mut tokens = out.tokens[i0..=i0 + n].to_vec();
    tokens.push(lexer::Token { tok: Tok::Eof, span: crate::diag::Span { lo: body.1, ..span } });
    Ok(lexer::Lexed { tokens, strings: out.strings })
}

/// The expanded tokens of an unchanged fn body (the old text's bytes
/// `body`, `{` through `}`) at their new positions, for a header edit
/// (`edit`) of fn `fn_index` whose body the patch cannot expand alone
/// (a user macro). They come from the last request's item patch of the
/// same body at the same place (`PatchBase::kept_bodies`), or from the
/// full resolve's stored expansion of the file when no patch since edited
/// a file its tokens or contexts name (`ResolveCache::expansion_of`,
/// `PatchBase::edited`): what a cold expansion of the same body text gives. Only while that expansion is this Ast's own
/// (`PatchBase::expansions`), and as the request's only edit (another
/// edit may move a macro definition its contexts name); `find_edits`
/// refuses an expansion that read a token position. Contexts move as the Ast's do (`Edit::span`, with a
/// memo of its own: the body's expansions are its own). The returned
/// strings hold only the ones the tokens name.
fn kept_body(front: &Front, base: &PatchBase, fn_index: usize, edit: Edit, body: (u32, u32)) -> Result<lexer::Lexed, &'static str> {
    let file = edit.file;
    let stored_owned: lexer::Lexed;
    let (tokens, strings) = match base.kept_bodies.iter().find(|k| k.fn_index == fn_index && k.file == file && k.span == body) {
        Some(k) => (&k.body.tokens[..], &k.body.strings[..]),
        None => {
            let cache = &front.resolve_cache;
            let old = front.map.text(file).ok_or("no text")?;
            let own = if file == FileId(0) { base.root_unspliced.as_str() } else { old };
            stored_owned = match cache.expansion_of(file, own).or_else(|| cache.expansion_of(file, old)) {
                Some(l) if cache.expansions() == base.expansions => l,
                _ => return Err("item: body macro"),
            };
            let stored = &stored_owned;
            // The expander gives both delimiters of a group the group's span.
            let at = |t: &lexer::Token, tok: Tok| t.tok == tok && t.span == crate::diag::Span { file, lo: body.0, hi: body.1, ctxt: CtxtId::ROOT };
            let i0 = stored.tokens.iter().position(|t| at(t, Tok::LBrace)).ok_or("item: body macro")?;
            let n = stored.tokens[i0..].iter().position(|t| at(t, Tok::RBrace)).ok_or("item: body macro")?;
            let toks = &stored.tokens[i0..=i0 + n];
            // Its spans and contexts stand when no patch edited a file they
            // name (a macro definition's file, or this one and back).
            let mut named: Vec<FileId> = Vec::new();
            let mut ctxts: Vec<CtxtId> = Vec::new();
            for t in toks {
                if !named.contains(&t.span.file) {
                    named.push(t.span.file);
                }
                if t.span.ctxt != CtxtId::ROOT && !ctxts.contains(&t.span.ctxt) {
                    ctxts.push(t.span.ctxt);
                    crate::diag::ctxt_files(t.span.ctxt, &mut named);
                }
            }
            if named.iter().any(|f| base.edited.contains(f)) {
                return Err("item: body macro");
            }
            (toks, &stored.strings[..])
        }
    };
    let mut memo = FxMap::default();
    let mut remap: FxMap<u32, u32> = FxMap::default();
    let mut out = lexer::Lexed { tokens: tokens.to_vec(), strings: Vec::new() };
    for t in &mut out.tokens {
        t.span = edit.span(t.span, &mut memo);
        for i in t.tok.string_indices_mut().into_iter().flatten() {
            let s = strings.get(*i as usize).ok_or("item: body macro")?;
            *i = *remap.entry(*i).or_insert_with(|| {
                out.strings.push(s.clone());
                out.strings.len() as u32 - 1
            });
        }
    }
    Ok(out)
}

/// One fn body's expanded tokens, as an item patch built them
/// (`kept_body`): fn `fn_index`, whose body spans `span` of `file`.
struct KeptBody {
    fn_index: usize,
    file: FileId,
    span: (u32, u32),
    body: lexer::Lexed,
}

/// Checks one lexed body (`{` at `lo` through `}` ending at `hi`, then
/// `Eof`): one balanced brace group, no `$`, macro the expander owns but
/// `PURE_MACROS`, or item keyword but `fn`, `static`, `const`, `use`.
/// Returns whether it calls a parser macro (`println!` and kin) and
/// whether it needs the expander (a pure builtin or an attribute), or
/// why the body fails a check.
fn body_tokens_ok(lexed: &lexer::Lexed, lo: usize, hi: usize, interner: &crate::intern::Interner) -> Result<(bool, bool), &'static str> {
    let toks = &lexed.tokens;
    let n = toks.len().checked_sub(1).ok_or("body shape")?;
    if n < 2 || toks[n].tok != Tok::Eof || toks[0].tok != Tok::LBrace || toks[0].span.lo as usize != lo {
        return Err("body shape");
    }
    if toks[n - 1].tok != Tok::RBrace || toks[n - 1].span.hi as usize != hi {
        return Err("body shape");
    }
    let (macro_rules, union) = (interner.intern("macro_rules"), interner.intern("union"));
    let mut depth = 0usize;
    let (mut calls, mut pure, mut user) = (false, false, false);
    for (i, t) in toks[..n].iter().enumerate() {
        match t.tok {
            Tok::LBrace | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::RBrace | Tok::RParen | Tok::RBracket => {
                depth = depth.checked_sub(1).ok_or("body shape")?;
                if depth == 0 && i != n - 1 {
                    return Err("body shape");
                }
            }
            // `fn`, `static`, `const`, `use`, struct, enum, type alias, and
            // impl items are compared after the parse (`same_items`).
            Tok::Trait | Tok::Mod | Tok::Extern => return Err("body item"),
            // A glob `use` in a body: a full resolve reads block globs
            // through what it records for them, which the body rewrite
            // against the frozen tables does not rebuild (the patch
            // oracle found `use core::ops::Bound::*;` rewriting another
            // way on tsrust-all4).
            Tok::Use if toks[i..n].iter().take_while(|t| t.tok != Tok::Semi).any(|t| t.tok == Tok::Star) => return Err("body glob"),
            // Attributes go through the expander (cfg stripping).
            Tok::Pound | Tok::DocStr(_) => pure = true,
            Tok::Dollar => return Err("body attr"),
            Tok::Ident(s) if s == macro_rules || s == union => return Err("body item"),
            // A macro call: `name!`, never path-qualified. A user macro
            // is the last reason (`find_item_edit` can take its stored
            // expansion when no other rule refuses the body).
            Tok::Bang if i > 0 => match toks[i - 1].tok {
                Tok::Ident(_) if i > 1 && toks[i - 2].tok == Tok::PathSep => user = true,
                Tok::Ident(s) if crate::expand::builtin::is_passthrough(interner.get(s)) => calls = true,
                Tok::Ident(s) if PURE_MACROS.contains(&interner.get(s)) => pure = true,
                Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super => user = true,
                _ => {}
            },
            _ => {}
        }
    }
    // Anything else the expander acts on is a refused macro.
    if depth != 0 {
        return Err("body shape");
    }
    if user || !pure && crate::expand::needs_expansion(&toks[..n], interner) {
        return Err("body macro");
    }
    Ok((calls, pure))
}

/// Builtin macros the expander owns whose expansion reads only their
/// own tokens and the crate's cfg: a body that calls them expands alone
/// to what the resolver's expansion of its file gives (no position, path,
/// env, file, or item output). `cfg!` names also pass the cfg name check.
const PURE_MACROS: &[&str] =
    &["matches", "write", "writeln", "debug_assert", "debug_assert_eq", "debug_assert_ne", "unimplemented", "stringify", "concat", "cfg"];

/// Applies the proven edits to the front state and runs the slot update.
/// `ctxts` gets each edit's fresh expansion contexts, in edit order.
fn apply(front: &mut Front, caches: &mut Caches, mut edits: Vec<BodyEdit>, reads: usize, ctxts: &mut Vec<FxMap<u32, CtxtId>>) -> Result<Patched, &'static str> {
    let mut base = front.patch.take().ok_or("no base")?;
    let (mut spans, files) = (0usize, edits.len());
    let nodes_before = super::compile::ast_nodes(&front.ast);
    // A crate with user macros or includes got no file ranges at the
    // resolve, so its span walks would visit the whole Ast per edit.
    // Probe once, on the first patch: the nodes that can hold another
    // file's spans (or a context) are few, and the rest walk by file.
    if base.ranges.is_none() && !edits.is_empty() {
        base.probe(Arc::make_mut(&mut front.ast), front.map.file_count());
    }
    let no_extras = span_shift::ExtraNodes::default();
    for e in &edits {
        // The old body's nodes stay in the arenas, unreachable; blank them,
        // because some passes scan whole arenas (closures, `dyn`, `Cow`).
        let ranges = base.ranges.as_ref().and_then(|r| r.get(e.file.0 as usize));
        let extras = base.extras.as_ref().and_then(|x| x.get(e.file.0 as usize)).unwrap_or(&no_extras);
        // The resolve cache's final chunks are parts of this Ast: the ones these writes
        // change go (the file's, and every one when other files' nodes hold its spans).
        front.resolve_cache.forget_final(e.file, !extras.is_empty());
        if let Some(body) = &e.body {
            span_shift::blank_nodes_extras(Arc::make_mut(&mut front.ast), e.file, body.old_body, ranges, extras);
        }
        if let Some(it) = &e.item {
            span_shift::blank_nodes_extras(Arc::make_mut(&mut front.ast), e.file, it.old, ranges, extras);
        }
        // Spans next: the new body is lexed at the new positions.
        let mut memo = FxMap::default();
        spans += span_shift::shift_ast_extras(Arc::make_mut(&mut front.ast), e.edit, ranges, extras, &mut memo);
        ctxts.push(memo);
        let splice_len = if e.file == FileId(0) { splice_of(front, &base).map_or(0, str::len) } else { 0 };
        let tables = Arc::get_mut(&mut base.tables).ok_or("state")?;
        shift_table_spans(tables, e.edit);
        let lines = front.map.lines(e.file).splice(&e.text, e.edit.a as usize, e.edit.b as usize, (e.edit.b as i64 + e.edit.d) as usize);
        front.map.replace_text(e.file, e.text.clone(), lines);
        if e.file == FileId(0) {
            front.src.clone_from(&e.text);
            front.chunks[0].text.clone_from(&e.text);
            base.root_unspliced = e.text[..e.text.len() - splice_len].to_string();
        }
        // The splice after the root text moves with the edit: its byte
        // ranges in file 0 and the lang method range, wherever they sit
        // (the base, the resolver tables, the Ast).
        if base.spliced && e.file == FileId(0) {
            let mv = |x: u32| if x >= e.edit.b { (x as i64 + e.edit.d) as u32 } else { x };
            let ranges = |rs: &mut Vec<(u32, u32, ShippedCrate)>| rs.iter_mut().for_each(|r| (r.0, r.1) = (mv(r.0), mv(r.1)));
            ranges(&mut base.std_ranges);
            base.std_methods = (mv(base.std_methods.0), mv(base.std_methods.1));
            ranges(&mut tables.std_ranges);
            tables.std_splice_lo = tables.std_splice_lo.map(mv);
            let ast = Arc::make_mut(&mut front.ast);
            ranges(&mut ast.shipped);
            ast.lang_methods = (mv(ast.lang_methods.0), mv(ast.lang_methods.1));
        }
        base.needs[e.file.0 as usize] = e.needs;
        base.stamps[e.file.0 as usize] = None;
        for d in base.dropped.iter_mut().filter(|d| d.file == e.file.0) {
            let s = e.edit.plain(crate::diag::Span { file: e.file, lo: d.lo, hi: d.hi, ctxt: CtxtId::ROOT });
            (d.lo, d.hi) = (s.lo, s.hi);
        }
    }
    for e in edits.iter_mut() {
        let file = e.file;
        let Some(e) = e.body.as_mut() else { continue };
        let ast = &front.ast;
        let before = (ast.exprs.len(), ast.pats.len(), ast.tys.len(), ast.blocks.len(), ast.stmt_items.len());
        let stmt_base = before.4 as u32;
        let (_, new_items, _) = Arc::make_mut(&mut front.ast).append_chunk(std::mem::take(&mut e.body_ast), stmt_base);
        // Each body item takes its old index (`same_items`). A body impl
        // takes its old place in the module items, and its statement goes,
        // as flatten hoists it (`hoist_block_impls`).
        if !e.is_impl.is_empty() {
            let ast = Arc::make_mut(&mut front.ast);
            let (mut stmts, mut impls) = (e.items.iter(), e.impls.iter());
            let mut to: Vec<Option<u32>> = Vec::with_capacity(e.is_impl.len());
            for &imp in &e.is_impl {
                to.push(if imp { None } else { Some(*stmts.next().ok_or("body items")?) });
            }
            let mut bad = false;
            for blk in &mut ast.blocks[before.3..] {
                blk.stmts.retain_mut(|s| match s {
                    crate::ast::Stmt::Item(i) => match to.get((*i - stmt_base) as usize) {
                        Some(&Some(n)) => {
                            *i = n;
                            true
                        }
                        Some(None) => false,
                        None => {
                            bad = true;
                            true
                        }
                    },
                    _ => true,
                });
            }
            if bad || new_items.len() != to.len() {
                return Err("body items");
            }
            for (mut it, k) in new_items.into_iter().zip(to) {
                match k {
                    Some(i) => ast.stmt_items[i as usize] = it,
                    None => {
                        let ItemKind::Impl(imp) = &mut it.kind else { return Err("body items") };
                        imp.in_body = true;
                        ast.items[*impls.next().ok_or("body items")?] = it;
                    }
                }
            }
        }
        if let Some(sig) = &e.sig {
            super::sig_nodes::relink(Arc::make_mut(&mut front.ast), e.item, e.sub, sig, (before.0 as u32, before.1 as u32));
        }
        let def = fn_def_at_mut(Arc::make_mut(&mut front.ast), e.item, e.sub);
        def.body = Some(BlockId(e.body.0 + before.3 as u32));
        def.exprs = (e.exprs.0 + before.0 as u32, e.exprs.1 + before.0 as u32);
        def.pats = (e.pats.0 + before.1 as u32, e.pats.1 + before.1 as u32);
        // The new body's nodes join the file's ranges for later edits.
        if let Some(r) = base.ranges.as_mut().and_then(|r| r.get_mut(file.0 as usize)) {
            let ast = &front.ast;
            r.exprs.push(before.0..ast.exprs.len());
            r.pats.push(before.1..ast.pats.len());
            r.tys.push(before.2..ast.tys.len());
            r.blocks.push(before.3..ast.blocks.len());
            r.stmt_items.push(before.4..ast.stmt_items.len());
        }
        // Under a probed plan, probe just the appended nodes: the first
        // probe never saw them, and the body's path rewrite may have
        // given a node a span from another file.
        if base.extras.is_some() {
            let ast = &front.ast;
            let only = FileRanges {
                exprs: vec![before.0..ast.exprs.len()],
                pats: vec![before.1..ast.pats.len()],
                tys: vec![before.2..ast.tys.len()],
                blocks: vec![before.3..ast.blocks.len()],
                items: Vec::new(),
                stmt_items: vec![before.4..ast.stmt_items.len()],
            };
            let n = front.map.file_count();
            let probed = span_shift::probe_extras_in(Arc::make_mut(&mut front.ast), n, &only);
            for (x, p) in base.extras.as_mut().unwrap().iter_mut().zip(probed) {
                x.exprs.extend(p.exprs);
                x.pats.extend(p.pats);
                x.tys.extend(p.tys);
                x.blocks.extend(p.blocks);
                x.items.extend(p.items);
                x.stmt_items.extend(p.stmt_items);
            }
        }
        let (hash, idents) = rescan_edited(front, &mut base, e)?;
        if !e.impls.is_empty() {
            body_impl_hashes(front, &mut base, e)?;
        }
        let def = fn_def_at(&front.ast, e.item, e.sub);
        let line = front.map.line_col(def.name_span).0;
        let h = fn_text_hash(&front.ast, &front.map, def, line, hash);
        base.body_hashes[e.fn_index] = h;
        let chunk = &mut front.chunks[0];
        chunk.scan.fns.get_mut(e.fn_index).ok_or("state")?.body_hash = h;
        *chunk.scan.body_idents.get_mut(e.fn_index).ok_or("state")? = idents;
    }
    // Item edits: the new fn takes the old one's place, and its item
    // rescans whole (its scan may move: the tail runs in signatures mode).
    let mut item_names: Vec<Sym> = Vec::new();
    let mut item_fns: Vec<usize> = Vec::new();
    let mut item_full = false;
    for e in edits.iter_mut() {
        let file = e.file;
        let Some(it) = e.item.as_mut() else { continue };
        item_full |= it.full;
        let ast = &front.ast;
        let before = (ast.exprs.len(), ast.pats.len(), ast.tys.len(), ast.blocks.len(), ast.stmt_items.len());
        let ast = Arc::make_mut(&mut front.ast);
        let stmt_base = before.4 as u32;
        let (mut new_items, new_stmts, _) = ast.append_chunk(std::mem::take(&mut it.item_ast), stmt_base);
        // Each body item takes its old index (`same_items`).
        if new_stmts.len() != it.items.len() {
            return Err("body items");
        }
        if !it.items.is_empty() {
            let mut bad = false;
            for blk in &mut ast.blocks[before.3..] {
                for s in &mut blk.stmts {
                    if let crate::ast::Stmt::Item(i) = s {
                        match it.items.get((*i - stmt_base) as usize) {
                            Some(&n) => *i = n,
                            None => bad = true,
                        }
                    }
                }
            }
            if bad {
                return Err("body items");
            }
            for (st, &k) in new_stmts.into_iter().zip(&it.items) {
                ast.stmt_items[k as usize] = st;
            }
        }
        let new_item = new_items.pop().ok_or("item parse")?;
        let crate::ast::Item { vis, attrs, kind, span } = new_item;
        match (kind, it.sub) {
            (ItemKind::Fn(f), None) => {
                ast.items[it.item] = crate::ast::Item { vis, attrs, kind: ItemKind::Fn(f), span };
            }
            (ItemKind::Impl(imp), Some(k)) => {
                // The placeholder impl's self type is unreachable now.
                ast.tys[imp.self_ty.0 as usize] = TyExpr::Infer;
                let def = imp.fns.into_iter().next().ok_or("item parse")?;
                let ItemKind::Impl(old) = &mut ast.items[it.item].kind else { return Err("state") };
                *old.fns.get_mut(k).ok_or("state")? = def;
            }
            _ => return Err("item parse"),
        }
        if let Some(r) = base.ranges.as_mut().and_then(|r| r.get_mut(file.0 as usize)) {
            let ast = &front.ast;
            r.exprs.push(before.0..ast.exprs.len());
            r.pats.push(before.1..ast.pats.len());
            r.tys.push(before.2..ast.tys.len());
            r.blocks.push(before.3..ast.blocks.len());
        }
        if base.extras.is_some() {
            let ast = &front.ast;
            let only = FileRanges {
                exprs: vec![before.0..ast.exprs.len()],
                pats: vec![before.1..ast.pats.len()],
                tys: vec![before.2..ast.tys.len()],
                blocks: vec![before.3..ast.blocks.len()],
                items: vec![it.item..it.item + 1],
                stmt_items: Vec::new(),
            };
            let n = front.map.file_count();
            let probed = span_shift::probe_extras_in(Arc::make_mut(&mut front.ast), n, &only);
            for (x, p) in base.extras.as_mut().unwrap().iter_mut().zip(probed) {
                x.exprs.extend(p.exprs);
                x.pats.extend(p.pats);
                x.tys.extend(p.tys);
                x.blocks.extend(p.blocks);
                x.items.extend(p.items);
                x.stmt_items.extend(p.stmt_items);
            }
        }
        // The whole item's scan, and every fn of it (a method's impl). The
        // fns nested in its other methods fold in its content hash, which
        // the edit moves (the edited fn holds none, `find_item_edit`).
        let (scan, bodies, inner) = super::ast_hash::scan_item(&front.ast, &front.ast.items[it.item]);
        nested_fn_hashes(front, &mut base, &scan, &bodies, &inner)?;
        let fns: Vec<usize> = front.fn_loc.iter().enumerate().filter(|(_, l)| l.0 == it.item).map(|(j, _)| j).collect();
        if fns.len() != bodies.len() {
            return Err("state");
        }
        for (&j, (hash, idents)) in fns.iter().zip(bodies) {
            let (item, sub) = front.fn_loc[j];
            let def = fn_def_at(&front.ast, item, sub);
            let line = front.map.line_col(def.name_span).0;
            let h = fn_text_hash(&front.ast, &front.map, def, line, hash);
            base.body_hashes[j] = h;
            base.fn_lines[j] = line;
            let chunk = &mut front.chunks[0];
            chunk.scan.fns.get_mut(j).ok_or("state")?.body_hash = h;
            *chunk.scan.body_idents.get_mut(j).ok_or("state")? = idents;
        }
        base.item_scans.remove(&it.item);
        front.chunks[0].scan.items[it.item] = scan;
        item_fns.push(it.fn_index);
        // The changed name: a free fn's flat name (its item scan's
        // `fn_name`), or a method's written name (P1.5: a method is only
        // ever called by name, so its callers mention it).
        item_names.push(if it.sub.is_some() { it.name } else { fn_def_at(&front.ast, it.item, None).name });
    }
    // A request with no edit keeps the last patch's bodies.
    if !edits.is_empty() {
        base.kept_bodies = edits.iter_mut().filter_map(|e| e.item.as_mut().and_then(|it| it.kept.take())).collect();
        for e in &edits {
            if !base.edited.contains(&e.file) {
                base.edited.push(e.file);
            }
        }
    }
    // Derive edits: the item's attributes and derive lists, then its scan
    // (the tail runs in full mode: any body may read the derives).
    let mut derive_edit = false;
    for e in edits.iter_mut() {
        let Some(dv) = e.derive.take() else { continue };
        derive_edit = true;
        let ast = Arc::make_mut(&mut front.ast);
        let it = &mut ast.items[dv.item];
        // The other attributes are token for token the old ones (and may
        // hold nodes of the new parse's own Ast): only derive lists move.
        if it.attrs.len() != dv.attrs.len() {
            return Err("derive: attrs");
        }
        let derive = dv.derive;
        for (old, new) in it.attrs.iter_mut().zip(dv.attrs) {
            if new.path.len() == 1 && new.path[0].name == derive {
                *old = new;
            }
        }
        match &mut it.kind {
            ItemKind::Struct(s) => s.derives = dv.derives,
            ItemKind::Enum(en) => en.derives = dv.derives,
            _ => return Err("state"),
        }
        let (scan, _, _) = super::ast_hash::scan_item(&front.ast, &front.ast.items[dv.item]);
        front.chunks[0].scan.items[dv.item] = scan;
    }
    // Fn lines in the edited files: an edit that adds or drops lines
    // moves every fn after it in that file, and no fn in any other. A fn
    // after the edit whose name's line holds the edit's end also moves in
    // its line, and its text hash reads that line from its start
    // (`fn_text_hash`): it hashes again, so its C (which embeds columns)
    // is made again.
    // The fns `apply` hashed again above at their new lines: body impl
    // methods (`body_impl_hashes`) and the edited body's nested fns
    // (`nested_fn_hashes`; the body holds items, so `rescan_edited` scanned
    // its item whole).
    let rehashed: Vec<usize> = edits.iter().filter_map(|e| e.body.as_ref()).flat_map(|b| b.hoisted.iter().copied()).collect();
    let rehashed_items: Vec<u32> = edits.iter().filter_map(|e| e.body.as_ref()).flat_map(|b| b.items.iter().copied()).collect();
    for e in &edits {
        let after = (e.edit.b as i64 + e.edit.d) as u32;
        let fns = base.fns_by_file.get(e.file.0 as usize).cloned().unwrap_or_default();
        for j in fns.into_iter().map(|j| j as usize) {
            let (item, sub) = front.fn_loc[j];
            let def = fn_def_at(&front.ast, item, sub);
            let span = def.name_span;
            if span.lo < after {
                continue;
            }
            let line = front.map.line_col(span).0;
            base.fn_lines[j] = line;
            let text = front.map.text(e.file).ok_or("state")?;
            if text[..span.lo as usize].rfind('\n').map_or(0, |i| i + 1) >= after as usize {
                continue;
            }
            // A body item's fn folds its item's content (`nested_fn_hashes`),
            // and so does a body impl's method (`body_impl_hashes` did this edit's).
            if rehashed.contains(&j) || item == usize::MAX && sub.is_some_and(|i| rehashed_items.contains(&(i as u32))) {
                continue;
            }
            if item == usize::MAX || super::ast_hash::body_impl_holder(&front.ast, item).is_some() {
                return Err("fn on the edit's line");
            }
            let h = fn_text_hash(&front.ast, &front.map, def, line, super::ast_hash::body_scan(&front.ast, def, None).0);
            base.body_hashes[j] = h;
            front.chunks[0].scan.fns.get_mut(j).ok_or("state")?.body_hash = h;
        }
    }
    // A fn that returns `impl Trait` moved its item scan (`item_stands`):
    // the environment hash follows, as a full resolve computes it, and the
    // tail checks the hidden type.
    if edits.iter().any(|e| e.body.as_ref().is_some_and(|b| b.rpit.is_some())) {
        front.env_hash = Some(crate::scan::env_hash(front.items.iter()));
        front.rpit_edit = true;
    }
    let bodies = edits.iter().filter_map(|e| e.body.as_ref());
    let mut edited: Vec<usize> = bodies.flat_map(|b| std::iter::once(b.fn_index).chain(b.nested)).collect();
    edited.extend_from_slice(&item_fns);
    // A const fn edit is a plain body edit when no const evaluation can
    // run that fn (`const_reach.rs`).
    let is_const = |i: usize| {
        let (item, sub) = front.fn_loc[i];
        fn_def_at(&front.ast, item, sub).qual.is_const
    };
    let const_edits: Vec<usize> = edited.iter().copied().filter(|&i| is_const(i)).collect();
    match &mut base.reach {
        Some(r) => r.update(front, &edited),
        // A header edit reads it too (`kept_delta::untouched_refusals`):
        // built once (at the full resolve, or here), later patches update it.
        None if !const_edits.is_empty() || !item_fns.is_empty() => base.reach = Some(super::const_reach::ConstReach::build(front)),
        None => {}
    }
    // One that only const and static values can read keeps the program
    // after their values check again (`Patched::revalue`).
    let reached: Vec<usize> = match &base.reach {
        Some(r) => const_edits.iter().copied().filter(|&i| r.reaches(front, i)).collect(),
        None => Vec::new(),
    };
    let revalue = !reached.is_empty() && base.reach.as_ref().is_some_and(|r| r.revaluable(front, &reached));
    // With an item edit the compile tail runs the full slot update in
    // signatures mode (`Patched::item_scans`).
    let item_level = !item_fns.is_empty() || derive_edit;
    let changed = if item_level { Vec::new() } else { slot_update(front, caches, &base.body_hashes, &edited, &base.live_slots) };
    let item_scans = item_level.then(|| front.chunks[0].scan.items.clone());
    let edits_len = edits.iter().filter(|e| e.body.is_some() || e.item.is_some() || e.derive.is_some()).count();
    let out = Patched {
        map: front.map.clone(),
        changed,
        fn_count: front.ast_fn_count,
        fn_lines: base.fn_lines.clone(),
        body_hashes: base.body_hashes.clone(),
        tables: base.tables.clone(),
        std_ranges: base.std_ranges.clone(),
        std_routes: base.std_routes.clone(),
        std_methods: base.std_methods,
        const_fn: !reached.is_empty() && !revalue,
        revalue,
        const_edits,
        item_scans,
        item_names,
        item_fns,
        item_full: derive_edit || item_full,
        derive_only: derive_edit && edited.is_empty(),
        files,
        nodes: super::compile::ast_nodes(&front.ast) - nodes_before,
        bodies: edits_len,
        spans,
        reads,
    };
    front.patch = Some(base);
    Ok(out)
}

/// Rescans the edited fn's item after its new body landed: the item
/// scan must stand (the edit changed no head). Returns the edited fn's
/// raw body hash and idents. The first edit in an impl whose bodies hold
/// no item scans every method and stores their hashes in the base; later
/// edits in that impl scan only the edited method, because a body hash
/// reads structure only (never spans), so unchanged methods keep theirs.
/// An item that holds body items rescans whole: its nested fns' hashes
/// fold in its content (`nested_fn_hashes`). A fn that returns `impl
/// Trait` folds its body hash into the item scan: the scan with the old
/// body hash must be the stored one, and the new scan replaces it.
fn rescan_edited(front: &mut Front, base: &mut PatchBase, e: &NewBody) -> Result<(u64, Vec<Sym>), &'static str> {
    if let (Some(sub), Some(stored)) = (e.sub, base.item_scans.get(&e.item).cloned()) {
        let (hash, idents, inner) = super::ast_hash::scan_body(&front.ast, fn_def_at(&front.ast, e.item, e.sub));
        if inner.is_empty() {
            let mut hashes = stored;
            *hashes.get_mut(sub).ok_or("item scan")? = hash;
            let scan = super::ast_hash::scan_item_reuse(&front.ast, &front.ast.items[e.item], &hashes);
            item_stands(front, e, scan, &hashes)?;
            base.item_scans.insert(e.item, hashes);
            return Ok((hash, idents));
        }
    }
    let (scan, bodies, inner) = super::ast_hash::scan_item(&front.ast, &front.ast.items[e.item]);
    item_stands(front, e, scan, &bodies.iter().map(|b| b.0).collect::<Vec<_>>())?;
    nested_fn_hashes(front, base, &scan, &bodies, &inner)?;
    if inner.is_empty() {
        base.item_scans.insert(e.item, bodies.iter().map(|b| b.0).collect());
    } else {
        base.item_scans.remove(&e.item);
    }
    bodies.into_iter().nth(e.sub.unwrap_or(0)).ok_or("item scan")
}

/// Proves the edited item's scan stands: `scan` (with the new body hashes
/// `hashes`) is the stored one, or the fn returns `impl Trait` and the
/// scan with its old body hash is; the new scan is then stored, as a full
/// resolve's item scan would be.
fn item_stands(front: &mut Front, e: &NewBody, scan: crate::scan::ItemScan, hashes: &[u64]) -> Result<(), &'static str> {
    if front.items.get(e.item) == Some(&scan) {
        return Ok(());
    }
    let old = e.rpit.ok_or("item scan")?;
    let mut old_hashes = hashes.to_vec();
    *old_hashes.get_mut(e.sub.unwrap_or(0)).ok_or("item scan")? = old;
    let was = super::ast_hash::scan_item_reuse(&front.ast, &front.ast.items[e.item], &old_hashes);
    if front.items.get(e.item) != Some(&was) || front.chunks[0].scan.items.get(e.item) != Some(&was) {
        return Err("item scan");
    }
    front.items[e.item] = scan;
    front.chunks[0].scan.items[e.item] = scan;
    Ok(())
}

/// The scans of the body impls a body edit put in place (`NewBody::impls`)
/// and their methods' body hashes and lines: each impl's scan must stand
/// (its text did, but for one method body at most), and its methods fold
/// the holder's new content in, as the full scan does (`ast_hash::assemble`).
fn body_impl_hashes(front: &mut Front, base: &mut PatchBase, e: &NewBody) -> Result<(), &'static str> {
    let (scan, bodies, _) = super::ast_hash::scan_item(&front.ast, &front.ast.items[e.item]);
    let content = super::ast_hash::item_content(&scan, &bodies);
    for &k in &e.impls {
        let (scan, bodies, inner) = super::ast_hash::scan_item(&front.ast, &front.ast.items[k]);
        if front.items.get(k) != Some(&scan) || front.chunks[0].scan.items.get(k) != Some(&scan) {
            return Err("item scan");
        }
        nested_fn_hashes(front, base, &scan, &bodies, &inner)?;
        let fns: Vec<usize> = front.fn_loc.iter().enumerate().filter(|(_, l)| l.0 == k).map(|(j, _)| j).collect();
        if fns.len() != bodies.len() {
            return Err("state");
        }
        for (&j, (hash, idents)) in fns.iter().zip(bodies) {
            let (item, sub) = front.fn_loc[j];
            let def = fn_def_at(&front.ast, item, sub);
            let line = front.map.line_col(def.name_span).0;
            let h = fn_text_hash(&front.ast, &front.map, def, line, crate::scan::fold_outer(hash, content));
            base.body_hashes[j] = h;
            base.fn_lines[j] = line;
            let chunk = &mut front.chunks[0];
            chunk.scan.fns.get_mut(j).ok_or("state")?.body_hash = h;
            *chunk.scan.body_idents.get_mut(j).ok_or("state")? = idents;
        }
        base.item_scans.remove(&k);
    }
    Ok(())
}

/// The body hashes of the fns nested anywhere in one edited item
/// (`inner`, from `scan_item`), which fold in the item's content hash, as
/// the full scan computes them (`ast_hash::assemble`), and their lines.
fn nested_fn_hashes(
    front: &mut Front,
    base: &mut PatchBase,
    scan: &crate::scan::ItemScan,
    bodies: &[(u64, Vec<Sym>)],
    inner: &[u32],
) -> Result<(), &'static str> {
    if inner.is_empty() {
        return Ok(());
    }
    let content = super::ast_hash::item_content(scan, bodies);
    for &i in inner {
        let ItemKind::Fn(def) = &front.ast.stmt_items[i as usize].kind else { continue };
        let j = front.fn_loc.iter().position(|&l| l == (usize::MAX, Some(i as usize))).ok_or("state")?;
        let (hash, idents) = super::ast_hash::body_scan(&front.ast, def, None);
        let line = front.map.line_col(def.name_span).0;
        let h = fn_text_hash(&front.ast, &front.map, def, line, crate::scan::fold_outer(hash, content));
        base.fn_lines[j] = line;
        base.body_hashes[j] = h;
        let chunk = &mut front.chunks[0];
        chunk.scan.fns.get_mut(j).ok_or("state")?.body_hash = h;
        *chunk.scan.body_idents.get_mut(j).ok_or("state")? = idents;
    }
    Ok(())
}

/// Takes the kept program in place of a fresh collect, with the number
/// of its spans moved, or says why not (the `kept=` of `lust-visits:`).
/// The program holds when it still shares the front's Ast, or when this
/// request's patch detached it and every edit allows it: the edited fn
/// is a plain fn (not a template, so no template check reads its body);
/// without user generics, both bodies hold nothing collect's whole-Ast
/// scans look for (`BodyEdit::plain`); and when collect runs instance
/// discovery over plain bodies, the new body's discovery output equals
/// the one the program was built with (`KeptBase`). Collect would then build the same tables, up to
/// spans, which move here with the edits. `tables` are this request's
/// resolver tables, as collect would attach them.
pub(super) fn reuse_kept(
    front: &mut Front,
    caches: &mut Caches,
    tables: Option<&Arc<ResolvedTables>>,
    walk_instances: bool,
) -> Result<(crate::check::collect::Program, usize, Vec<crate::diag::Diag>), &'static str> {
    use crate::check::generics::FnClass;
    use crate::def::LocalDefId;
    // A build's program holds the generic instances a check's lacks.
    let k = front.kept[usize::from(walk_instances)].take().ok_or(if front.kept.iter().any(Option::is_some) { "mode" } else { "none" })?;
    front.kept_put_back = k.prefer;
    let mut bases = k.bases;
    let recheck = k.recheck;
    // A build's instances replay its templates' checks, as a check's do
    // (`instanced_templates`).
    if !recheck.is_empty() && (walk_instances || {
        let inst = instanced_templates(&k.program);
        recheck.iter().any(|&i| inst.contains_key(&LocalDefId(i as u32)))
    }) {
        return Err("template errors");
    }
    let mut edits = match k.edits {
        Some(e) => e,
        None if Arc::ptr_eq(&k.program.ast, &front.ast) => Vec::new(),
        None => {
            // The full collect that replaces the program starts from its type store
            // (B1-PLAN.md, `ty::TypePool`).
            pool_from(caches, k.program);
            return Err("ast");
        }
    };
    // A build's instances and glue would keep the old derive lists.
    if walk_instances && edits.iter().any(|e| e.derive.is_some()) {
        return Err("derive build");
    }
    let mut p = k.program;
    // A check's templates with instances check again only as a build's do,
    // or in a request of body edits alone, whose instances of the edited
    // templates replay below (`kept_delta::replay_discovery`).
    let instanced = instanced_templates(&p);
    let bodies_only = edits.iter().all(|e| !e.header && e.derive.is_none());
    // Nested templates of edited bodies, with the edit's old node range.
    let mut nested_templates: Vec<(usize, (u32, u32))> = Vec::new();
    // The edits below change what fingerprints read.
    p.fp_memo.off();
    p.ast = front.ast.clone();
    p.resolved = tables.cloned();
    caches.gen_reuse.begin_kept();
    // Collect's whole-Ast scans only turn the generic flags on; once
    // `user_generics` is on they decide nothing.
    for e in &edits {
        if !e.plain && !p.gx.user_generics {
            return Err("body scan");
        }
        // A body that now calls a fn handing out a `Cow` turns the
        // generic flags on in collect (`uses_cow`). A derive list edit
        // has no body, and no flag scan reads derive lists.
        if !p.gx.user_generics && e.derive.is_none() && calls_cow_fn(&p, e.fn_index) {
            return Err("body scan");
        }
        // Body items keep their indexes, text, and blocks (`same_items`),
        // so the program's statics, consts, item blocks, and nested fn
        // signatures stand. Their nodes are new, and so are the body
        // impls' methods'. A plain one keeps its closures (their defs key
        // on the parent def and their order, `closure::closure_def`) and
        // its discovery output (its text and the items it sees stand). A
        // template's picks and closure tables key on its nodes: it checks
        // again below, as an edited template does, in a check only.
        let body_fns = e.items.iter().filter_map(|i| match p.body_items.get(i).copied() {
            Some(crate::check::collect::BodyItem::Fn(f)) => Some(f),
            _ => None,
        });
        for f in body_fns.chain(e.hoisted.iter().map(|&j| LocalDefId(j as u32))) {
            match p.gx.fn_class.get(f.0 as usize) {
                Some(FnClass::Plain) => {}
                Some(FnClass::Template) if !walk_instances && !p.is_lang_method(f) && !instanced.contains_key(&f) => {
                    nested_templates.push((f.0 as usize, e.old_exprs))
                }
                _ => return Err("body items"),
            }
        }
        // A generic assoc const's template keys on its value's node.
        if !e.hoisted.is_empty() && !p.gx.assoc_const_tmpls.is_empty() {
            let has_consts = |j: &usize| match p.fn_info(LocalDefId(*j as u32)).loc {
                crate::check::collect::FnLoc::Impl(i, _) => matches!(&p.ast.items[i as usize].kind, ItemKind::Impl(imp) if !imp.consts.is_empty()),
                _ => true,
            };
            if e.hoisted.iter().any(has_consts) {
                return Err("body items");
            }
        }
        // A template checks again below, in a check only: a build's
        // instances replay its picks.
        let Some(fn_index) = e.fn_index else { continue };
        let f = LocalDefId(fn_index as u32);
        match p.gx.fn_class.get(fn_index) {
            Some(FnClass::Plain) => {}
            // A template with closures stands when its closures are the
            // registered ones (checked below, before its template check),
            // and one that returns `impl Trait` while its hidden type does.
            // A header edit's instances take the new signature in the
            // header delta (`generics::refresh_instance`).
            Some(FnClass::Template) if !walk_instances && !p.is_lang_method(f) && (bodies_only || e.header || !instanced.contains_key(&f)) => {}
            _ => return Err("fn class"),
        }
    }
    let mut spans = 0;
    for e in edits.iter_mut().filter(|e| !e.shifted) {
        let (edit, ctxts) = (e.edit, &mut e.ctxts);
        spans += crate::check::prog_shift::shift_program(&mut p, &mut |s| edit.span(s, ctxts));
        e.shifted = true;
    }
    // Item patch edits: the signature delta redoes each edited header
    // (its own template check and reveal included).
    super::laps::mark("collect/kept shift");
    let headers: Vec<super::kept_delta::HeaderEdit> = edits
        .iter()
        .filter(|e| e.header)
        .filter_map(|e| Some(super::kept_delta::HeaderEdit { fn_index: e.fn_index?, old_exprs: e.old_exprs }))
        .collect();
    // The header delta checks the templates that read an edited header
    // again under the old derive lists, and the derive delta after it takes
    // those fresh checks as standing: a derive edit that removes a trait
    // such a template uses would pass (a program kept after a refused
    // derive delta, then a header edit). Both kinds collect in full.
    if !headers.is_empty() && edits.iter().any(|e| e.derive.is_some()) {
        return Err("header and derive");
    }
    if !headers.is_empty() {
        let reach = front.patch.as_ref().and_then(|b| b.reach.as_ref());
        if let Err((why, intact)) = super::kept_delta::apply_headers(&mut p, front, caches, reach, &headers, walk_instances, &mut bases) {
            // The program is as it was, with its spans moved: it stays
            // for the next request, which redoes these headers with its
            // own (sigedit R9: a rejected header edit, then its fix). A
            // signature's own errors are this request's answer.
            let sig_errs = caches.delta_sig_errs.take();
            if intact {
                front.delta_errs = sig_errs;
                caches.gen_reuse.hold(p.reuse_stamp);
                front.kept[usize::from(walk_instances)] = Some(KeptProgram { program: p, edits: Some(edits), bases, prefer: true, recheck });
            }
            return Err(why);
        }
    }
    // Templates that a header delta found failing: their errors are this
    // request's answer, as collect's template check gives them.
    let mut header_template_errs: Vec<(usize, Vec<crate::diag::Diag>)> = caches.delta_template_errs.take().unwrap_or_default();
    if walk_instances && !header_template_errs.is_empty() {
        return Err("sig template");
    }
    // Derive list edits: the derive delta toggles the synthetic records
    // and runs the checks derive lists feed again.
    let mut derives: Vec<usize> = edits.iter().filter_map(|e| e.derive).collect();
    derives.sort_unstable();
    derives.dedup();
    let mut derive_reach = None;
    if !derives.is_empty() {
        match super::kept_derive::apply_derives(&mut p, front, caches, &derives, walk_instances) {
            Ok(reach) => derive_reach = reach,
            Err((why, intact)) => {
                // A refused derive delta undid its writes: the program is as it
                // was, with its spans moved, and stays for the next request (a
                // rejected derive edit, then its revert). Not after a header delta
                // of this request: its writes stand.
                if intact && headers.is_empty() {
                    caches.gen_reuse.hold(p.reuse_stamp);
                    front.kept[usize::from(walk_instances)] = Some(KeptProgram { program: p, edits: Some(edits), bases, prefer: false, recheck });
                }
                return Err(why);
            }
        }
    }
    // Const and static initializers are checked as bodies at the end of
    // collect (check/const_body.rs) and read fn signatures and derive
    // lists as fn bodies do: after a header or derive delta the ones whose
    // reads moved check again, and any error sends the request to the
    // full path. Only the keys the deltas can move compare (the header
    // delta's `Touched`, the derive delta's reach); the oracle proves each
    // keyed clean set with the full compare.
    if !headers.is_empty() || !derives.is_empty() {
        let mut errs = Vec::new();
        let mut touched = caches.header_moves.as_mut();
        // The derive delta's answers for every key the stored sets read, in
        // parallel from its tables (`derive_keys_moved`).
        let tables = caches.derive_tables.take();
        let mut dmoves = derive_reach.as_ref().map(|r| match tables {
            Some(t) => crate::driver::graph::DeriveMoves::with_tables(r, t),
            None => crate::driver::graph::DeriveMoves::memoized(r),
        });
        if let Some(m) = dmoves.as_mut() {
            let mut seen: crate::intern::FxMap<crate::driver::graph::ReadKey, ()> = crate::intern::FxMap::default();
            let keys: Vec<crate::driver::graph::ReadKey> =
                p.const_body_reads.iter().flat_map(|(_, r)| r.keys(crate::driver::graph::ReadKeys::none()).copied()).filter(|k| seen.insert(*k, ()).is_none()).collect();
            p.derive_keys_moved(m, &keys);
        }
        let mut moved = |q: &crate::check::collect::Program, k: &crate::driver::graph::ReadKey| {
            touched.as_mut().is_some_and(|t| t.hit(q, k)) || dmoves.as_mut().is_some_and(|m| q.derive_key_moves(m, k))
        };
        // No Adt or derive list changes from here: deep Adt fingerprints
        // hold across the compare (707 keys of a large reach took 330 ms).
        p.fp_memo.on(p.adts.len());
        let edited: Vec<LocalDefId> = headers.iter().map(|h| LocalDefId(h.fn_index as u32)).collect();
        let unproven = crate::check::const_body::check_dirty(&mut p, &mut errs, &mut moved, super::item_oracle::on(), &edited);
        p.fp_memo.off();
        if unproven > 0 {
            super::item_oracle::fail("keyed clean const body has dirty reads", "item", &unproven.to_string());
        }
        super::laps::mark("collect/kept const bodies");
        if !errs.is_empty() {
            return Err("const body");
        }
    }
    // An edited fn that returns `impl Trait`: collect reveals its hidden
    // type from the new body, so the program stands only while that type
    // does (`Front::rpit_edit` sends the request on to collect otherwise).
    let plain = |i: &usize| p.gx.fn_class.get(*i) == Some(&FnClass::Plain);
    let mut rpit: Vec<usize> = edits.iter().filter(|e| e.rpit).filter_map(|e| e.fn_index).filter(plain).collect();
    rpit.sort_unstable();
    rpit.dedup();
    for fn_index in rpit {
        let (record_reads, unwind) = (p.record_reads, p.unwind);
        (p.record_reads, p.unwind) = (true, false);
        let stands = crate::check::opaque::hidden_stands(&mut p, LocalDefId(fn_index as u32));
        (p.record_reads, p.unwind) = (record_reads, unwind);
        if !stands {
            if headers.is_empty() && derives.is_empty() {
                put_back(front, caches, p, edits, bases, recheck);
            }
            return Err("hidden type");
        }
    }
    // An edited template checks again as collect's template check does:
    // its old picks and closure call kinds go, the check records new ones.
    // So does a template whose last check had errors (`KeptProgram::recheck`):
    // its error stands until a check passes, as in a collect.
    let mut template_errs = Vec::new();
    let mut seen: Vec<usize> = Vec::new();
    let mut errored: Vec<usize> = Vec::new();
    for (t, errs) in header_template_errs.drain(..) {
        errored.push(t);
        seen.push(t);
        template_errs.extend(errs);
    }
    let edited = edits.iter().filter_map(|e| e.fn_index);
    let nested: Vec<usize> = nested_templates.iter().map(|n| n.0).collect();
    // Entries stored from here on are this patch's (the instance replay).
    let start = crate::driver::gen_reuse::stamp_now();
    for fn_index in edited.chain(recheck.iter().copied()).chain(nested) {
        let header = edits.iter().any(|x| x.header && x.fn_index == Some(fn_index));
        if header || p.gx.fn_class.get(fn_index) != Some(&FnClass::Template) || seen.contains(&fn_index) {
            continue;
        }
        seen.push(fn_index);
        let f = LocalDefId(fn_index as u32);
        if !crate::check::generics::template_closures_stand(&mut p, f) {
            return Err("closures");
        }
        let mut ranges: Vec<(u32, u32)> = edits.iter().filter(|x| x.fn_index == Some(fn_index)).map(|x| x.old_exprs).collect();
        // A nested template's old nodes sit in its holder's old range.
        ranges.extend(nested_templates.iter().filter(|n| n.0 == fn_index).map(|n| n.1));
        if ranges.is_empty() {
            ranges.push(p.fn_def(f).exprs);
        }
        p.gx.trait_picks.retain(|x, _| !ranges.iter().any(|r| x.0 >= r.0 && x.0 < r.1));
        p.gx.template_closures.retain(|k, _| k.0 != f);
        p.gx.template_calls.retain(|k, _| k.0 != f);
        // Collect's template check runs before mono: a coercion of a
        // type parameter to `dyn` then needs no concrete vtable.
        let (counts, mono_done) = (p.gx.mono_counts, std::mem::replace(&mut p.gx.mono_done, false));
        // A template's own `impl Trait`: its check stores the hidden type
        // callers reveal, which must stand as for a plain fn.
        let od = crate::check::generics::opaque_def(p.def_id(f));
        let hidden = p.gx.opaque_hidden.get(&od).copied();
        let errs = crate::check::generics::check_template(&mut p, f, &mut caches.gen_reuse);
        if !errs.is_empty() {
            errored.push(fn_index);
        }
        template_errs.extend(errs);
        (p.gx.mono_counts, p.gx.mono_done) = (counts, mono_done);
        if p.gx.opaque_hidden.get(&od).copied() != hidden {
            return Err("hidden type");
        }
    }
    // Discovery checks every plain body when user generics exist; with
    // only the lang enum methods' generics, a build checks the bodies
    // that name one (not tracked here) and a check none.
    // Until here only a template's check again or a delta wrote to the
    // program (its spans aside), so a refusal below can keep it.
    let intact = headers.is_empty() && derives.is_empty() && seen.is_empty();
    let (record_reads, unwind) = (p.record_reads, p.unwind);
    let refused = 'discovery: {
        if p.gx.has_generics && edits.iter().any(|e| e.fn_index.is_some()) {
            if !p.gx.user_generics && walk_instances {
                return Err("lang generics");
            }
            // A header delta's replay (`kept_delta::replay_discovery`) has
            // checked every plain body against its base already, a pending
            // closure map included, as collect does.
            if p.gx.user_generics && headers.is_empty() {
                // As collect runs discovery: before the driver sets these.
                (p.record_reads, p.unwind) = (true, false);
                // The edits are in: deep fingerprints follow the program.
                p.fp_memo.follow_scoped();
                for (fn_index, base) in &bases {
                    if p.gx.fn_class.get(*fn_index) != Some(&FnClass::Plain) {
                        continue;
                    }
                    let f = LocalDefId(*fn_index as u32);
                    crate::driver::graph::FpMemo::sync(&mut p);
                    let (mut checked, discarded) = crate::check::check_fn(&p, f);
                    if checked.closure_map_pending {
                        crate::check::derive_delta::log(&|| format!("kept bases {}: closure map pending\n", p.display_name(p.fn_def(f).name)));
                        break 'discovery Some("discovery");
                    }
                    let out = crate::check::generics::discovery_out(&p, &checked, &discarded);
                    // An output that differs only in types that make Adt
                    // instances stands when those were made before (`made_before`).
                    // A body with errors too: collect uses its output as well
                    // (and notes it unstored), and the driver's check answers
                    // the errors.
                    let makers = match base.as_ref() {
                        Some(b) if b.same(&p, &out, walk_instances) => Some((Vec::new(), Vec::new())),
                        Some(b) if !walks_requests(&p) => b.makers(&out),
                        _ => None,
                    };
                    let Some(makers) = makers else {
                        crate::check::derive_delta::log(&|| {
                            let why = base.as_ref().map_or("no base".to_string(), |b| b.differs(&p, &out));
                            format!("kept bases {}: output differs: {why}\n", p.display_name(p.fn_def(f).name))
                        });
                        break 'discovery Some("discovery");
                    };
                    let reads = std::mem::take(&mut checked.reads);
                    let clean = discarded.is_empty();
                    drop((checked, discarded));
                    if makers.0 != makers.1 {
                        if !made_before(&mut p, f, &makers.0, &makers.1) {
                            crate::check::derive_delta::log(&|| format!("kept bases {}: new types not made before its turn\n", p.display_name(p.fn_def(f).name)));
                            break 'discovery Some("discovery");
                        }
                        crate::check::derive_delta::log(&|| format!("kept bases {}: types made before its turn\n", p.display_name(p.fn_def(f).name)));
                    }
                    let (adt_tys, reqs, closures, vts) = &out;
                    if clean {
                        caches.gen_reuse.store_discovered(&p, f, &reads, adt_tys, reqs, closures, vts);
                    } else if makers.0 != makers.1 {
                        // As collect notes a body with errors: the program holds this
                        // output now, not the stored one (`GenReuse::out_copy`).
                        caches.gen_reuse.note_unstored(&p, f, adt_tys, reqs, closures, vts, None);
                    }
                    caches.gen_reuse.discovery_checked += 1;
                    // Every body type enters the global store, as discovery's
                    // replay does (lowering and codegen read it there).
                    for t in out.0.iter().map(|t| &**t).chain(out.3.iter().flat_map(|(a, b)| [a, b])) {
                        crate::check::generics::build_owned_ty(&mut p, t);
                    }
                }
                // The instances of the templates that checked again, in a
                // check with generic associated consts: as collect walks them.
                if !walk_instances && walks_requests(&p) && seen.iter().any(|&t| instanced.contains_key(&LocalDefId(t as u32))) {
                    let rechecked: Vec<LocalDefId> = seen.iter().map(|&t| LocalDefId(t as u32)).collect();
                    let fn_count = front.fn_loc.len();
                    let stands = |_: LocalDefId| false;
                    if let Err(why) =
                        super::kept_delta::replay_discovery(&mut p, caches, fn_count, false, start, &Vec::new(), &mut |_, _| false, &stands, None, &rechecked, false)
                    {
                        break 'discovery Some(why);
                    }
                }
            }
        }
        None
    };
    p.fp_memo.follow_end();
    (p.record_reads, p.unwind) = (record_reads, unwind);
    if let Some(why) = refused {
        if intact {
            put_back(front, caches, p, edits, bases, recheck);
        }
        return Err(why);
    }
    super::laps::mark("collect/kept bodies");
    // The caller keeps the program with these errors (`keep`).
    front.template_recheck = errored;
    Ok((p, spans, template_errs))
}

/// Puts the kept program back after a refused body patch that wrote
/// nothing to it but its moved spans (the edits say so): the request then
/// collects in full, and when that answers with errors the program stays
/// for the next request (`keep_err`), as after a refused header delta (an
/// edit with a body error, then its fix or revert). The discovery outputs it
/// has stay known when that collect replaces them (`GenReuse::hold`).
fn put_back(front: &mut Front, caches: &mut Caches, p: crate::check::collect::Program, edits: Vec<KeptEdit>, bases: Vec<KeptBase>, recheck: Vec<usize>) {
    caches.gen_reuse.hold(p.reuse_stamp);
    let slot = usize::from(p.gx.walk_instances);
    front.kept[slot] = Some(KeptProgram { program: p, edits: Some(edits), bases, prefer: true, recheck });
}

/// True when discovery makes instances from a body's requests: in a
/// build, and in a check of a program with generic associated consts
/// (`materialize`). An edited body's requests must then stay the same.
pub(super) fn walks_requests(p: &crate::check::collect::Program) -> bool {
    p.gx.walk_instances || !p.gx.assoc_const_tmpls.is_empty()
}

/// The local templates with instances in a check's program (a check of
/// a program with generic associated consts makes them, `walks_requests`),
/// a closure's instances counting for the fn that owns it. An instance
/// replays its template's check, so a kept program may check one of these
/// again only as a build would (it refuses). Empty for a build's program,
/// whose own rules refuse first, and when the check makes no instances.
pub(super) fn instanced_templates(p: &crate::check::collect::Program) -> crate::intern::FxMap<crate::def::LocalDefId, ()> {
    let mut out = crate::intern::FxMap::default();
    if p.gx.walk_instances || !walks_requests(p) {
        return out;
    }
    for info in p.gx.instances.values() {
        let mut f = info.template_local;
        // A closure body fn up to its parent, through nested closures.
        while let Some(g) = f {
            if out.insert(g, ()).is_some() {
                break;
            }
            f = p.gx.closure_fns.get(&g).and_then(|d| p.gx.closures.get(d)).map(|e| e.parent);
        }
    }
    out
}

/// True when `old` and `new`, the instance-making types of fn `x`'s base
/// and new discovery outputs (`OutCopy::makers`; the rest of the two is the
/// same), are the same list once the types whose instances were all made
/// before `x`'s turn in collect's discovery (`generics::made_before_turn`)
/// are left out. Discovery takes the plain bodies in fn order, and the
/// bodies before `x` are the same in a cold collect, so the same instances
/// exist when `x`'s turn begins. Its turn makes nothing from a type left
/// out, and the same instances, in the same order, from the rest: the
/// program holds the instances a cold collect makes, in its order.
pub(super) fn made_before(
    p: &mut crate::check::collect::Program,
    x: crate::def::LocalDefId,
    old: &[Arc<crate::check::generics::OwnedTy>],
    new: &[Arc<crate::check::generics::OwnedTy>],
) -> bool {
    let mut open = |ts: &[Arc<crate::check::generics::OwnedTy>]| -> Vec<usize> {
        (0..ts.len())
            .filter(|&i| {
                let t = crate::check::generics::build_owned_ty(p, &ts[i]);
                !crate::check::generics::made_before_turn(p, t, x)
            })
            .collect()
    };
    let (a, b) = (open(old), open(new));
    a.len() == b.len() && a.iter().zip(&b).all(|(&i, &j)| old[i] == new[j])
}

/// True when the edited fn's new body calls one of `cow_fns` by method
/// or path, or when the edit has no fn to scan (a nested body item).
fn calls_cow_fn(p: &crate::check::collect::Program, fn_index: Option<usize>) -> bool {
    let Some(i) = fn_index else { return true };
    let def = p.fn_def(crate::def::LocalDefId(i as u32));
    p.ast.exprs[def.exprs.0 as usize..def.exprs.1 as usize].iter().any(|e| match e {
        crate::ast::Expr::MethodCall { name, .. } => p.gx.cow_fns.contains(name),
        crate::ast::Expr::Path(segs) => segs.last().is_some_and(|s| p.gx.cow_fns.contains(&s.name)),
        _ => false,
    })
}

/// Moves the span keys, module spans and import record spans of the
/// resolver tables for one edit (`const_init_module` keys are item spans
/// collect looks up).
fn shift_table_spans(tables: &mut ResolvedTables, edit: Edit) {
    if tables.const_init_module.keys().any(|s| edit.plain(*s) != *s) {
        tables.const_init_module = std::mem::take(&mut tables.const_init_module).into_iter().map(|(s, m)| (edit.plain(s), m)).collect();
    }
    for m in &mut tables.modules {
        m.span = edit.plain(m.span);
    }
    // The import records too: no later request reads them before a full
    // resolve rebuilds them, but they stay what a cold resolve of the edited
    // text holds (`LUST_CHECK_RESOLVE=1`, driver/resolve_oracle.rs).
    if let Some((_, scope)) = tables.macro_scopes.get_mut(&edit.file) {
        for e in &mut scope.events {
            e.lo = edit.plain(crate::diag::Span { file: edit.file, lo: e.lo, hi: e.lo, ctxt: crate::diag::CtxtId::ROOT }).lo;
        }
    }
    for b in &mut tables.single_binds {
        b.0 = edit.plain(b.0);
    }
    for p in tables.pending_single.values_mut().flatten() {
        p.span = edit.plain(p.span);
    }
    for a in &mut tables.ambig_single {
        a.0.span = edit.plain(a.0.span);
    }
}

pub(super) fn fn_def_at_mut(ast: &mut Ast, item: usize, sub: Option<usize>) -> &mut FnDef {
    match (&mut ast.items[item].kind, sub) {
        (ItemKind::Fn(d), None) => d,
        (ItemKind::Impl(imp), Some(k)) => &mut imp.fns[k],
        _ => unreachable!("fn_loc out of date"),
    }
}

/// The bodies-mode slot update for a patched request: the item list,
/// fn locations, slots, and heads stand, so only body hashes move. Same
/// rules as `compile::slot_update` in bodies mode: a fn rechecks when
/// its body hash moved, its last check failed, or its C names a dead
/// slot. Returns the fns to check.
///
/// The dead-slot rule (the only part that walks per-fn state) runs for
/// the edited fns only. For any other fn it was settled by the last
/// request's slot update, and nothing since then can flip it: slot
/// assignment and the fn's own `FnOut::used` change only when that fn is
/// regenerated, instance slots only grow, and the compile tail's work
/// preparation re-evaluates the same rule for builds before it reuses
/// any C. The hash and ok scan stays: two word compares per fn, and
/// the ok flags are written by the tail, so no smaller exact set of
/// failed fns exists here.
fn slot_update(front: &mut Front, caches: &mut Caches, hashes: &[u64], edited: &[usize], live: &[bool]) -> Vec<usize> {
    let n = front.ast_fn_count;
    let mut changed = Vec::new();
    for (i, &hash) in hashes.iter().enumerate().take(n) {
        let slot = front.fn_slot[i] as usize;
        if edited.contains(&i)
            && caches.out[slot]
                .used
                .iter()
                .any(|&u| !live.get(u as usize).copied().unwrap_or(false) && !front.inst_slot.get(u as usize).copied().unwrap_or(false))
        {
            caches.ok[slot] = false;
        }
        if front.slot_hash[slot] != hash || !caches.ok[slot] {
            caches.ok[slot] = false;
            caches.has_out[slot] = false;
            caches.slot_reads[slot] = None;
            front.slot_hash[slot] = hash;
            changed.push(i);
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    use crate::driver::{Cmd, Request, Session, SessionKey, compile};
    use std::path::{Path, PathBuf};

    const MODULE: &str = "pub struct Acc {
    pub v: i64,
}

impl Acc {
    pub fn add(&mut self, x: i64) {
        self.v += x;
    }
    pub fn get(&self) -> i64 {
        self.v
    }
}

pub fn helper(x: i64) -> i64 {
    x * 2
}

pub fn run() -> i64 {
    let mut a = Acc { v: 0 };
    for i in 0..10 {
        a.add(helper(i));
    }
    a.get()
}
";

    /// Writes a crate root with `n` module files of `MODULE`.
    fn write_crate(dir: &Path, n: usize) -> PathBuf {
        let _ = std::fs::remove_dir_all(dir);
        std::fs::create_dir_all(dir).unwrap();
        let mut root = String::new();
        for k in 0..n {
            std::fs::write(dir.join(format!("m{k}.rs")), MODULE).unwrap();
            root.push_str(&format!("mod m{k};\n"));
        }
        root.push_str("\nfn main() {\n    let mut t = 0;\n");
        for k in 0..n {
            root.push_str(&format!("    t += m{k}::run();\n"));
        }
        root.push_str("    println!(\"{t}\");\n}\n");
        let path = dir.join("main.rs");
        std::fs::write(&path, root).unwrap();
        path
    }

    fn check(session: &mut Session, root: &Path) -> (i32, String) {
        run(session, root, Cmd::Check)
    }

    fn run(session: &mut Session, root: &Path, cmd: Cmd) -> (i32, String) {
        let req = Request {
            cmd,
            session: SessionKey::synthetic(root, false),
            file: root.to_path_buf(),
            out: root.with_extension("bin"),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 0,
            run_args: None,
            harness: false, cc: false, overlay: Default::default(),
            client: Default::default(),
        };
        let resp = compile(&req, session);
        (resp.code, resp.stderr)
    }

    /// One field of a `lust-visits:` line.
    fn field<'a>(line: &'a str, name: &str) -> &'a str {
        line.split_whitespace().find_map(|kv| kv.strip_prefix(name).and_then(|v| v.strip_prefix('='))).unwrap_or("")
    }

    fn edit(path: &Path, old: &str, new: &str) {
        let text = std::fs::read_to_string(path).unwrap();
        assert!(text.contains(old), "{old}");
        std::fs::write(path, text.replacen(old, new, 1)).unwrap();
    }

    /// A body edit takes the body patch, and what its front end walks
    /// does not grow with the crate: the same edit in a 3-module and a
    /// 12-module crate re-reads one file, builds and moves the same
    /// number of nodes and spans, rescans one item, and checks one body.
    /// The answers match a cold session, and a syntax error in a body
    /// keeps the base for the fix. A no-op check reuses the last answer.
    /// A signature edit resolves in full.
    /// (Collect still walks the whole crate: `collect` grows.)
    #[test]
    fn body_edit_work_does_not_grow_with_the_crate() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-patch-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
            let m1 = dir.join("m1.rs");
            // A body edit that adds a line: every later fn of the file moves.
            edit(&m1, "        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            let v = warm.front.last_visits.clone();
            assert_eq!(field(&v, "path"), "patch", "{v}");
            assert_eq!((field(&v, "files"), field(&v, "scanned"), field(&v, "checked")), ("1", "1", "1"), "{v}");
            per_size.push((field(&v, "nodes").to_string(), field(&v, "spans").to_string()));
            // A body error: the warm answer is the cold answer.
            edit(&m1, "    a.get()\n", "    a.get() + true\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch");
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            // A syntax error resolves in full and fails as cold does; the
            // base stands, so the fix after it is a patch again.
            edit(&m1, "    a.get() + true\n", "    a.get( +\n");
            let (code, err) = check(&mut warm, &root);
            let mut cold = Session::new(dir.join("obj-cold2"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the syntax error");
            assert_ne!(code, 0);
            edit(&m1, "    a.get( +\n", "    a.get()\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            // A no-op check of the same request reuses that answer.
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "reuse");
            // A signature edit: a full resolve again.
            edit(&m1, "pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i64, _k: u8) -> i64 {");
            edit(&m1, "a.add(helper(i));", "a.add(helper(i, 0));");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "patch work (nodes, spans) for 3 and 12 modules");
    }

    /// A crate with a user macro got no per-file span ranges at the
    /// resolve, so each patch used to walk the whole Ast. The first
    /// patch now probes the Ast for the nodes that can hold another
    /// file's spans, and later patches walk one file plus those nodes:
    /// the same edit in a 3-module and a 12-module crate moves the
    /// same number of spans, and the answers match a cold session.
    #[test]
    fn body_edit_with_user_macros_still_walks_one_file() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-patch-macro-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            edit(&root, "mod m0;\n", "#[macro_export]\nmacro_rules! twice { ($e:expr) => { $e * 2 }; }\n\nmod m0;\n");
            edit(&root, "    println!(\"{t}\");\n", "    t += twice!(1);\n    println!(\"{t}\");\n");
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root).0, 0);
            let m1 = dir.join("m1.rs");
            // Two edits: the first probes, the second walks by the plan.
            edit(&m1, "        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            edit(&m1, "        self.v += y - 1;\n", "        self.v += y - 2;\n        self.v += 1;\n");
            let (code, err) = check(&mut warm, &root);
            let v = warm.front.last_visits.clone();
            assert_eq!(field(&v, "path"), "patch", "{v}");
            assert_eq!((field(&v, "files"), field(&v, "checked")), ("1", "1"), "{v}");
            per_size.push((field(&v, "nodes").to_string(), field(&v, "spans").to_string()));
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree");
            assert_eq!(code, 0);
            // An error after the edit reports at the moved position.
            edit(&m1, "    a.get()\n", "    a.get() + true\n");
            let (code, err) = check(&mut warm, &root);
            let mut cold = Session::new(dir.join("obj-cold2"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "patch work (nodes, spans) with macros for 3 and 12 modules: {per_size:?}");
    }

    /// The second body edit in one impl rescans only the edited method
    /// and reuses the other methods' stored body hashes, one of which
    /// returns `impl Trait` (its body hash folds into the item scan).
    /// Every warm answer matches a cold session.
    #[test]
    fn second_edit_in_an_impl_rescans_one_method() {
        let dir = std::env::temp_dir().join(format!("lust-patch-impl-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("m.rs"),
            "pub struct Acc {\n    pub v: i64,\n    pub xs: Vec<i64>,\n}\n\nimpl Acc {\n    pub fn add(&mut self, x: i64) {\n        self.v += x;\n    }\n    pub fn get(&self) -> i64 {\n        self.v\n    }\n    pub fn vals(&self) -> impl Iterator<Item = &i64> {\n        self.xs.iter()\n    }\n}\n\npub fn run() -> i64 {\n    let mut a = Acc { v: 0, xs: vec![1] };\n    a.add(3);\n    a.get() + a.vals().count() as i64\n}\n",
        )
        .unwrap();
        let root = dir.join("main.rs");
        std::fs::write(&root, "mod m;\n\nfn main() {\n    println!(\"{}\", m::run());\n}\n").unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let m = dir.join("m.rs");
        let mut cold_n = 0;
        for (old, new) in [
            ("        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n"),
            ("        self.v\n", "        self.v + 0\n"),
            ("        self.v += y - 1;\n", "        self.v += y - 2;\n        self.v += 1;\n"),
            ("        self.v + 0\n", "        self.v + true\n"),
        ] {
            edit(&m, old, new);
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            cold_n += 1;
            let mut cold = Session::new(dir.join(format!("obj-cold{cold_n}")), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree after editing {old:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module with most kinds of span a collected program keeps: Adts
    /// with generic params, a trait and impls, a `dyn` signature, a
    /// nested fn (an item block), and a generic fn, all after `helper`.
    const RICH: &str = "pub fn helper(x: i64) -> i64 {
    x * 2
}

pub trait Shape {
    fn area(&self) -> i64;
}

pub struct Sq<T> {
    pub s: T,
}

impl Shape for Sq<i64> {
    fn area(&self) -> i64 {
        self.s * self.s
    }
}

pub fn total(s: &dyn Shape) -> i64 {
    s.area()
}

pub fn nested() -> i64 {
    fn inner(x: i64) -> i64 {
        x + 1
    }
    inner(2)
}

pub fn pick<T: Copy>(x: T) -> T {
    x
}

pub fn run() -> i64 {
    let q = Sq { s: 3 };
    total(&q) + nested() + pick(helper(1))
}
";

    /// The stdout of a binary just built. Another test thread's fork can
    /// hold it open for writing for a moment (ETXTBSY): retry then.
    fn run_bin(bin: &Path) -> Vec<u8> {
        for _ in 0..100 {
            match std::process::Command::new(bin).output() {
                Ok(o) => return o.stdout,
                Err(e) if e.kind() == std::io::ErrorKind::ExecutableFileBusy => std::thread::sleep(std::time::Duration::from_millis(20)),
                Err(e) => panic!("{}: {e}", bin.display()),
            }
        }
        panic!("{}: still busy", bin.display())
    }

    /// Every span of a program, sorted (contexts aside: their ids are
    /// per process, not per session).
    fn program_spans(p: &mut crate::check::collect::Program) -> Vec<(u32, u32, u32)> {
        let mut out = Vec::new();
        crate::check::prog_shift::shift_program(p, &mut |s| {
            out.push((s.file.0, s.lo, s.hi));
            s
        });
        out.sort_unstable();
        out
    }

    /// A body edit reuses the kept program instead of collecting, its
    /// collect work does not grow with the crate (3 and 12 modules), and
    /// the kept program's spans after the edit are those of a fresh
    /// collect of the edited text.
    #[test]
    fn kept_program_matches_a_fresh_collect() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-kept-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            for k in 0..n {
                std::fs::write(dir.join(format!("m{k}.rs")), RICH).unwrap();
            }
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            let m1 = dir.join("m1.rs");
            // Adds a line in the first fn of the file: every later item moves.
            edit(&m1, "    x * 2\n", "    let y = x + 1;\n    (y - 1) * 2\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            let v = warm.front.last_visits.clone();
            assert_eq!((field(&v, "path"), field(&v, "kept"), field(&v, "collect")), ("patch", "reuse", "0"), "{v}");
            per_size.push((field(&v, "discovery").to_string(), field(&v, "checked").to_string()));
            let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut fresh, &root), (0, String::new()));
            let (a, b) = (warm.front.kept[0].as_mut().unwrap(), fresh.front.kept[0].as_mut().unwrap());
            assert_eq!(program_spans(&mut a.program), program_spans(&mut b.program), "kept and fresh program spans");
            // A build keeps its own program: after a check-only edit and a
            // check, the next build reuses it too and runs as cold does.
            let (code, err) = run(&mut warm, &root, Cmd::Build);
            assert_eq!(code, 0, "{err}");
            edit(&m1, "    (y - 1) * 2\n", "    (y - 2) * 2\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let bin = root.with_extension("bin");
            let out = run_bin(&bin);
            let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
            assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
            assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
            // A generic fn's body: the kept program checks it again as a
            // template; an error there is collect's error, as cold.
            edit(&m1, "pub fn pick<T: Copy>(x: T) -> T {\n    x\n", "pub fn pick<T: Copy>(x: T) -> T {\n    let y = x;\n    y\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            edit(&m1, "    let y = x;\n    y\n", "    let y = x;\n    y + 1\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let mut cold = Session::new(dir.join("obj-cold-t"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the template error");
            assert_ne!(code, 0);
            edit(&m1, "    let y = x;\n    y + 1\n", "    let y = x;\n    y\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "the fix reuses it too: {}", warm.front.last_visits);
            // An error in the edited body: the warm answer is the cold one.
            edit(&m1, "    (y - 2) * 2\n", "    (y - 1) * true\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "kept program work (discovery, checked) for 3 and 12 modules");
    }

    /// Edits `file` of the crate at `root`, checks it warm, and asserts
    /// the warm answer is a cold session's; returns the warm
    /// `lust-visits:` line.
    fn warm_equals_cold(warm: &mut Session, root: &Path, file: &Path, old: &str, new: &str) -> String {
        edit(file, old, new);
        let got = check(warm, root);
        let dir = root.parent().unwrap().join(format!("obj-cold-{}", warm.front.last_visits.len()));
        let mut cold = Session::new(dir.clone(), false, SessionKey::synthetic(root, false));
        assert_eq!(got, check(&mut cold, root), "warm and cold agree after {new:?}: {}", warm.front.last_visits);
        let _ = std::fs::remove_dir_all(&dir);
        warm.front.last_visits.clone()
    }

    /// A body edit of a blanket impl method whose body coerces a type
    /// parameter to `dyn` checks the template again on the kept program
    /// as collect does (before mono, so no concrete vtable is asked for).
    #[test]
    fn kept_template_dyn_coercion_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-kept-dyn-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("main.rs");
        let src = "use std::any::Any;\n\ntrait AnyValue: Any {\n    fn as_any(&self) -> &dyn Any;\n}\n\n\
                   impl<T: Any> AnyValue for T {\n    fn as_any(&self) -> &dyn Any {\n        self\n    }\n}\n\n\
                   fn main() {\n    println!(\"{}\", 5u8.as_any().is::<u8>());\n}\n";
        std::fs::write(&root, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root), (0, String::new()));
        let v = warm_equals_cold(&mut warm, &root, &root, "        self\n", "        let _e: u32 = 1;\n        self\n");
        assert_eq!((field(&v, "path"), field(&v, "kept")), ("patch", "reuse"), "{v}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module with cfg-disabled code the expander drops: a test module
    /// and a fn for another platform, around active fns.
    const INACTIVE: &str = "pub fn helper(x: i64) -> i64 {
    x * 2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn doubles() {
        assert_eq!(helper(1), 2);
    }
}

#[cfg(not(unix))]
pub fn os_name() -> &'static str {
    \"other\"
}

pub fn run() -> i64 {
    let v: i64 = helper(3);
    v
}

pub trait Twice {
    fn twice(&self) -> i64 {
        #[cfg(test)]
        let _t = 1;
        2
    }
}
";

    /// An edit inside cfg-disabled code takes the body patch with no Ast
    /// node built (`find_inactive_edit`): edit, error, fix, undo, and
    /// another edit each give the cold answer. A grammar error in
    /// disabled code is the cold error (it resolves in full); a type error
    /// there is no error, as in rustc. Tokens the cold passes read (`cfg`,
    /// `#`), and disabled code inside an active body, resolve in full. A
    /// later active error shows its moved line.
    #[test]
    fn inactive_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-inactive-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, INACTIVE).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let path = |v: &str| (field(v, "path").to_string(), field(v, "nodes").to_string());
        let patch = || ("patch".to_string(), "0".to_string());
        let steps: &[(&str, &str, bool)] = &[
            // edit (adds lines), type error (no error in disabled code), fix
            ("        assert_eq!(helper(1), 2);\n", "        let y = 3;\n        assert_eq!(helper(1), y - 1);\n", true),
            ("let y = 3;", "let y: u32 = \"no\";", true),
            ("let y: u32 = \"no\";", "let y = 3;", true),
            // a grammar error: cold rejects; then the fix
            ("let y = 3;", "let y = ;", false),
            ("let y = ;", "let y = 3;", false),
            // undo, then another edit in the other disabled fn
            ("        let y = 3;\n        assert_eq!(helper(1), y - 1);\n", "        assert_eq!(helper(1), 2);\n", true),
            ("    \"other\"\n", "    let s = \"other\";\n    s\n", true),
            // tokens the cold passes read
            ("    let s = \"other\";\n", "    let s = if cfg!(windows) { \"w\" } else { \"other\" };\n", false),
            ("    let s = if cfg!(windows) { \"w\" } else { \"other\" };\n", "    let s = \"other\";\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(path(&v), patch(), "{new:?}: {v}");
            }
        }
        // A disabled statement inside an active body (a trait default
        // method's): its positions would move under the patch.
        let v = warm_equals_cold(&mut warm, &root, &m1, "        let _t = 1;\n", "        let _t = 2;\n");
        assert_eq!((field(&v, "path"), field(&v, "why")), ("resolve", "inactive_in_item"), "{v}");
        // An active error after disabled code that grew: its line moves.
        warm_equals_cold(&mut warm, &root, &m1, "    #[test]\n", "    #[test]\n\n\n");
        let v = warm_equals_cold(&mut warm, &root, &m1, "    v\n}", "    v + true\n}");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose const fn bodies feed a const, an array length, and
    /// a static, read by an active fn.
    const CONSTS: &str = "pub const fn len() -> usize {
    4
}

pub const fn seed() -> i64 {
    3
}

pub const LEN: usize = len();
pub static TABLE: [i64; 2] = [seed(), seed() + 1];

pub fn run() -> i64 {
    let a: [u8; 4] = [0; LEN];
    a.len() as i64 + TABLE[1]
}
";

    /// A const fn body edit patches (no full resolve) and then collects
    /// and walks reads as a cold resolve does: a new value that breaks an
    /// array type is the cold error, the fix passes, and a build after a
    /// static's const fn edit prints the new value, as a cold build does.
    #[test]
    fn const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-constfn-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, CONSTS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        for (old, new) in [("    4\n", "    5\n"), ("    5\n", "    4\n"), ("    3\n}\n\npub const LEN", "    let x = 7;\n    x\n}\n\npub const LEN")] {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Const fns that no const item reads (`unread`), one an array repeat
    /// length in a body reads (`local`), and one a `thread_local!` const
    /// initializer reads (`tls_init`).
    const UNREAD: &str = "use std::cell::Cell;

pub const fn unread(x: u32) -> u32 {
    x + 1
}

pub const fn local() -> usize {
    2
}

pub const fn tls_init() -> u32 {
    9
}

thread_local! {
    static T: Cell<u32> = const { Cell::new(tls_init()) };
}

pub fn run() -> i64 {
    let a = [0u8; local()];
    (unread(3) + T.with(|t| t.get())) as i64 + a.len() as i64
}
";

    /// A body edit of a const fn that no const evaluation can run
    /// (`const_reach.rs`) is a plain body edit: the kept program stands
    /// (no collect). Edit, error, fix, undo, and another edit each give
    /// the cold answer. A const fn a body's array length reads collects
    /// again; so does `unread` once an edit adds such a reader, and
    /// `tls_init`, which a stored check ran (a const overflow there is
    /// the cold error). A build prints what a cold build prints.
    #[test]
    fn unreached_const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-unread-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, UNREAD).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=)
        let steps: &[(&str, &str, &str)] = &[
            ("    x + 1\n", "    let y = x;\n    y + 1\n", "reuse"),
            ("    y + 1\n", "    y + true\n", "reuse"),
            ("    y + true\n", "    y + 1\n", "reuse"),
            ("    let y = x;\n    y + 1\n", "    x + 1\n", "reuse"),
            ("    x + 1\n", "    x * 2 + 1\n", "reuse"),
            ("    2\n}\n\npub const fn tls_init", "    3\n}\n\npub const fn tls_init", "gen_state"),
            ("    9\n", "    let m: u32 = 4294967295;\n    m + 1\n", "gen_state"),
            // The failed reader stored no reads: it rechecks as any failed
            // body does, against the output its failed check made.
            ("    let m: u32 = 4294967295;\n    m + 1\n", "    10\n", "reuse"),
            ("    let a = [0u8; local()];\n", "    let a = [0u8; local()];\n    let _b: [u8; 7] = [0u8; unread(3) as usize];\n", "reuse"),
            ("    x * 2 + 1\n", "    x * 2 + 2\n", "gen_state"),
            ("    x * 2 + 2\n", "    x * 2 + 1\n", "gen_state"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Fns whose signatures hold nodes before the body: parameter
    /// patterns, array lengths in parameter and return types, a method's
    /// tuple pattern.
    const SIGS: &str = "pub const N: usize = 2;

pub fn skip(_: &str) -> i64 {
    1
}

pub fn pair((a, b): (i64, i64), [c, _]: [i64; N]) -> i64 {
    a + b + c
}

pub fn first(xs: [u8; 4]) -> [u8; N] {
    [xs[0], xs[1]]
}

pub struct S;

impl S {
    pub fn get(&self, (x, _y): (i64, i64), _: u8) -> i64 {
        x
    }
}

pub fn run() -> i64 {
    skip(\"a\") + pair((1, 2), [3, 4]) + first([1, 2, 3, 4])[1] as i64 + S.get((5, 6), 7)
}
";

    /// A body edit of a fn whose signature holds patterns or array
    /// lengths takes the body patch, and the kept program stands. Edit,
    /// error, fix, undo, and another edit each give the cold answer
    /// (a name the pattern binds, used and then misspelled, too), and a
    /// build prints what a cold build prints.
    #[test]
    fn signature_nodes_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-sigs-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, SIGS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str)] = &[
            ("    a + b + c\n", "    let d = a * b;\n    d + c\n"),
            ("    d + c\n", "    dd + c\n"),
            ("    dd + c\n", "    d + c + 1\n"),
            ("    let d = a * b;\n    d + c + 1\n", "    a + b + c\n"),
            ("    1\n}\n\npub fn pair", "    let _z: u8 = 3;\n    1\n}\n\npub fn pair"),
            ("    [xs[0], xs[1]]\n", "    [xs[1], xs[0]]\n"),
            ("    [xs[1], xs[0]]\n", "    [xs[1], xs[0], 1]\n"),
            ("    [xs[1], xs[0], 1]\n", "    [xs[1], xs[3]]\n"),
            ("        x\n", "        x + _y\n"),
            ("        x + _y\n", "        x + y\n"),
            ("        x + y\n", "        x * _y\n"),
        ];
        for &(old, new) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), "reuse", "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A fn with nested fns and a nested const, and a generic fn.
    const NESTED: &str = "pub fn outer(k: i64) -> i64 {
    const B: i64 = 3;
    fn twice(v: i64) -> i64 {
        v * 2
    }
    fn wrap(v: i64) -> Vec<i64> {
        vec![v]
    }
    twice(k) + wrap(B).len() as i64
}

pub fn id<T>(x: T) -> T {
    x
}

pub fn run() -> i64 {
    id(outer(4))
}
";

    /// An edit inside a nested fn's own body takes the body patch (braces
    /// may change there), and the kept program stands while the nested
    /// fn's discovery output makes the same instances (`made_before`: a
    /// `Vec<String>` makes none in a check). Edit, error, fix, undo, and another
    /// edit each give the cold answer; a build prints what a cold build
    /// prints.
    #[test]
    fn nested_fn_body_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-nested-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, NESTED).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=)
        let steps: &[(&str, &str, &str)] = &[
            ("        v * 2\n", "        let w = v + B;\n        w * 2\n", "reuse"),
            ("        w * 2\n", "        w * true\n", "reuse"),
            ("        w * true\n", "        if w > 0 { w * 2 } else { 0 }\n", "reuse"),
            ("        let w = v + B;\n        if w > 0 { w * 2 } else { 0 }\n", "        v * 2\n", "reuse"),
            ("        vec![v]\n", "        vec![v, v]\n", "reuse"),
            ("        vec![v, v]\n", "        let s: Vec<String> = id(Vec::new());\n        vec![v + s.len() as i64]\n", "reuse"),
            ("        v * 2\n", "        v * 4\n", "reuse"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Const fns whose results reach only const and static values
    /// (`base` through `SCALE`, `pair` through `PAIRS`, `Num::new` through
    /// a `const` block in `NUMS`), a const that patterns match on, and one
    /// whose result reaches an array length (`width`).
    const VALUES: &str = "pub const fn base() -> i64 {
    3
}

pub const fn pair(a: i64) -> (i64, i64) {
    (a, a + 1)
}

pub const fn width() -> usize {
    2
}

pub struct Num(i64);

impl Num {
    pub const fn new(v: i64) -> Num {
        Num(v)
    }
}

pub const SCALE: i64 = base() * 2;
pub static PAIRS: [(i64, i64); 2] = [pair(1), pair(SCALE)];
pub static NUMS: [Num; 2] = [const { Num::new(4) }; 2];
const W: usize = width();

pub fn run() -> i64 {
    let a: [u8; W] = [0; W];
    let k = match PAIRS[1].0 {
        SCALE => 1,
        _ => 2,
    };
    SCALE + PAIRS[1].1 + k + a.len() as i64 + NUMS[1].0
}
";

    /// A body edit of a const fn whose result reaches only const and
    /// static values keeps the program when every value evaluates as
    /// before (kept=reuse). A new value, a const evaluation error, its
    /// fix, and the undo collect again (the collect error keeps the item
    /// state, so the fix patches); one that reaches an array length always
    /// does. Every answer is the cold one, and a build after a
    /// changed value prints what a cold build prints.
    #[test]
    fn revalued_const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-revalue-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, VALUES).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=; "" for any)
        let steps: &[(&str, &str, &str)] = &[
            ("    3\n}\n\npub const fn pair", "    let b = 3;\n    b\n}\n\npub const fn pair", "reuse"),
            ("    (a, a + 1)\n", "    let n = a + 1;\n    (a, n)\n", "reuse"),
            ("    let n = a + 1;\n    (a, n)\n", "    (a, a + 2)\n", "gen_state"),
            ("    (a, a + 2)\n", "    (a, a + 1)\n", "gen_state"),
            // A collect error (const evaluation overflows) keeps the item
            // state: the fix patches too.
            ("    let b = 3;\n    b\n", "    let b: i64 = 9223372036854775807;\n    b + 1\n", "gen_state"),
            ("    let b: i64 = 9223372036854775807;\n    b + 1\n", "    let b = 4;\n    b\n", "gen_state"),
            ("    let b = 4;\n    b\n", "    let b = 4;\n    let _c = 1;\n    b\n", "reuse"),
            // A const block in a static's value evaluates with the value.
            ("        Num(v)\n", "        let w = v;\n        Num(w)\n", "reuse"),
            ("        let w = v;\n        Num(w)\n", "        Num(v + 1)\n", "gen_state"),
            ("    2\n}\n\npub struct Num", "    let w = 2;\n    w\n}\n\npub struct Num", "gen_state"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if !kept.is_empty() {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
                assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
            }
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A root file that carries a std splice (it calls a std method the
    /// splice defines, `and_then`) and holds fns of its own.
    const SPLICED_ROOT: &str = "use std::collections::HashMap;

mod m0;
mod m1;

fn count(words: &[&str]) -> usize {
    let mut m: HashMap<&str, usize> = HashMap::new();
    for w in words {
        *m.entry(w).or_insert(0) += 1;
    }
    m.len()
}

fn pick(o: Option<usize>) -> usize {
    o.and_then(|n| n.checked_add(1)).unwrap_or(0)
}

fn main() {
    let t = m0::run() + m1::run() + count(&[\"a\", \"b\", \"a\"]) as i64 + pick(Some(2)) as i64;
    println!(\"{t}\");
}
";

    /// An edit in a fn body of a root file that carries the std splice
    /// takes the body patch: the splice's ranges move with it. Edit,
    /// error, fix, undo, and another edit (one that adds lines, so every
    /// std line moves) each give the cold answer, and a build prints what
    /// a cold build prints.
    #[test]
    fn spliced_root_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-spliced-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        std::fs::write(&root, SPLICED_ROOT).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        assert!(warm.front.patch.as_ref().is_some_and(|b| b.spliced), "the root carries the std splice");
        let steps: &[(&str, &str)] = &[
            ("    m.len()\n", "    let n = m.len();\n    n\n"),
            ("    n\n}", "    n + true\n}"),
            ("    n + true\n}", "    n + 1\n}"),
            ("    let n = m.len();\n    n + 1\n", "    m.len()\n"),
            ("    println!", "    let _u = 1;\n    let _v = 2;\n    println!"),
            ("    m.len()\n", "    m.len() * 2\n"),
        ];
        for &(old, new) in steps {
            let v = warm_equals_cold(&mut warm, &root, &root, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
        }
        assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
        // The splice's positions are a fresh resolve's.
        let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut fresh, &root).0, 0);
        let pos = |s: &Session| {
            let b = s.front.patch.as_ref().unwrap();
            (s.front.ast.shipped.clone(), s.front.ast.lang_methods, b.std_ranges.clone(), b.std_methods, b.tables.std_splice_lo, b.tables.std_ranges.clone())
        };
        assert!(pos(&warm) == pos(&fresh), "splice positions after the patches");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Templates whose bodies hold closures.
    const TEMPLATE_CLOSURES: &str = "pub fn map_get<V: Copy>(m: &[(&str, V)], key: &str) -> Option<V> {
    m.iter().find(|(k, _)| *k == key).map(|e| e.1)
}

pub fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    let g = |y: i64| f(y) + 1;
    g(x)
}

pub trait Each<K> {
    fn each(&self, f: &mut dyn FnMut(&K));
}

impl Each<i64> for Vec<i64> {
    fn each(&self, f: &mut dyn FnMut(&i64)) {
        for x in self {
            f(x);
        }
    }
}

pub fn count_if<K>(m: &dyn Each<K>, mut keep: impl FnMut(&K) -> bool, mut on_hit: Option<&mut dyn FnMut(&K)>) -> i64 {
    let mut n = 0;
    m.each(&mut |k| {
        if keep(k) {
            n += 1;
            if let Some(h) = on_hit.as_mut() {
                h(k);
            }
        }
    });
    n
}

pub fn run() -> i64 {
    let v: Vec<i64> = vec![1, 2, 3];
    let mut seen = 0;
    let c = count_if(&v, |x| *x > 1, Some(&mut |_k: &i64| seen += 1));
    map_get(&[(\"a\", 1i64)], \"a\").unwrap_or(0) + apply(|v| v * 2, 3) + c + seen
}
";

    /// A body edit of a template with closures keeps the program while
    /// its closures are the registered ones (as many, same kinds and
    /// signatures); another closure, or one of another kind, collects
    /// again. Edit, error, fix, undo, and another edit each give the cold
    /// answer, and a build prints what a cold build prints.
    #[test]
    fn template_closure_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-tclos-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, TEMPLATE_CLOSURES).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=; "" for any)
        let steps: &[(&str, &str, &str)] = &[
            ("    m.iter().find", "    let n = m.len();\n    let _ = n;\n    m.iter().find", "reuse"),
            ("*k == key", "*k == 1", ""),
            ("*k == 1", "k.len() == key.len() && *k == key", ""),
            ("k.len() == key.len() && *k == key", "*k == key", "reuse"),
            ("    let g = |y: i64| f(y) + 1;\n", "    let g = |y: i64| f(y) + 2;\n", "reuse"),
            ("    let g = |y: i64| f(y) + 2;\n    g(x)\n", "    let g = |y: i64| f(y) + 2;\n    let h = |z: i64| z;\n    h(g(x))\n", "closures"),
            ("    let h = |z: i64| z;\n    h(g(x))\n", "    g(x)\n", "closures"),
            ("    let mut n = 0;\n    m.each", "    let _z = 1;\n    let mut n = 0;\n    m.each", "reuse"),
            ("    let g = |y: i64| f(y) + 2;\n    g(x)\n", "    let mut n = 0;\n    let mut g = |y: i64| {\n        n += 1;\n        f(y) + n\n    };\n    g(x)\n", "closures"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            if !kept.is_empty() {
                assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
            }
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose fns return `impl Trait`: an iterator chain over
    /// closures (gostd `table_ranges`), a closure, a value whose auto traits
    /// a caller needs, a method, and a closure whose kind its body decides.
    const RPIT: &str = "pub struct Table {
    pub r16: &'static [(u16, u16, u16)],
    pub r32: &'static [(u32, u32, u32)],
}

impl Table {
    pub fn starts(&self) -> impl Iterator<Item = i64> + '_ {
        self.r16.iter().map(|t| t.0 as i64)
    }
}

pub struct Bag<T> {
    pub items: Vec<T>,
}

impl<T> Bag<T> {
    pub fn all(&self) -> impl Iterator<Item = &T> + '_ {
        self.items.iter()
    }
}

pub fn ranges(x: &Table) -> impl Iterator<Item = (i64, i64, i64)> + '_ {
    let a = x.r16.iter().map(|&(lo, hi, s)| (i64::from(lo), i64::from(hi), i64::from(s)));
    let b = x.r32.iter().map(|&(lo, hi, s)| (lo as i64, hi as i64, s as i64));
    a.chain(b)
}

pub fn adder(n: i64) -> impl Fn(i64) -> i64 {
    move |x| x + n
}

pub fn token() -> impl Sized {
    7u8
}

pub fn once(s: String) -> impl FnOnce() -> usize {
    move || s.len()
}

fn need_send<T: Send>(_t: T) {}

pub static T: Table = Table { r16: &[(1, 5, 1), (10, 20, 2)], r32: &[(0x10000, 0x10010, 1)] };

pub fn run() -> i64 {
    let mut n = 0;
    for (lo, hi, s) in ranges(&T) {
        n += (hi - lo) / s + 1;
    }
    need_send(adder(1));
    need_send(token());
    let bag = Bag { items: vec![4i64, 5] };
    need_send(bag.all());
    n + adder(2)(3) + T.starts().sum::<i64>() + once(String::from(\"ab\"))() as i64 + bag.all().next().copied().unwrap_or(0)
}
";

    /// A body edit of a fn that returns `impl Trait` takes the body patch.
    /// The kept program stands while the new body reveals the same hidden
    /// type; another hidden type (a caller loses `Send`, a closure captures
    /// another type), a definer error, and its fix collect again and walk
    /// the callers' reads. A generic method's template check stores its
    /// hidden type, which must stand the same way. Each step gives the cold answer, and a build
    /// prints what a cold build prints.
    #[test]
    fn rpit_body_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-rpit-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, RPIT).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=; "" for any)
        let steps: &[(&str, &str, &str)] = &[
            ("    let a = x.r16", "    let lust_bench_edit: u32 = 1;\n    let a = x.r16", "reuse"),
            ("    a.chain(b)\n", "    b.chain(a)\n", "hidden_type"),
            ("    b.chain(a)\n", "    a.chain(b)\n", "hidden_type"),
            ("    let lust_bench_edit: u32 = 1;\n", "", "reuse"),
            ("        self.r16.iter()", "        let _k = 2;\n        self.r16.iter()", "reuse"),
            ("        self.items.iter()\n", "        let _q = 1;\n        self.items.iter()\n", "reuse"),
            ("        self.items.iter()\n", "        self.items.iter().rev()\n", "hidden_type"),
            ("        self.items.iter().rev()\n", "        self.items.iter()\n", "hidden_type"),
            ("        self.items.iter()\n", "        let r = std::rc::Rc::new(1);\n        self.items.iter().filter(move |_| *r > 0)\n", ""),
            ("        let r = std::rc::Rc::new(1);\n        self.items.iter().filter(move |_| *r > 0)\n", "        self.items.iter()\n", ""),
            ("        self.items.iter()\n", "        self.items.iter().map(|x| x)\n", ""),
            ("        self.items.iter().map(|x| x)\n", "        self.items.iter()\n", ""),
            ("    7u8\n", "    std::rc::Rc::new(7u8)\n", "hidden_type"),
            ("    std::rc::Rc::new(7u8)\n", "    7u16\n", "hidden_type"),
            ("    7u16\n", "    7u8\n", "hidden_type"),
            ("    move |x| x + n\n", "    move |x| x + n + \"a\"\n", "hidden_type"),
            // The fix of an error (here and after the `Rc` capture): the
            // program from before the error stays (`put_back`).
            ("    move |x| x + n + \"a\"\n", "    move |x| x + n\n", "reuse"),
            ("    move |x| x + n\n", "    let r = std::rc::Rc::new(n);\n    move |x| x + *r\n", "hidden_type"),
            ("    let r = std::rc::Rc::new(n);\n    move |x| x + *r\n", "    move |x| x + n\n", "reuse"),
            ("    move |x| x + n\n", "    let _z = 0;\n    move |x| x + n\n", "reuse"),
            ("    move || s.len()\n", "    move || {\n        let t = s;\n        t.len()\n    }\n", ""),
            ("    move || {\n        let t = s;\n        t.len()\n    }\n", "    move || s.len()\n", ""),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            if !kept.is_empty() {
                assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
            }
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose fns hold items: a `OnceLock` static, a `LazyLock`
    /// static (its init closure hoists into a hidden fn), and a const and
    /// a fn that reads it.
    const ITEMS: &str = "use std::sync::{LazyLock, OnceLock};

pub fn mode() -> u32 {
    static MODE: OnceLock<u32> = OnceLock::new();
    *MODE.get_or_init(|| 7)
}

pub fn lazy() -> u32 {
    static TABLE: LazyLock<Vec<u32>> = LazyLock::new(|| vec![1, 2, 3]);
    TABLE.len() as u32
}

pub fn nested() -> i64 {
    const K: i64 = 4;
    fn inner(x: i64) -> i64 {
        x + K
    }
    inner(2)
}

pub fn run() -> i64 {
    mode() as i64 + lazy() as i64 + nested()
}
";

    /// An edit around unchanged body items takes the body patch: edit,
    /// error, fix, undo, and another edit each give the cold answer, and a
    /// build prints what a cold build prints. An edit to an item, or one
    /// that moves braces around items, resolves in full.
    #[test]
    fn body_items_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-items-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, ITEMS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, bool)] = &[
            ("    *MODE.get_or_init(|| 7)\n", "    let m = *MODE.get_or_init(|| 7);\n    m + 1\n", true),
            ("    m + 1\n", "    m + true\n", true),
            ("    m + true\n", "    m + 1\n", true),
            ("    let m = *MODE.get_or_init(|| 7);\n    m + 1\n", "    *MODE.get_or_init(|| 7)\n", true),
            ("    inner(2)\n", "    inner(3) * K\n", true),
            ("    TABLE.len() as u32\n", "    let n = TABLE.len();\n    n as u32 + 1\n", true),
            // the item itself, or braces around it
            ("    const K: i64 = 4;\n", "    const K: i64 = 5;\n", false),
            ("    static MODE: OnceLock<u32> = OnceLock::new();\n    *MODE.get_or_init(|| 7)\n", "    {\n        static MODE: OnceLock<u32> = OnceLock::new();\n    }\n    7\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
            // Plain nested fns with no closure: the kept program stands,
            // and its spans are a fresh collect's.
            if new.contains("inner(3)") || new.contains("let n = TABLE.len()") {
                assert_eq!(field(&v, "kept"), "reuse", "{new:?}: {v}");
                let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
                assert_eq!(check(&mut fresh, &root).0, 0);
                let (a, b) = (warm.front.kept[0].as_mut().unwrap(), fresh.front.kept[0].as_mut().unwrap());
                assert_eq!(program_spans(&mut a.program), program_spans(&mut b.program), "kept and fresh program spans");
                let _ = std::fs::remove_dir_all(dir.join("obj-fresh"));
            }
        }
        warm_equals_cold(&mut warm, &root, &m1, "    {\n        static MODE: OnceLock<u32> = OnceLock::new();\n    }\n    7\n", "    static MODE: OnceLock<u32> = OnceLock::new();\n    *MODE.get_or_init(|| 7)\n");
        let v = warm_equals_cold(&mut warm, &root, &m1, "    inner(3) * K\n", "    inner(4) * K\n");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A body edit around a nested fn in a file with an inner `allow`: the
    /// re-parsed nested fn gets the scope's allows, as a whole parse seeds
    /// them, so its body hashes are a full resolve's (the patch oracle
    /// found the missing seed).
    #[test]
    fn nested_fn_under_file_allows_hashes_as_cold() {
        let dir = std::env::temp_dir().join(format!("lust-allow-seed-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        std::fs::write(&m0, format!("#![allow(dead_code)]\n{ITEMS}")).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let v = warm_equals_cold(&mut warm, &root, &m0, "    inner(2)\n", "    inner(3)\n");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // Body hashes hash `Sym` ids: compare with a full resolve of the
        // same text in the same session.
        let hashes = |s: &Session| s.front.chunks[0].scan.fns.iter().map(|f| f.body_hash).collect::<Vec<_>>();
        let patched = hashes(&warm);
        warm.front.patch = None;
        assert_eq!(check(&mut warm, &root).0, 0);
        assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
        assert_eq!(patched, hashes(&warm), "patched and resolved body hashes");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A header edit of a free fn or an inherent method takes the item
    /// patch (path "item"): a where clause, a parameter type, a return
    /// type, each with an error state and the undo, all give the cold
    /// answer; the request after a collect error patches too (the item
    /// state stands, R9). An outline edit (a new generic param) resolves.
    #[test]
    fn item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-item-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, &str)] = &[
            ("pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i64) -> i64 where u32: Copy {", "item"),
            ("pub fn helper(x: i64) -> i64 where u32: Copy {", "pub fn helper(x: i64) -> i64 where String: Copy {", "item"),
            // A collect error keeps the item state (R9): the fix patches.
            ("pub fn helper(x: i64) -> i64 where String: Copy {", "pub fn helper(x: i64) -> i64 {", "item"),
            ("pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i32) -> i64 {", "item"),
            ("pub fn helper(x: i32) -> i64 {", "pub fn helper(x: i64) -> i64 {", "item"),
            ("    pub fn add(&mut self, x: i64) {", "    pub fn add(&mut self, x: i64) where u8: Copy {", "item"),
            ("    pub fn add(&mut self, x: i64) where u8: Copy {", "    pub fn add(&mut self, x: u8) {", "item"),
            // A body error (not a collect error) keeps the item state.
            ("    pub fn add(&mut self, x: u8) {", "    pub fn add(&mut self, x: i64) {", "item"),
            ("pub fn helper(x: i64) -> i64 {", "pub fn helper<T>(x: i64) -> i64 {", "resolve"),
            ("pub fn helper<T>(x: i64) -> i64 {", "pub fn helper(x: i64) -> i64 {", "resolve"),
        ];
        for &(old, new, path) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A method header edit in an impl that also holds methods an
    /// impl-level macro call made, and a method with a nested fn, takes the
    /// item patch: the made methods have no written range (skipped), and
    /// the nested fn's body hash folds in the impl's new content. A header
    /// edit of the method that holds the nested fn resolves. Each state is
    /// the cold answer.
    #[test]
    fn impl_with_made_methods_and_body_items_item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-item-impl-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "macro_rules! getter {\n    ($n:ident, $k:expr) => {\n        pub fn $n(&self) -> i64 {\n            self.0 * $k\n        }\n    };\n}\n\n\
                   pub struct W(i64);\n\nimpl W {\n    getter!(twice, 2);\n\n    \
                   pub fn nested(&self) -> i64 {\n        fn inner(x: i64) -> i64 {\n            x + 1\n        }\n        inner(self.0)\n    }\n\n    \
                   getter!(thrice, 3);\n\n    pub fn sum(&self, k: i64) -> i64 {\n        self.twice() + self.thrice() + k\n    }\n}\n\n\
                   pub fn run() -> i64 {\n    let w = W(2);\n    w.sum(1) + w.nested()\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let sum = "    pub fn sum(&self, k: i64) -> i64 {";
        let steps: &[(&str, &str, &str, i32)] = &[
            (sum, "    pub fn sum(&self, k: i64) -> i64 where u32: Copy {", "item", 0),
            ("    pub fn sum(&self, k: i64) -> i64 where u32: Copy {", "    pub fn sum(&self, k: i64) -> i64 where String: Copy {", "item", 1),
            ("    pub fn sum(&self, k: i64) -> i64 where String: Copy {", "    pub fn sum(&self, k: u8) -> i64 {", "item", 1),
            ("    pub fn sum(&self, k: u8) -> i64 {", sum, "item", 0),
            // The method that holds the nested fn: the item patch, which
            // keeps the nested fn (`same_items`).
            ("    pub fn nested(&self) -> i64 {", "    pub fn nested(&self) -> i64 where u32: Copy {", "item", 0),
            ("    pub fn nested(&self) -> i64 where u32: Copy {", "    pub fn nested(&self) -> i64 {", "item", 0),
            // A body edit of the nested fn's method, then a header edit.
            ("            x + 1\n", "            x + 2\n", "patch", 0),
            (sum, "    pub fn sum(&self, k: i64) -> i64 where i64: Copy {", "item", 0),
            ("    pub fn sum(&self, k: i64) -> i64 where i64: Copy {", sum, "item", 0),
        ];
        for (old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), *path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, *code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A header edit of a fn with `impl Trait` params (APIT) takes the
    /// item patch when the APITs stand (the same synthetic generics): a
    /// where clause, an error and its fix, a new plain param, also after
    /// generics whose bounds hold parens and on a method. A changed,
    /// added, or moved APIT resolves. Each state is the cold answer.
    #[test]
    fn apit_item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-apit-item-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "pub fn any_of(xs: &[u32], mut test: impl FnMut(u32) -> bool) -> bool {\n    xs.iter().any(|&x| test(x))\n}\n\n\
                   pub fn show<F: Fn(u8) -> u8>(f: F, x: impl std::fmt::Debug) -> String {\n    format!(\"{:?} {}\", x, f(1))\n}\n\n\
                   pub struct Acc(i64);\n\nimpl Acc {\n    pub fn each(&self, f: impl Fn(i64) -> i64) -> i64 {\n        f(self.0)\n    }\n}\n\n\
                   pub fn run() -> i64 {\n    let n = any_of(&[1, 2], |x| x > 1) as i64;\n    let _ = show(|x| x + 1, 5u8);\n    \
                   n + Acc(2).each(|v| v * 2)\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let any = "pub fn any_of(xs: &[u32], mut test: impl FnMut(u32) -> bool) -> bool {";
        let any_w = "pub fn any_of(xs: &[u32], mut test: impl FnMut(u32) -> bool) -> bool where u32: Copy {";
        let any_bad = "pub fn any_of(xs: &[u32], mut test: impl FnMut(u32) -> bool) -> bool where String: Copy {";
        let any_k = "pub fn any_of(xs: &[u32], mut test: impl FnMut(u32) -> bool, _k: u8) -> bool {";
        let any_fn = "pub fn any_of(xs: &[u32], mut test: impl Fn(u32) -> bool) -> bool {";
        let any_moved = "pub fn any_of(mut test: impl FnMut(u32) -> bool, xs: &[u32]) -> bool {";
        let show = "pub fn show<F: Fn(u8) -> u8>(f: F, x: impl std::fmt::Debug) -> String {";
        let show_w = "pub fn show<F: Fn(u8) -> u8>(f: F, x: impl std::fmt::Debug) -> String where u8: Copy {";
        let show_2 = "pub fn show<F: Fn(u8) -> u8>(f: F, x: impl std::fmt::Debug, _y: impl Copy) -> String {";
        let each = "    pub fn each(&self, f: impl Fn(i64) -> i64) -> i64 {";
        let each_r = "    pub fn each(&self, f: impl Fn(i64) -> i64) -> i32 {";
        let steps: &[(&str, &str, &str, i32)] = &[
            (any, any_w, "item", 0),
            (any_w, any_bad, "item", 1),
            (any_bad, any, "item", 0),
            (any, any_k, "item", 1),
            (any_k, any, "item", 0),
            (any, any_fn, "resolve", 0),
            (any_fn, any, "resolve", 0),
            (any, any_moved, "resolve", 1),
            (any_moved, any, "resolve", 0),
            (show, show_w, "item", 0),
            (show_w, show, "item", 0),
            (show, show_2, "resolve", 1),
            (show_2, show, "resolve", 0),
            (each, each_r, "item", 1),
            (each_r, each, "item", 0),
        ];
        for &(old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A header edit of a fn whose body calls a user macro takes the item
    /// patch when the body text stands: the body's stored expansion parses
    /// and rewrites with the new header (a param rename, an error and its
    /// fix, a hygienic local in the macro). A body edit in the macro's
    /// input takes the body patch. A macro definition edit, a header and
    /// body edit together,
    /// or another such fn's header edit after a patch of its file resolve
    /// (a patch of another file does not); the header
    /// edit after the definition edit patches with the new expansion.
    /// Each state is the cold answer.
    #[test]
    fn user_macro_body_item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-umacro-item-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m0 = dir.join("m0.rs");
        let src = "macro_rules! args {\n    ($($x:expr),* $(,)?) => { vec![$($x.to_string()),*] };\n}\n\n\
                   macro_rules! tw {\n    ($e:expr) => {{ let t = $e; t + t }};\n}\n\n\
                   pub fn chain(d: &str, n: usize) -> Vec<String> {\n    let mut v = args![d, n];\n    v.push(String::new());\n    v\n}\n\n\
                   pub fn twice(t: i64) -> i64 {\n    tw!(t)\n}\n\n\
                   pub fn run() -> i64 {\n    chain(\"a\", 2).len() as i64 + twice(3)\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let ch = "pub fn chain(d: &str, n: usize) -> Vec<String> {";
        let ch_w = "pub fn chain(d: &str, n: usize) -> Vec<String> where u32: Copy {";
        let ch_bad = "pub fn chain(d: &str, n: usize) -> Vec<String> where String: Copy {";
        let ch_k = "pub fn chain(d: &str, n: usize, _k: u8) -> Vec<String> {";
        let ch_e = "pub fn chain(e: &str, n: usize) -> Vec<String> {";
        let call = "    let mut v = args![d, n];";
        let call_3 = "    let mut v = args![d, n, 1];";
        let def = "{ vec![$($x.to_string()),*] }";
        let def_2 = "{ [$(format!(\"{}\", $x)),*].to_vec() }";
        let tw = "pub fn twice(t: i64) -> i64 {";
        let tw_w = "pub fn twice(t: i64) -> i64 where i64: Copy {";
        // A patch in another file names nothing the body's expansion does.
        let m1 = dir.join("m1.rs");
        let v = warm_equals_cold(&mut warm, &root, &m1, "pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i64) -> i64 where u32: Copy {");
        assert_eq!(field(&v, "path"), "item", "{v}");
        let steps: &[(&str, &str, &str, i32)] = &[
            (ch, ch_w, "item", 0),
            (ch_w, ch_bad, "item", 1),
            (ch_bad, ch, "item", 0),
            (ch, ch_k, "item", 1),
            (ch_k, ch, "item", 0),
            (ch, ch_e, "item", 1),
            (ch_e, ch, "item", 0),
            // Another fn's body after a patch of its own file: the stored
            // expansion may name moved spans, so it resolves; the undo
            // patches.
            (tw, tw_w, "resolve", 0),
            (tw_w, tw, "item", 0),
            (call, call_3, "patch", 0),
            (call_3, call, "patch", 0),
            (&format!("{ch}\n{call}"), &format!("{ch_w}\n{call_3}"), "resolve", 0),
            (&format!("{ch_w}\n{call_3}"), &format!("{ch}\n{call}"), "resolve", 0),
            (def, def_2, "resolve", 0),
            (ch, ch_w, "item", 0),
            (ch_w, ch, "item", 0),
            (def_2, def, "resolve", 0),
        ];
        for (old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), *path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, *code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A body edit in a fn that calls user macros takes the body patch:
    /// its file expands again under the full resolve's macro environment
    /// (`expand_by_file`). Macros from the crate root (textual scope),
    /// the same file (one defined after the edit, whose definition moves),
    /// another file by `$crate` path, hygienic locals, a closure in a
    /// duplicated `$body`, an error and its fix; another body's local
    /// `macro_rules!` of the same name stays its own; `thread_local!`
    /// statics after the edit (their hidden init fns have no `{ .. }`
    /// body of their own to blank). Refused: an undefined
    /// macro, a `macro_rules!` or a `static` in the body. Each state is the
    /// cold answer.
    #[test]
    fn user_macro_body_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-umacro-body-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("main.rs");
        let main = "macro_rules! sq {\n    ($e:expr) => { $e * $e };\n}\n\nmod m0;\nmod m1;\n\n\
                    fn main() {\n    let t = m0::run() + m1::run();\n    println!(\"{t}\");\n}\n";
        std::fs::write(&root, main).unwrap();
        let m1 = "#[macro_export]\nmacro_rules! with_val {\n    ($v:expr, |$d:ident| $body:expr) => {{\n        let v__: i64 = $v;\n        \
                  match v__ {\n            0 => {\n                let $d = v__;\n                $body\n            }\n            \
                  _ => (|$d: i64| $body)(v__),\n        }\n    }};\n}\n\npub fn helper(x: i64) -> i64 {\n    x + 1\n}\n\n\
                  pub fn run() -> i64 {\n    helper(2)\n}\n";
        std::fs::write(dir.join("m1.rs"), m1).unwrap();
        let m0 = dir.join("m0.rs");
        let src = "macro_rules! tw {\n    ($e:expr) => {{ let t = $e; t + t }};\n}\n\n\
                   pub fn calc(a: i64) -> i64 {\n    let v = tw!(a);\n    v + sq!(a)\n}\n\n\
                   pub fn pick(n: i64) -> i64 {\n    crate::with_val!(n, |d| d + 1)\n}\n\n\
                   pub fn shadow() -> i64 {\n    macro_rules! tw {\n        ($e:expr) => { $e * 100 };\n    }\n    tw!(1)\n}\n\n\
                   macro_rules! late {\n    ($e:expr) => { $e - 1 };\n}\n\n\
                   pub fn after(n: i64) -> i64 {\n    late!(n) + tw!(n)\n}\n\n\
                   thread_local! {\n    static CELL: std::cell::Cell<i64> = std::cell::Cell::new(1);\n    \
                   static CELL2: std::cell::Cell<i64> = std::cell::Cell::new(2);\n}\n\n\
                   pub fn cells() -> i64 {\n    CELL.with(|c| c.get()) + CELL2.with(|c| c.get())\n}\n\n\
                   pub fn run() -> i64 {\n    calc(3) + pick(4) + after(5) + shadow() + cells()\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let v0 = "    let v = tw!(a);\n";
        let steps: &[(&str, &str, &str, i32)] = &[
            (v0, "    let v = tw!(a + 1);\n", "patch", 0),
            ("    let v = tw!(a + 1);\n", v0, "patch", 0),
            // More lines: `late`'s definition after the edit moves.
            (v0, "    let v = tw!(a);\n    let _w: u32 = tw!(1u32);\n", "patch", 0),
            ("    let _w: u32 = tw!(1u32);\n", "    let _w: u32 = tw!(1u64);\n", "patch", 1),
            ("    let _w: u32 = tw!(1u64);\n", "    let _w: u32 = tw!(1u32);\n", "patch", 0),
            ("    late!(n) + tw!(n)\n", "    late!(n * 2) + tw!(sq!(n))\n", "patch", 0),
            ("crate::with_val!(n, |d| d + 1)", "crate::with_val!(n, |d| d * 2 + sq!(d))", "patch", 0),
            ("crate::with_val!(n, |d| d * 2 + sq!(d))", "crate::with_val!(n, |d| d * 2 + t)", "patch", 1),
            // Hygiene: the macro's own `t` is not the body's.
            ("crate::with_val!(n, |d| d * 2 + t)", "let t = 7;\n    crate::with_val!(n, |d| d * 2 + t) + tw!(t)", "patch", 0),
            // A resolve error writes no visits line (`-`: not checked).
            ("    let _w: u32 = tw!(1u32);\n", "    let _w: u32 = nope!(1u32);\n", "-", 1),
            ("    let _w: u32 = nope!(1u32);\n", "    let _w: u32 = tw!(1u32);\n", "patch", 0),
            (v0, "    macro_rules! m2 {\n        () => { 2 };\n    }\n    let v = tw!(a) + m2!();\n", "resolve", 0),
            ("    let v = tw!(a) + m2!();\n", "    let v = tw!(a) + m2!() + sq!(2);\n", "resolve", 0),
            ("    macro_rules! m2 {\n        () => { 2 };\n    }\n    let v = tw!(a) + m2!() + sq!(2);\n", v0, "resolve", 0),
            ("    late!(n * 2) + tw!(sq!(n))\n", "    static S: i64 = 1;\n    late!(n * 2) + S\n", "resolve", 0),
            ("    static S: i64 = 1;\n    late!(n * 2) + S\n", "    late!(n) + tw!(n)\n", "resolve", 0),
            (v0, "    let v = tw!(a) - 1;\n", "patch", 0),
        ];
        for (old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert!(*path == "-" || field(&v, "path") == *path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, *code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A derive list edit takes the item patch in full mode: a trait out
    /// (an error, then its fix) and in, each the cold answer. An edit
    /// outside the derive list's names (an attribute) resolves.
    #[test]
    fn derive_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-derive-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "/// A point.\n#[derive(Clone, Copy, Debug, PartialEq)]\npub struct P {\n    x: i64,\n}\n\n\
                   fn twice(p: P) -> (P, P) {\n    (p, p)\n}\n\npub fn run() -> i64 {\n    let (a, b) = twice(P { x: 2 });\n    \
                   println!(\"{:?}\", a == b);\n    a.x\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, &str)] = &[
            ("#[derive(Clone, Copy, Debug, PartialEq)]", "#[derive(Clone, Debug, PartialEq)]", "item"),
            ("#[derive(Clone, Debug, PartialEq)]", "#[derive(Clone, Copy, Debug, PartialEq)]", "item"),
            ("#[derive(Clone, Copy, Debug, PartialEq)]", "#[derive(Clone, Copy, Debug, PartialEq, Default)]", "item"),
            ("#[derive(Clone, Copy, Debug, PartialEq, Default)]", "#[derive(Clone, Copy, Debug, PartialEq)]", "item"),
            ("#[derive(Clone, Copy, Debug, PartialEq)]", "#[derive(Clone, Copy, Debug, PartialEq)]\n#[repr(C)]", "resolve"),
        ];
        for &(old, new, path) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Refused derive deltas (sigedit Sol review 2, item 3), each the cold
    /// answer: a rejected derive edit (a derive diagnostic) undoes its
    /// delta and keeps the program, so its revert takes the delta again,
    /// also after an unrelated body edit, after repeated rejects, and after
    /// a build of the rejected state. A trait the Adt never derived gets a
    /// record from collect's kernel. An associated-type impl bounded by Copy
    /// refuses only toggles whose reach it can involve.
    #[test]
    fn derive_refusals_keep_the_program() {
        let dir = std::env::temp_dir().join(format!("lust-derive-undo-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "#[derive(Clone, Copy, Debug, PartialEq)]\npub struct P {\n    x: i64,\n}\n\n#[derive(Clone, Copy)]\npub struct Q(u8);\n\n\
                   pub struct Rep<T>(T);\n\nimpl<T: Copy> Iterator for Rep<T> {\n    type Item = T;\n    fn next(&mut self) -> Option<T> {\n        \
                   Some(self.0)\n    }\n}\n\nfn twice(p: P) -> (P, P) {\n    (p, p)\n}\n\npub fn run() -> i64 {\n    \
                   let (a, b) = twice(P { x: 2 });\n    let mut r = Rep(3u8);\n    let q = Q(r.next().unwrap_or(0));\n    \
                   println!(\"{:?} {}\", a == b, q.clone().0);\n    a.x\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let (full, no_clone) = ("#[derive(Clone, Copy, Debug, PartialEq)]", "#[derive(Copy, Debug, PartialEq)]");
        let steps: &[(&str, &str, &str)] = &[
            // Copy without Clone: a derive diagnostic, then the revert.
            (full, no_clone, "derive_diag"),
            (no_clone, full, "reuse"),
            // An unrelated body edit while the reject stands.
            (full, no_clone, "derive_diag"),
            ("    a.x\n", "    a.x + 1\n", "derive_diag"),
            (no_clone, full, "reuse"),
            // Repeated rejects.
            (full, no_clone, "derive_diag"),
            (no_clone, "#[derive(Copy, Debug)]", "derive_diag"),
            ("#[derive(Copy, Debug)]", full, "reuse"),
            // First-ever derives: Hash and Eq in, out, in again.
            (full, "#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]", "reuse"),
            ("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]", full, "reuse"),
            (full, "#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]", "reuse"),
            // Rep's impl (bounded by Copy) cannot involve Q's reach.
            ("#[derive(Clone, Copy)]\npub struct Q", "#[derive(Clone)]\npub struct Q", "reuse"),
            ("#[derive(Clone)]\npub struct Q", "#[derive(Clone, Copy)]\npub struct Q", "reuse"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            // The body edit takes the body patch, the others the item patch.
            assert!(matches!(field(&v, "path"), "item" | "patch"), "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
        }
        // A build of a rejected state, then the revert checks on the kept
        // check program.
        let full_hash = "#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]";
        edit(&m0, full_hash, "#[derive(Copy, Debug, PartialEq, Eq, Hash)]");
        let built = run(&mut warm, &root, Cmd::Build);
        let cold_dir = dir.join("obj-cold-build");
        let mut cold = Session::new(cold_dir.clone(), false, SessionKey::synthetic(&root, false));
        assert_eq!(built, run(&mut cold, &root, Cmd::Build), "warm and cold builds agree");
        assert_ne!(built.0, 0);
        let v = warm_equals_cold(&mut warm, &root, &m0, "#[derive(Copy, Debug, PartialEq, Eq, Hash)]", full_hash);
        assert_eq!(field(&v, "kept"), "reuse", "{v}");
        // A generic fn whose signature projects through Rep's impl, with
        // an instance at Rep<Q>: Q's Copy toggle refuses.
        edit(&m0, "pub fn run() -> i64 {\n", "fn first<I: Iterator>(mut i: I) -> Option<I::Item> {\n    i.next()\n}\n\npub fn run() -> i64 {\n    let _f = first(Rep(Q(1)));\n");
        assert_eq!(check(&mut warm, &root).0, 0);
        let v = warm_equals_cold(&mut warm, &root, &m0, "#[derive(Clone, Copy)]\npub struct Q", "#[derive(Clone)]\npub struct Q");
        assert_eq!(field(&v, "kept"), "derive_assoc_impl", "{v}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A trait impl method's header edit takes the item patch in full
    /// mode: its callers (`+`, a `for` loop) never name it. Same types
    /// spelled another way, a type change the trait rejects (a collect
    /// error), its fix, then the revert.
    #[test]
    fn trait_impl_method_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-trait-item-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "pub struct V(i64);\n\nimpl std::ops::Add for V {\n    type Output = V;\n    fn add(self, o: V) -> V {\n        V(self.0 + o.0)\n    }\n}\n\n\
                   pub struct C {\n    n: u32,\n}\n\nimpl Iterator for C {\n    type Item = u32;\n    fn next(&mut self) -> Option<u32> {\n        \
                   self.n = self.n.checked_sub(1)?;\n        Some(self.n)\n    }\n}\n\n\
                   pub fn run() -> i64 {\n    let mut t = (V(1) + V(2)).0;\n    for x in (C { n: 3 }) {\n        t += x as i64;\n    }\n    t\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, &str)] = &[
            ("    fn add(self, o: V) -> V {", "    fn add(self, o: V) -> Self {", "item"),
            ("    fn next(&mut self) -> Option<u32> {", "    fn next(&mut self) -> Option<Self::Item> {", "item"),
            ("    fn add(self, o: V) -> Self {", "    fn add(self, o: Self) -> Self {", "item"),
            ("    fn next(&mut self) -> Option<Self::Item> {", "    fn next(&mut self) -> Option<u64> {", "item"),
            ("    fn next(&mut self) -> Option<u64> {", "    fn next(&mut self) -> Option<u32> {", "item"),
            ("    fn add(self, o: Self) -> Self {", "    fn add(self, o: V) -> V {", "item"),
        ];
        for &(old, new, path) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A header edit of a fn whose body holds pure builtin macros or a
    /// statement attribute takes the item patch: the body expands as the
    /// body patch's does. A body error (the caller's, then the fn's own)
    /// is the cold answer and keeps the item state.
    #[test]
    fn expander_body_item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-pure-item-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "fn pick(x: i64) -> bool {\n    matches!(x, 1 | 2)\n}\n\nfn mk(n: usize) -> Vec<i64> {\n    #[allow(unused_variables)]\n    let unused = 1;\n    vec![0; n]\n}\n\n\
                   pub fn run() -> i64 {\n    let v = mk(2);\n    if pick(v.len() as i64) { 1 } else { 0 }\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, &str, i32)] = &[
            ("fn mk(n: usize) -> Vec<i64> {", "fn mk(n: usize) -> Vec<i64> where i64: Copy {", "item", 0),
            ("fn pick(x: i64) -> bool {", "fn pick(x: i32) -> bool {", "item", 1),
            ("fn pick(x: i32) -> bool {", "fn pick(x: i64) -> bool {", "item", 0),
            ("fn mk(n: usize) -> Vec<i64> where i64: Copy {", "fn mk(n: u8) -> Vec<i64> {", "item", 1),
        ];
        for &(old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A const fn's header edit takes the item patch in full mode: the
    /// const it computes moves, and `run` reads that const (in an array
    /// length) without naming the fn.
    #[test]
    fn const_fn_item_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-const-item-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        let m0 = dir.join("m0.rs");
        let src = "pub const fn sq(x: i64) -> i64 {\n    x * x\n}\n\nconst N: i64 = sq(3);\n\n\
                   pub fn run() -> i64 {\n    let a: [u8; 9] = [0; N as usize];\n    a.len() as i64\n}\n";
        std::fs::write(&m0, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, &str, i32)] = &[
            ("pub const fn sq(x: i64) -> i64 {\n    x * x\n", "pub const fn sq(x: i32) -> i64 {\n    x as i64 * x as i64\n", "item", 0),
            ("pub const fn sq(x: i32) -> i64 {\n    x as i64 * x as i64\n", "pub const fn sq(x: i32) -> i64 {\n    x as i64 * x as i64 + 1\n", "patch", 1),
            ("pub const fn sq(x: i32) -> i64 {\n    x as i64 * x as i64 + 1\n", "pub const fn sq(x: i64) -> i64 {\n    x * x\n", "item", 0),
            ("pub const fn sq(x: i64) -> i64 {\n    x * x\n", "pub const fn sq(x: i16) -> i64 {\n    x as i64 * x as i64 + 1\n", "item", 1),
        ];
        for &(old, new, path, code) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m0, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
            assert_eq!(check(&mut warm, &root).0, code, "{new:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The last fn of the root file sits right before the std splice: an
    /// edit that grows it (its header, then its body) must rewrite it as
    /// user code, as a full resolve does (the splice start moves with the
    /// edit).
    #[test]
    fn edit_before_std_splice_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-splice-{}", std::process::id()));
        let root = write_crate(&dir, 1);
        std::fs::write(dir.join("m0.rs"), ITEMS).unwrap();
        let tail = "\n#[allow(dead_code)]\npub(crate) fn sx(x: u32) -> u64 { x as u64 }\n";
        let text = std::fs::read_to_string(&root).unwrap() + tail;
        std::fs::write(&root, text).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        assert!(!warm.front.ast.shipped.is_empty(), "the root has a std splice");
        let steps: &[(&str, &str, &str)] = &[
            ("fn sx(x: u32) -> u64 { x as u64 }", "fn sx(x: u8) -> u16 { x as u16 }", "item"),
            ("fn sx(x: u8) -> u16 { x as u16 }", "fn sx(x: u8) -> u16 { let y = x as u16; y + y }", "patch"),
            ("fn sx(x: u8) -> u16 { let y = x as u16; y + y }", "fn sx(x: u32) -> u64 { x as u64 }", "item"),
        ];
        for &(old, new, path) in steps {
            let v = warm_equals_cold(&mut warm, &root, &root, old, new);
            assert_eq!(field(&v, "path"), path, "{new:?}: {v}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose fn bodies call pure builtin macros the expander owns.
    const MACROS: &str = "use std::fmt::Write;

#[derive(Clone, Copy)]
pub enum K {
    A,
    B(i64),
}

pub fn is_b(k: K) -> bool {
    matches!(k, K::B(_))
}

pub fn show(k: K) -> String {
    let mut s = String::new();
    write!(s, \"{}\", is_b(k) as i64).unwrap();
    s
}

pub fn run() -> i64 {
    debug_assert!(is_b(K::B(1)));
    show(K::A).len() as i64 + is_b(K::B(2)) as i64
}
";

    /// A body that calls pure builtin macros (`matches!`, `write!`,
    /// `debug_assert!`) takes the body patch: it expands alone. Edit,
    /// error, fix, undo, another edit, and a build all give the cold
    /// answer. A macro that reads a position (`line!`) resolves in full.
    #[test]
    fn pure_macro_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-macros-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, MACROS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, bool)] = &[
            ("    matches!(k, K::B(_))\n", "    let b = matches!(k, K::B(x) if x > 0);\n    b\n", true),
            ("    b\n", "    b + 1\n", true),
            ("    b + 1\n", "    b\n", true),
            ("    let b = matches!(k, K::B(x) if x > 0);\n    b\n", "    matches!(k, K::B(_))\n", true),
            ("    write!(s, \"{}\", is_b(k) as i64).unwrap();\n", "    writeln!(s, \"{} {}\", is_b(k) as i64, 2).unwrap();\n", true),
            ("    debug_assert!(is_b(K::B(1)));\n", "    debug_assert_eq!(is_b(K::B(1)), true);\n", true),
            ("    debug_assert_eq!(is_b(K::B(1)), true);\n", "    debug_assert_eq!(is_b(K::B(1)), true, \"at {}\", line!());\n", false),
            ("    debug_assert_eq!(is_b(K::B(1)), true, \"at {}\", line!());\n", "    debug_assert_eq!(is_b(K::B(1)), true);\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
        }
        let v = warm_equals_cold(&mut warm, &root, &m1, "    s\n}", "    let t = matches!(s.len(), 1 | 2);\n    if t { s } else { String::new() }\n}");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // cfg! and a cfg'd statement expand with the crate cfg; an unknown
        // cfg name is the cold error.
        let steps: &[(&str, &str, bool)] = &[
            ("    let mut s = String::new();\n", "    let mut s = String::new();\n    if cfg!(windows) {\n        s.push('w');\n    }\n", true),
            ("        s.push('w');\n", "        s.push('v');\n", true),
            ("    let mut s = String::new();\n", "    let mut s = String::new();\n    #[cfg(test)]\n    let _t = 1;\n", true),
            ("    let _t = 1;\n", "    let _t = 2;\n", true),
            ("cfg!(windows)", "cfg!(lust_no_such_name)", false),
            ("cfg!(lust_no_such_name)", "cfg!(windows)", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
        }
        // A user macro of another name: bodies that call builtins patch.
        let dbl = "macro_rules! dbl {\n    ($e:expr) => {\n        $e * 2\n    };\n}\n\npub fn d() -> i64 {\n    dbl!(1)\n}\n\n";
        warm_equals_cold(&mut warm, &root, &m1, "pub fn is_b(", &format!("{dbl}pub fn is_b("));
        let v = warm_equals_cold(&mut warm, &root, &m1, "    matches!(k, K::B(_))\n", "    matches!(k, K::B(1))\n");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // A user macro named like a builtin: the expander may pick it.
        let own = "macro_rules! matches {\n    ($($t:tt)*) => {\n        false\n    };\n}\n\n";
        warm_equals_cold(&mut warm, &root, &m1, "pub fn d()", &format!("{own}pub fn d()"));
        let v = warm_equals_cold(&mut warm, &root, &m1, "    matches!(k, K::B(1))\n", "    matches!(k, K::B(2))\n");
        assert_eq!(field(&v, "path"), "resolve", "{v}");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module with nested statics in two fns and a generic fn.
    const STATICS: &str = "use std::sync::atomic::{AtomicI64, Ordering};

pub fn bump() -> i64 {
    static N: AtomicI64 = AtomicI64::new(10);
    N.fetch_add(1, Ordering::Relaxed)
}

pub fn twice<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

pub fn base() -> i64 {
    static B: AtomicI64 = AtomicI64::new(5);
    B.load(Ordering::Relaxed)
}

pub fn run() -> i64 {
    let (a, b) = twice(bump());
    a + b + base()
}
";

    /// A full resolve (a signature edit) in a crate whose fns hold statics
    /// keeps generic reuse while the statics keep their indexes: few
    /// bodies check. A new static before the others moves their indexes:
    /// collect runs again without reuse, and a build prints what a cold
    /// build prints.
    #[test]
    fn full_resolve_keeps_reuse_while_statics_stand() {
        let dir = std::env::temp_dir().join(format!("lust-statics-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, STATICS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let all: usize = field(&warm.front.last_visits, "checked").parse().unwrap();
        let v = warm_equals_cold(&mut warm, &root, &m1, "pub fn base() -> i64 {", "pub fn base() -> i64 {\n    let _k = 1;");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // A signature edit takes the item patch; with no patch base it
        // resolves in full, which this test is about.
        warm.front.patch = None;
        let v = warm_equals_cold(&mut warm, &root, &m1, "pub fn twice<T: Copy>(x: T) -> (T, T) {", "pub fn twice<T: Copy + Clone>(x: T) -> (T, T) {");
        assert_eq!(field(&v, "path"), "resolve", "{v}");
        let checked: usize = field(&v, "checked").parse().unwrap();
        assert!(checked < all, "a signature edit checks {checked} of {all} bodies: {v}");
        // A static before the others, in a new fn.
        warm_equals_cold(&mut warm, &root, &m1, "pub fn bump() -> i64 {", "pub fn first() -> i64 {\n    static F: AtomicI64 = AtomicI64::new(100);\n    F.load(Ordering::Relaxed)\n}\n\npub fn bump() -> i64 {");
        warm_equals_cold(&mut warm, &root, &m1, "    a + b + base()\n", "    a + b + base() + first()\n");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The shadow scans: a macro defined or imported under a builtin's
    /// name counts; prose and casts do not.
    #[test]
    fn shadow_scans() {
        use super::{shadows_builtin, shadows_parser_macro};
        assert!(shadows_parser_macro("use a::m as vec;"));
        assert!(shadows_parser_macro("macro_rules! println { () => {} }"));
        assert!(shadows_builtin("use a::{m as matches, n};"));
        assert!(shadows_builtin("macro_rules! write { () => {} }"));
        assert!(shadows_builtin("macro_rules! $name { () => {} }"));
        assert!(!shadows_builtin("($value as $repr);"));
        assert!(!shadows_builtin("// treated as line terminators."));
        assert!(!shadows_builtin("let x = y as u8;"));
        assert!(!shadows_builtin("macro_rules! dbl { () => {} }"));
    }
}
