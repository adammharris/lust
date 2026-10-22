// Session state for the compile pipeline: everything an edit can reuse (the AST,
// per-function body hashes, generated C, glue, and object files). One session
// serves one crate under one selection: `lust daemon` keeps one session per
// `SessionKey` alive between requests (docs/ARCH.md section 1.8); a plain
// `lust check` uses a fresh session once. The pipeline itself is in compile.rs.
use crate::ast::Ast;
use crate::cgen::{FnOut, GlueSet};
use crate::def::{CrateIds, DiskDefId, LOCAL_CRATE, stable_crate_hash};
use crate::diag::SourceMap;
use crate::intern::{FxMap, Interner, Known};
use crate::lexer::Lexed;
use crate::protocol::SessionKey;
use crate::scan;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Parsed program state. Owned separately from the caches so both can be borrowed at once.
pub(crate) struct Front {
    /// Shared with the request's `Program` (it owns its inputs).
    pub(crate) interner: Arc<Interner>,
    pub(crate) known: Arc<Known>,
    /// The merged Ast. A collected `Program` holds another reference;
    /// writers (`Arc::make_mut`) run when none does.
    pub(crate) ast: Arc<Ast>,
    /// The resolve of `resolve_cache` that made `ast` (`ResolvedCrate::generation`), whose final
    /// chunks are parts of it; 0 when `ast` came from elsewhere.
    pub(crate) ast_gen: u64,
    /// `None` until the first successful parse.
    pub(crate) env_hash: Option<u64>,
    /// Session-stable Adt and static numbering state, kept across
    /// requests and passed to every `collect` (see
    /// `collect::DefOrder`): a def keeps its session-local index
    /// when other defs are added or reordered, which is what lets
    /// cached outputs that carry those indices (`FnOut::types`,
    /// the glue set) survive such edits.
    pub(crate) def_order: crate::check::collect::DefOrder,
    /// The current request's client view (env, shown paths), set at the
    /// start of each compile (`compile::client_view`).
    pub(crate) client: crate::expand::ClientView,
    /// How many `def_order` entries (Adts plus statics) the disk
    /// def-order file already holds. Like the slot manifest, the
    /// order is persisted so a restarted daemon numbers defs as
    /// the previous one did; a fresh numbering would sort added
    /// defs into the middle and move the indices disk objects
    /// were built under.
    pub(crate) def_order_stored: usize,
    /// True while `def_order` came from the disk file and has not
    /// yet been checked against a parsed crate. The first slot
    /// update drops a loaded order that names none of the crate's
    /// current defs (a stale file for a different def set) and
    /// numbers fresh; see `slot_update`.
    pub(crate) def_order_loaded: bool,
    /// The Adt index of every Adt def at the last parse, by def
    /// hash. The slot update compares the next parse's predicted
    /// indices against these: cached output is reusable only when
    /// every old def is still present at the same index.
    pub(crate) prev_adt_ids: FxMap<crate::def::DefPathHash, u32>,
    /// The static index of every top-level static at the last parse.
    pub(crate) prev_static_ids: FxMap<crate::def::DefPathHash, u32>,
    /// Set by the slot update when a bodies or signatures mode edit
    /// moved Adt or static ids and it rebuilt in full instead; the
    /// shared tail reads (and clears) it as full mode.
    pub(crate) ids_forced_full: bool,
    /// The last collected program's static ids in index order
    /// (`Program::static_defs`): while a full resolve leaves them equal,
    /// nested statics kept their indexes and generic reuse holds.
    pub(crate) prev_static_defs: Option<Vec<crate::def::DefId>>,
    /// Set by a body patch whose const fn edit only const and static values
    /// can read (`ConstReach::revaluable`): the kept program must evaluate
    /// them again (`collect::const_values_hold`) before it stands.
    pub(crate) revalue_consts: bool,
    /// Set by a body patch of a fn that returns `impl Trait`: unless the
    /// kept program stands (same hidden type, `opaque::hidden_stands`),
    /// every passing body is a read-set candidate, so the users of the
    /// opaque type check again. Cleared by the request that collects.
    pub(crate) rpit_edit: bool,
    /// Set when `patch::reuse_kept` takes a program a refused patch put back
    /// (`KeptProgram::prefer`): the full collect that answered in between
    /// stored the read sets it checked against its own program, so every
    /// passing body is a read-set candidate, as for `rpit_edit`. Cleared by
    /// the next request.
    pub(crate) kept_put_back: bool,
    /// How the last builds used the kept programs (`note_kept_use`): the
    /// last one reused one, and how many builds in a row took the patch
    /// path. A front image save keeps the kept programs on these alone
    /// (`image_keeps_kept`).
    kept_reused: bool,
    patch_streak: u32,
    /// The templates whose check failed in the request that `reuse_kept`
    /// answered with their errors: `patch::keep` gives them to the kept
    /// program (`KeptProgram::recheck`).
    pub(crate) template_recheck: Vec<usize>,
    /// Collect's answer for this request, given by a refused header delta
    /// (`Caches::delta_sig_errs`, moved here by `patch::reuse_kept` when it
    /// puts the program back): compile answers it without collecting.
    pub(crate) delta_errs: Option<Vec<crate::diag::Diag>>,
    /// Set by a full resolve whose collect failed: its slot update left the
    /// per-slot caches consistent (changed bodies lost their passing mark),
    /// so the next slot update keeps them in full mode and the read-set
    /// walk checks every passing body, instead of a full rebuild. That
    /// also keeps the const fn compare and generic reuse. Cleared by the
    /// next slot update and by anything that resets the front.
    pub(crate) walk_after_reject: bool,
    /// Slots of read-set walk candidates that a failed collect left
    /// unwalked: they kept their passing mark, but their stored reads may
    /// be stale. The next request adds the ones still passing to its walk
    /// (`compile`), so they recheck when a read moved. Full mode walks
    /// every passing body anyway, so a compaction remap drops the list.
    pub(crate) walk_pending: Vec<u32>,
    /// `walk_pending` came only from failed collects whose kept program
    /// stayed with derive list edits alone (a refused derive delta, undone):
    /// the next derive delta on that program moves every key they can
    /// move, so its keyed shortcuts still hold (`compile`).
    pub(crate) pending_derive_only: bool,
    /// Set by a failed collect of a request with a const fn edit: values
    /// moved, and no body rechecked under them. The next request is a
    /// const fn edit too (`compile`).
    pub(crate) const_fn_pending: bool,
    /// The const fn bodies (`compile`'s `const_fns`) at the last build's
    /// generic reuse walk: while they differ, no derive or keyed shortcut
    /// stands in for an instance or closure body's reads.
    pub(crate) walked_const_fns: u64,
    /// Top-level items of the last parse (to see which items an edit changed).
    pub(crate) items: Vec<scan::ItemScan>,
    /// Where each LocalDefId's definition lives: item index, and index inside an impl block.
    pub(crate) fn_loc: Vec<(usize, Option<usize>)>,
    /// Each LocalDefId's slot. A slot is a function's place in the final bin's one
    /// table; cached code, objects, and the C function table all use slots. Local
    /// ids shift when functions are added, slots do not: assignment is append-only.
    pub(crate) fn_slot: Vec<u32>,
    /// Slot by stable function identity. The key is the disk pair
    /// `(StableCrateHash, DefPathHash)` (docs/ARCH.md sections 1.7 and 4.2), never
    /// a `Sym` or a local id, so the same source gets the same slots in any
    /// session, in any interning order. `driver::graph::SlotManifest` is the
    /// manifest type over this map (S7); the encode/decode pair below fixes the
    /// persisted byte shape for today's non-generic keys.
    pub(crate) slot_of: FxMap<DiskDefId, u32>,
    /// Canonical def path text per slot key, for hash collision checks
    /// (src/def.rs). A key keeps the path that first claimed it; a different
    /// path under the same key is a collision.
    pub(crate) slot_paths: FxMap<DiskDefId, Box<str>>,
    /// How many `slot_of` entries the disk slot manifest already holds
    /// (loaded at session start, then every store). The manifest is
    /// rewritten only when assignment grows past this count.
    pub(crate) slot_manifest_stored: usize,
    /// The unit byte target recorded in the disk slot manifest (loaded at
    /// session start, then every store; 0 = none recorded). A
    /// persistent session adopts it as `Caches::unit_bytes` so unit
    /// grouping, and therefore unit keys, survive a restart; a
    /// one-shot session only preserves it across its own stores.
    pub(crate) manifest_unit_bytes: u32,
    /// Body hash per slot, at the last parse. An instance slot of a
    /// generic program holds its source fingerprint at its last check
    /// (`gen_reuse::GenReuse::src_of`).
    pub(crate) slot_hash: Vec<u64>,
    /// True per slot for an instance slot of a generic program
    /// (appended after collect). The slot update leaves these alone:
    /// whether an instance is live is known only after collect, and a
    /// check request makes no generic fn instances at all. A mark
    /// lives as long as its slot number (it clears only where
    /// `slot_of` does); `Caches::ok` false marks a stale instance.
    pub(crate) inst_slot: Vec<bool>,
    /// The instance count of the last program (its fns after the AST
    /// fns): live slots for the compaction test, with the AST fns.
    pub(crate) inst_live: usize,
    /// Per instance slot, the item-level environment (`GenReuse::env`)
    /// of its last check or read replay: a slot from another one
    /// replays its stored reads before reuse.
    pub(crate) slot_env: Vec<u64>,
    /// How many AST fns the slot assignment covers: `fn_slot` holds
    /// these first, then the instance slots of a generic program.
    pub(crate) ast_fn_count: usize,
    /// Set when a slot compaction renumbered live slots this request:
    /// cached C of a generic program then cannot be reused as is.
    pub(crate) slots_renumbered: bool,
    /// Fn head hash per slot (`ast_hash::fn_head_hash`), at the last
    /// parse. A slot whose head changed always rechecks: its body is
    /// checked against that head (parameter names and patterns bind
    /// the locals), which neither the body hash nor the caller-visible
    /// `Sig` fingerprint covers.
    pub(crate) slot_head: Vec<u64>,
    /// Lexed and scanned chunks from the last request, reused when their text is unchanged.
    /// The Expr arena length right after the last fresh parse (the full
    /// parse or a resolve): `ast_bloated` in compile.rs compares against it.
    pub(crate) fresh_exprs: usize,
    pub(crate) chunks: Vec<Chunk>,
    /// The source text of the last request, to find what an edit changed.
    pub(crate) src: String,
    /// The session's source map: each file's path and line index. One crate
    /// root file per session today, always `FileId(0)`; spans in the AST name it.
    pub(crate) map: SourceMap,
    /// The chunk-boundary mask (see `split_items`). Fixed for the session, so boundaries are too.
    pub(crate) split_mask: Option<u64>,
    /// The chunk path blanked the nodes of some items it could not parse
    /// again (a parse error mid-request), so the Ast lacks live nodes for
    /// them. Bodies mode, which parses no chunk, stays off until a
    /// signatures or full parse succeeds.
    pub(crate) chunks_blanked: bool,
    /// True while this session's front state was built by the resolver
    /// (W-RESOLVE): a merged multi-file AST the chunk path must never
    /// try to reuse. Routing itself follows the current text (see
    /// `compile`): when a request no longer routes to the resolver,
    /// the state is dropped and this flag clears with it.
    pub(crate) resolved_crate: bool,
    /// The Cargo-graph crate identity for the in-flight resolver
    /// compile, handed from `resolved_setup` to the shared tail for one
    /// request (taken there, so it never outlives its request).
    pub(crate) resolved_crate_ids: Option<CrateIds>,
    /// The Cargo workspace root of a manifest build (W-PANIC): Cargo runs
    /// rustc there with relative paths, so panic locations name files
    /// relative to it (docs/ARCH.md 3.5). None for a single file.
    pub(crate) display_root: Option<std::path::PathBuf>,
    /// Per-file resolver front-end cache (raw and expanded token
    /// streams plus outlines), kept across requests in this crate
    /// session. Unused until the session first takes the resolver path.
    pub(crate) resolve_cache: crate::resolve::worklist::ResolveCache,
    /// The resolver state the body patch edits in place on the next
    /// request (driver/patch.rs). Set by a full resolve that reached
    /// the slot update; None otherwise.
    pub(crate) patch: Option<super::patch::PatchBase>,
    /// The last collected program of each mode (check, build), for a body
    /// patch to reuse in place of a fresh collect (driver/patch.rs
    /// `KeptProgram`).
    pub(crate) kept: [Option<super::patch::KeptProgram>; 2],
    /// The last successful compile's `lust-visits:` line (see
    /// `compile::Visits`), kept for tests.
    pub(crate) last_visits: String,
    /// The last successful check's answer and its request key
    /// (`compile::check_fingerprint`): a no-op check of the same
    /// request on the resolver path returns it as is.
    pub(crate) last_check: Option<(u64, crate::protocol::Response)>,
    /// The std plan the last resolver request settled on, the next
    /// request's first guess (`StdPlan`). Only a guess: the driver
    /// checks it against the files each pass sees.
    pub(crate) std_plan: Option<crate::stdload::StdPlan>,
    /// The patch oracle's state (`item_oracle.rs`; unused when it is off).
    pub(crate) oracle: std::sync::Mutex<super::item_oracle::State>,
    /// The last full resolve's module dependency record (`LUST_B3_OBSERVE=1`,
    /// resolve/mdr.rs), which the next full resolve compares with.
    pub(crate) mdr: Option<crate::resolve::mdr::Mdr>,
}

pub(crate) struct Chunk {
    /// Byte range of the chunk in the current source.
    pub(crate) start: usize,
    pub(crate) text: String,
    pub(crate) lexed: Lexed,
    /// The `start` the tokens were lexed at. Token spans are absolute, so they are only exact
    /// while this equals `start`.
    pub(crate) lexed_start: usize,
    pub(crate) scan: scan::ChunkScan,
    /// This chunk's items in `front.ast.items`, or None if it has not been parsed yet.
    pub(crate) items: Option<std::ops::Range<usize>>,
    /// This chunk's body items in `front.ast.stmt_items`, on the same
    /// lifecycle as `items`. The chunk splice rebuilds `stmt_items`
    /// from these ranges, so a re-parsed chunk's old body items are
    /// replaced, never kept next to the new ones.
    pub(crate) stmt_items: Option<std::ops::Range<usize>>,
    /// This chunk's inner attrs in `front.ast.inner_attrs`, on the
    /// same lifecycle as `items` (only the first chunk has any).
    pub(crate) inner_attrs: Option<std::ops::Range<usize>>,
    /// Outside inputs this chunk's macro expansion read (included files
    /// with content hashes, env values; see `expand::Dep`). The chunk is
    /// dropped instead of reused when one changes (added for W-MACRO).
    pub(crate) expand_deps: Vec<crate::expand::Dep>,
    /// The tokens hold an inner attribute opener (`compile::has_inner_attr`),
    /// computed once at lex time so a kept chunk is not scanned again.
    pub(crate) inner_attr: bool,
}

/// Per-slot results and build state.
pub(crate) struct Caches {
    /// The last check of this function passed.
    pub(crate) ok: Vec<bool>,
    pub(crate) out: Vec<FnOut>,
    pub(crate) has_out: Vec<bool>,
    /// The read set of the slot's last passing check (docs/ARCH.md
    /// section 8.2), stored with the result. On later edits the dirty
    /// walk (`Program::reads_dirty`) replays these reads against the
    /// new program; a body whose reads all still match is reused
    /// without a recheck. Session-local only (`Sym` and `DefId` keys are
    /// stable inside one session, never written to disk in this form).
    pub(crate) slot_reads: Vec<Option<crate::driver::graph::Reads>>,
    /// The read keys the frozen sets in `slot_reads` name (`Reads::freeze`):
    /// as long-lived as those sets.
    pub(crate) read_keys: crate::driver::graph::ReadKeys,
    /// The reads B1's unit records (`unit_records`) name, each once (`cgen::record::ReadTable`).
    pub(crate) unit_reads: crate::cgen::record::ReadTable,
    /// This request's derive delta's keyed dirty walk (driver/kept_derive.rs):
    /// by slot, whether a stored read moved. Taken by the compile tail.
    pub(crate) derive_dirty: Option<Vec<bool>>,
    /// This request's edits are all derive list edits (`Patched::derive_only`).
    pub(crate) derive_only: bool,
    /// The read keys this request's header delta can move
    /// (driver/kept_delta.rs `Touched`). Taken by the compile tail.
    pub(crate) header_moves: Option<crate::driver::kept_delta::Touched>,
    /// Set by a header delta (`kept_delta::apply_headers`): template checks
    /// that fail give their errors here, by template, instead of refusing;
    /// `reuse_kept` answers them as collect does. None outside a header delta.
    pub(crate) delta_template_errs: Option<Vec<(usize, Vec<crate::diag::Diag>)>>,
    /// Set by a header delta refused because the one edited signature's
    /// own checks fail (`kept_delta::apply`): the errors collect would answer.
    pub(crate) delta_sig_errs: Option<Vec<crate::diag::Diag>>,
    /// The derive delta's moved fn names and signature answers for this
    /// request (`kept_derive::apply_derives`), for its const body check.
    pub(crate) derive_tables: Option<crate::driver::graph::DeriveTables>,
    /// The cached IR body per slot, in the translatable form of
    /// `ir_cache::CachedBody`. Set when the slot's body is lowered;
    /// read when a slot renumber makes its C stale and the C must be
    /// re-emitted without a front-end redo.
    pub(crate) slot_ir: Vec<Option<super::ir_cache::CachedBody>>,
    pub(crate) glue: GlueSet,
    /// Fingerprint of the statics the last built glue unit was
    /// generated from (`graph::statics_fingerprint`). A build whose
    /// current statics differ must rebuild the glue unit, whatever
    /// edit mode the current request is in: a `check` request consumes
    /// the edit that moved a static's value (slot hashes advance), so
    /// the following `build` request sees no change to react to. This
    /// fingerprint is the built-state record that survives that gap.
    /// Zero means no build yet.
    pub(crate) statics_fp: u64,
    /// Fingerprint of the location tables last built into the loc
    /// unit (slot lines, slot files, file paths). A build whose
    /// tables match does not re-emit or recompile that unit. Zero
    /// means no build yet. Like `statics_fp`, it is recorded when
    /// the build that compiles the unit starts, so an edit consumed
    /// by a check request still rebuilds the unit in the next build.
    pub(crate) loc_fp: u64,
    /// B1 (`cgen::record`, LUST_B1_OBSERVE=1): what each release C fn unit was made of and
    /// read in the last build, by registration name (a glue shard by its keys' identity, the
    /// release statics pass by one name for its index and parts).
    pub(crate) unit_records: crate::intern::FxMap<String, crate::cgen::record::UnitRecord>,
    /// How many parts the statics pass of `unit_records` made: its units are the index and
    /// these (`compile::statics_unit_fp`).
    pub(crate) statics_parts: usize,
    /// `release_c::codegen_key` of the last build: a build under another key makes
    /// every slot's C again (release C and classic C share the slot cache).
    pub(crate) codegen_key: u64,
    /// The slots some fn held at the last build (`held` of the generic reuse walk):
    /// a build that lost none of them has no body whose C names a dead slot.
    pub(crate) held_slots: Vec<bool>,
    /// `graph::glue_method_slots_fp` as of the last glue build: the
    /// slots that glue calling written `fmt` and `drop` methods names.
    pub(crate) glue_slots_fp: u64,
    /// A compile since the last build saw a full-mode edit or a const
    /// fn edit, so derived glue text may be stale. Set by any compile
    /// (check requests included), cleared by the build that refreshes
    /// the glue. Same reason as `statics_fp`: the edit and the build
    /// that must react to it are usually different requests.
    pub(crate) glue_stale: bool,
    /// Slots whose generated C a compile wiped since the last build
    /// (a removed fn or a dead instance, `wipe_slot` and the slot
    /// update's dead-slot emptying). The next build reassembles their
    /// units: the old unit object still carries the dead slot's C,
    /// which can name symbols (a removed static) that no unit defines
    /// any more. Cleared by the build that reassembles them, like
    /// `glue_stale` (a check request can do the wiping).
    pub(crate) wiped_slots: Vec<u32>,
    /// Target C bytes per function unit (`cgen::group_fns_by_bytes`).
    /// 0 = not chosen yet; the first build that groups functions
    /// picks it from the total C size. A persistent session adopts
    /// the slot manifest's recorded value instead, so grouping also
    /// stays stable across restarts.
    pub(crate) unit_bytes: usize,
    /// The function groups in use (slot ranges, one per function
    /// unit). Frozen between fresh bases: a warm edit keeps every
    /// existing group's membership, and new slots group into new
    /// groups at the end, so one edit dirties only its own unit
    /// even though grouping is by bytes. A fresh base regroups all.
    pub(crate) groups: Vec<std::ops::Range<usize>>,
    /// Slot capacity of `lust_fns` in libbase.so, and how many function units it has.
    pub(crate) table_cap: usize,
    pub(crate) base_units: usize,
    /// Bumped on every base rebuild; used only for the rebuild's temp file name.
    /// Each finished base is renamed to an owner+content name (`libbase-<pid>-<hash>.so`)
    /// in `base_dir`, a persistent directory (the disk cache's `bases/`
    /// subdir), never in `obj_dir`: executables load the base by absolute
    /// rpath at run time, so it must outlive the daemon that built it,
    /// while `obj_dir` is per-daemon temp state the daemon deletes on
    /// exit. `base_files` holds the base file names this session put on
    /// disk, oldest first. Old bases are deleted only when no known
    /// output file references them any more (see `base_still_used` and
    /// the manifest sweep in compile.rs), so live binaries keep working.
    pub(crate) base_gen: u64,
    /// The current base's library name for the linker (`base-<pid>-<hash>`).
    pub(crate) base_name: String,
    /// The resolved persistent directory for base libraries. None until
    /// this session's first base build picks one (see `resolve_base_dir`).
    pub(crate) base_dir: Option<PathBuf>,
    /// True once this session swept dead entries from `base_dir`'s manifest.
    pub(crate) base_swept: bool,
    pub(crate) base_files: std::collections::VecDeque<String>,
    /// (base file name, output file) for every executable linked against a base in this session.
    pub(crate) base_users: Vec<(String, PathBuf)>,
    pub(crate) obj_dir: PathBuf,
    /// Units compiled into `obj_dir` with the current layout, and with which debug setting.
    pub(crate) objects: Option<bool>,
    /// A daemon session builds against libbase.so; a one-shot session links statically.
    pub(crate) persistent: bool,
    /// The process exits right after this session's request (`lust check` and `lust test`
    /// one-shots set it): compile leaks the program and IR instead of freeing them. A
    /// non-persistent session inside a daemon (the patch oracle's fresh compile) frees them.
    pub(crate) leak_at_exit: bool,
    /// The session is a front image's in a one-shot process (main.rs): it saves and the
    /// process exits, so the next request is a new process that may never patch (a CI
    /// build). A full resolve then leaves the patch base's span probe and const reach to
    /// the patch that needs them (`resolved_setup`; patch.rs builds both lazily).
    pub(crate) image_one_shot: bool,
    /// Generic reuse (driver/gen_reuse.rs): template check and instance
    /// discovery results of a generic program, valid while `gen_key`
    /// (the item-level environment and AST fn count they were made
    /// under) holds.
    pub(crate) gen_reuse: super::gen_reuse::GenReuse,
    /// The instance key each instance Adt id named in the C made since
    /// the last full regeneration of a generic program. C names Adts by
    /// id, so cached C is reusable only while every id names the same
    /// instance (`compile::inst_adt_ids`).
    pub(crate) inst_ids: FxMap<u32, u64>,
    /// Units whose current code is in an overlay object, not in libbase.so.
    pub(crate) overlays: std::collections::BTreeSet<usize>,
}

pub struct Session {
    /// The one crate selection this session serves. A request whose key does
    /// not match is a routing bug; compile rejects it instead of mixing state.
    pub(crate) key: SessionKey,
    pub(crate) front: Front,
    pub(crate) caches: Caches,
    /// The checked shipped std (S5), loaded at most once per session:
    /// std is immutable inside a session (docs/ARCH.md section 3.8).
    /// `None` until a request can mention a source std fn, so a session
    /// that never routes one never pays for the load.
    pub(crate) std_cache: Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    /// The disk cache (unit objects and the slot manifest), opened on the
    /// first compile. Opening hashes the tcc tree for the compiler id, so
    /// a session pays it once, not per request. `cache_tried` separates
    /// "not opened yet" from "cache is off".
    pub(crate) disk_cache: Option<crate::driver::cache::Cache>,
    pub(crate) cache_tried: bool,
}

impl Front {
    /// Notes how this build used the kept programs: its path (`patch` and
    /// `item` patch the last build's state, `resolve` and `chunks` start
    /// again) and whether `patch::reuse_kept` took one (`reuse`).
    pub(crate) fn note_kept_use(&mut self, path: &str, kept: &str) {
        self.kept_reused = kept == "reuse";
        self.patch_streak = if matches!(path, "patch" | "item") { self.patch_streak + 1 } else { 0 };
    }

    /// True when a front image save should keep the kept programs: the
    /// next build may reuse them. That is when the last build reused one,
    /// or when it and the build before it took the patch path: an edit
    /// loop without a daemon, whose next edit can reuse what this build
    /// kept. A CI merge is a full resolve, which drops the kept programs
    /// unread, or one patch between full resolves (the tsgo replay never
    /// reused one); there they are the largest churn of every image delta
    /// (253 MB raw each) and 20-25 MB of every restore.
    pub(crate) fn image_keeps_kept(&self) -> bool {
        self.kept_reused || self.patch_streak >= 2
    }
}

impl Session {
    pub fn new(obj_dir: PathBuf, persistent: bool, key: SessionKey) -> Session {
        let interner = Interner::default();
        let known = Known::new(&interner);
        Session {
            key,
            front: Front {
                interner: Arc::new(interner),
                known: Arc::new(known),
                ast: Arc::default(),
                ast_gen: 0,
                env_hash: None,
                def_order: crate::check::collect::DefOrder::default(),
                client: crate::expand::ClientView::default(),
                def_order_stored: 0,
                def_order_loaded: false,
                prev_adt_ids: FxMap::default(),
                prev_static_ids: FxMap::default(),
                ids_forced_full: false,
                prev_static_defs: None,
                revalue_consts: false,
                rpit_edit: false,
                kept_put_back: false,
                kept_reused: false,
                patch_streak: 0,
                template_recheck: Vec::new(),
                delta_errs: None,
                walk_after_reject: false,
                walk_pending: Vec::new(),
                pending_derive_only: false,
                const_fn_pending: false,
                walked_const_fns: 0,
                items: Vec::new(),
                fn_loc: Vec::new(),
                fn_slot: Vec::new(),
                slot_of: FxMap::default(),
                slot_paths: FxMap::default(),
                slot_manifest_stored: 0,
                manifest_unit_bytes: 0,
                slot_hash: Vec::new(),
                inst_slot: Vec::new(),
                inst_live: 0,
                slot_env: Vec::new(),
                ast_fn_count: 0,
                slots_renumbered: false,
                slot_head: Vec::new(),
                fresh_exprs: 0,
                chunks: Vec::new(),
                src: String::new(),
                map: SourceMap::default(),
                split_mask: None,
                chunks_blanked: false,
                resolved_crate: false,
                resolved_crate_ids: None,
                display_root: None,
                resolve_cache: crate::resolve::worklist::ResolveCache::new(!persistent),
                patch: None,
                kept: Default::default(),
                last_visits: String::new(),
                last_check: None,
                std_plan: None,
                oracle: Default::default(),
                mdr: None,
            },
            caches: Caches {
                ok: Vec::new(),
                out: Vec::new(),
                has_out: Vec::new(),
                slot_reads: Vec::new(),
                read_keys: Default::default(),
                unit_reads: Default::default(),
                derive_dirty: None,
                derive_only: false,
                header_moves: None,
                delta_template_errs: None,
                delta_sig_errs: None,
                derive_tables: None,
                slot_ir: Vec::new(),
                glue: GlueSet::default(),
                statics_fp: 0,
                loc_fp: 0,
                unit_records: Default::default(),
                statics_parts: 0,
                codegen_key: 0,
                held_slots: Vec::new(),
                glue_slots_fp: 0,
                glue_stale: false,
                wiped_slots: Vec::new(),
                unit_bytes: 0,
                groups: Vec::new(),
                table_cap: 0,
                base_units: 0,
                base_gen: 0,
                base_name: String::new(),
                base_dir: None,
                base_swept: false,
                base_files: std::collections::VecDeque::new(),
                base_users: Vec::new(),
                obj_dir,
                objects: None,
                persistent,
                leak_at_exit: false,
                image_one_shot: false,
                overlays: Default::default(),
                gen_reuse: Default::default(),
                inst_ids: FxMap::default(),
            },
            std_cache: None,
            disk_cache: None,
            cache_tried: false,
        }
    }
    pub fn obj_dir(&self) -> &Path {
        &self.caches.obj_dir
    }

    /// Before a front image save (src/image.rs): joins the session's side
    /// threads, so the image holds no handle of a thread that ends with
    /// this process.
    pub fn settle(&mut self) {
        if let Some(p) = self.front.patch.as_mut() {
            p.settle();
        }
    }

    /// After a front image load: process-owned handles are this process's
    /// to open again (the disk cache, opened on the next compile).
    pub fn after_restore(&mut self) {
        self.disk_cache = None;
        self.cache_tried = false;
    }

    /// The persistent base library directory, once a base was built.
    pub fn base_dir(&self) -> Option<&Path> {
        self.caches.base_dir.as_deref()
    }

    /// Both crate identities for stable defs: the session-local id (one crate
    /// per session today) and the stable hash over the key's package and
    /// target identity (docs/ARCH.md section 1.7 steps 1 and 2). Features and
    /// the target triple select the session; they are not part of def
    /// identity, matching section 1.8's split of SessionKey from the crate
    /// disambiguator.
    pub(crate) fn crate_ids(&self) -> CrateIds {
        let k = &self.key.krate;
        CrateIds { local: LOCAL_CRATE, stable: stable_crate_hash(&k.package_id, &k.target_kind, &k.target_name, k.test) }
    }
}

/// The slot manifest byte shape: magic, entry count, then one 20-byte
/// entry per slot (`DiskDefId` bytes + slot), sorted by slot, then the
/// unit byte target (`Caches::unit_bytes`) the stored objects were grouped with
/// as a trailing u32 (0 = not recorded; files without the trailer,
/// written before it existed, still decode with 0). Only stable disk
/// pairs are stored, so a restarted daemon that loads these bytes recovers the
/// same slot assignment in any crate load or discovery order (docs/ARCH.md
/// sections 4.2 and 8.4). The byte target rides along because unit keys
/// depend on the grouping: a restarted daemon that regrouped with a
/// different target would orphan every stored object. The in-memory manifest type is
/// `driver::graph::SlotManifest`; the bytes live in the disk cache
/// (`driver::cache::Cache::load_slot_manifest`). `LSS1` files recorded
/// a slot count per unit from the count-based grouping; they read as
/// a miss under the new magic, so slots number fresh once.
const SLOT_MANIFEST_MAGIC: &[u8; 4] = b"LSS2";

/// Serializes a slot map and its unit byte target. See `SLOT_MANIFEST_MAGIC`.
pub(crate) fn encode_slot_manifest(slot_of: &FxMap<DiskDefId, u32>, unit_bytes: u32) -> Vec<u8> {
    let mut entries: Vec<(u32, DiskDefId)> = slot_of.iter().map(|(k, &s)| (s, *k)).collect();
    entries.sort_unstable();
    let mut out = Vec::with_capacity(12 + entries.len() * 20);
    out.extend_from_slice(SLOT_MANIFEST_MAGIC);
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (slot, key) in entries {
        out.extend_from_slice(&key.to_bytes());
        out.extend_from_slice(&slot.to_le_bytes());
    }
    out.extend_from_slice(&unit_bytes.to_le_bytes());
    out
}

/// The def-order file byte shape: magic, the stable crate hash the
/// hashes were numbered under, Adt count, static count, instance base,
/// instance count (4 bytes each), then each def hash in order (Adts
/// first) and each instance key in order (`collect::InstOrder`), 8
/// bytes each. Only stable hashes are stored (def hashes mix in the
/// stable crate hash; instance keys hash def disk ids and args), so a
/// restarted daemon recovers the same Adt, static, and instance Adt
/// numbering (see `collect::DefOrder`). The stored crate hash lets a
/// reader reject a file written for a different crate identity instead
/// of numbering this crate's defs by a foreign order. `LSDO` files
/// (no instances) read as a miss.
const DEF_ORDER_MAGIC: &[u8; 4] = b"LSD2";

/// Serializes a def order. See `DEF_ORDER_MAGIC`.
pub(crate) fn encode_def_order(order: &crate::check::collect::DefOrder, stable: crate::def::StableCrateHash) -> Vec<u8> {
    let inst = &order.instances;
    let mut out = Vec::with_capacity(28 + (order.adts.len() + order.statics.len() + inst.keys.len()) * 8);
    out.extend_from_slice(DEF_ORDER_MAGIC);
    out.extend_from_slice(&stable.0.to_le_bytes());
    for n in [order.adts.len(), order.statics.len(), inst.base as usize, inst.keys.len()] {
        out.extend_from_slice(&(n as u32).to_le_bytes());
    }
    for h in order.adts.iter().chain(&order.statics) {
        out.extend_from_slice(&h.0.to_le_bytes());
    }
    for k in &inst.keys {
        out.extend_from_slice(&k.to_le_bytes());
    }
    out
}

/// Reads bytes written by `encode_def_order`. None on any shape
/// error, on a stable crate hash other than `stable`, or on a hash
/// listed twice (in one list, or as both an Adt and a static), so
/// a bad or stale file is a cache miss and the caller numbers defs
/// fresh, never by a wrong order.
pub(crate) fn decode_def_order(b: &[u8], stable: crate::def::StableCrateHash) -> Option<crate::check::collect::DefOrder> {
    if b.get(..4)? != DEF_ORDER_MAGIC {
        return None;
    }
    if u64::from_le_bytes(b.get(4..12)?.try_into().ok()?) != stable.0 {
        return None;
    }
    let word = |at: usize| -> Option<usize> { Some(u32::from_le_bytes(b.get(at..at + 4)?.try_into().ok()?) as usize) };
    let (na, ns, base, ni) = (word(12)?, word(16)?, word(20)?, word(24)?);
    let n = na.checked_add(ns)?;
    if b.len() != n.checked_add(ni)?.checked_mul(8)?.checked_add(28)? {
        return None;
    }
    let mut order = crate::check::collect::DefOrder::default();
    for i in 0..n {
        let at = 28 + i * 8;
        let h = crate::def::DefPathHash(u64::from_le_bytes(b[at..at + 8].try_into().ok()?));
        if order.adts.contains(&h) || order.statics.contains(&h) {
            return None;
        }
        if i < na { &mut order.adts } else { &mut order.statics }.push(h);
    }
    order.instances.base = base as u32;
    for i in 0..ni {
        let at = 28 + (n + i) * 8;
        let k = u64::from_le_bytes(b[at..at + 8].try_into().ok()?);
        if order.instances.place.contains_key(&k) {
            return None;
        }
        order.instances.place_of(k);
    }
    Some(order)
}

/// Reads bytes written by `encode_slot_manifest`: the slot map and
/// the stored unit size (0 when the file predates the trailer).
/// None on any shape error (bad magic, a truncated or trailing
/// byte, one slot claimed twice, or an implausible unit size), so
/// a bad file is a cache miss, never a wrong slot.
pub(crate) fn decode_slot_manifest(b: &[u8]) -> Option<(FxMap<DiskDefId, u32>, u32)> {
    if b.get(..4)? != SLOT_MANIFEST_MAGIC {
        return None;
    }
    let n = u32::from_le_bytes(b.get(4..8)?.try_into().ok()?) as usize;
    let body = n.checked_mul(20)?.checked_add(8)?;
    let unit_bytes = if b.len() == body {
        0
    } else if b.len() == body.checked_add(4)? {
        let ub = u32::from_le_bytes(b[body..body + 4].try_into().ok()?);
        if ub > 64 * 1024 * 1024 {
            return None;
        }
        ub
    } else {
        return None;
    };
    let mut map = FxMap::default();
    let mut slots: Vec<u32> = Vec::with_capacity(n);
    for i in 0..n {
        let at = 8 + i * 20;
        let key = DiskDefId::from_bytes(&b[at..at + 16])?;
        let slot = u32::from_le_bytes(b[at + 16..at + 20].try_into().ok()?);
        if slots.contains(&slot) || map.insert(key, slot).is_some() {
            return None;
        }
        slots.push(slot);
    }
    Some((map, unit_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, StableCrateHash};

    fn key(krate: u64, hash: u64) -> DiskDefId {
        DiskDefId { krate: StableCrateHash(krate), hash: DefPathHash(hash) }
    }

    /// The session key's stable crate hash matches the pre-S6 synthetic hash
    /// byte for byte (same package string, `bin` target, stem name, test
    /// flag), so slot identities for single-file programs do not move.
    /// Features select a session without changing def identity (section 1.8).
    #[test]
    fn session_key_keeps_the_synthetic_crate_hash() {
        let dir = PathBuf::from("/tmp/lust-session-test");
        for test in [false, true] {
            let key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), test);
            let s = Session::new(dir.clone(), false, key.clone());
            assert_eq!(s.crate_ids().stable, crate::def::synthetic_crate_hash("/tmp/x/main.rs", test));
            assert_eq!(s.key, key);
        }
        let mut key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false);
        key.features = vec!["alpha".into()];
        let s = Session::new(dir, false, key);
        assert_eq!(s.crate_ids().stable, crate::def::synthetic_crate_hash("/tmp/x/main.rs", false), "features do not rename defs");
    }

    /// An image keeps the kept programs after a build that reused one, and
    /// after two patch-path builds in a row (the second edit of a loop
    /// without a daemon); it drops them after a full resolve, and after a
    /// single patch between full resolves (a CI merge).
    #[test]
    fn image_keeps_kept_programs_only_for_a_next_reuse() {
        let key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false);
        let mut s = Session::new(PathBuf::from("/tmp/lust-session-test"), true, key);
        let f = &mut s.front;
        assert!(!f.image_keeps_kept(), "a new session has no use for them");
        f.note_kept_use("resolve", "none");
        assert!(!f.image_keeps_kept(), "a full resolve drops them unread");
        f.note_kept_use("patch", "none");
        assert!(!f.image_keeps_kept(), "one patch between full resolves");
        f.note_kept_use("item", "discovery");
        assert!(f.image_keeps_kept(), "a second patch in a row: an edit loop");
        f.note_kept_use("patch", "reuse");
        assert!(f.image_keeps_kept(), "the last build reused one");
        f.note_kept_use("resolve", "none");
        assert!(!f.image_keeps_kept(), "a full resolve ends the loop");
        f.note_kept_use("patch", "reuse");
        assert!(f.image_keeps_kept(), "a reuse keeps them at once");
    }

    /// Serialize, then read back in a fresh map (a restarted daemon): every
    /// function keeps its slot, dead slots included, whatever order the map
    /// held its entries in.
    #[test]
    fn slot_manifest_round_trips() {
        let mut m = FxMap::default();
        m.insert(key(1, 10), 0);
        m.insert(key(1, 20), 1);
        m.insert(key(1, 30), 5);
        m.insert(key(2, 10), 3);
        let back = decode_slot_manifest(&encode_slot_manifest(&m, 131_072)).unwrap();
        assert_eq!(back, (m.clone(), 131_072), "slots and unit byte target round-trip");
        // A pre-trailer file (no unit byte target recorded) still decodes.
        let mut old = encode_slot_manifest(&m, 131_072);
        old.truncate(old.len() - 4);
        assert_eq!(decode_slot_manifest(&old), Some((m, 0)), "old shape keeps its slots");
        let empty: FxMap<DiskDefId, u32> = FxMap::default();
        assert_eq!(decode_slot_manifest(&encode_slot_manifest(&empty, 0)), Some((empty, 0)));
    }

    /// The def order round-trips (a restarted daemon numbers defs
    /// as the previous one did), and bad bytes decode to None, so
    /// the caller falls back to a fresh numbering.
    #[test]
    fn def_order_round_trips_and_rejects_bad_bytes() {
        let stable = StableCrateHash(42);
        let mut order = crate::check::collect::DefOrder::default();
        order.adts = vec![DefPathHash(30), DefPathHash(10), DefPathHash(20)];
        order.statics = vec![DefPathHash(7), DefPathHash(9)];
        order.instances.base = 40;
        for k in [77, 55, 66] {
            order.instances.place_of(k);
        }
        let bytes = encode_def_order(&order, stable);
        let back = decode_def_order(&bytes, stable).unwrap();
        assert_eq!(back.adts, order.adts);
        assert_eq!(back.statics, order.statics);
        assert_eq!((back.instances.base, &back.instances.keys), (40, &vec![77, 55, 66]));
        assert_eq!(back.instances.place.get(&55), Some(&1));
        // Every prefix and a trailing byte are shape errors.
        for cut in 0..bytes.len() {
            assert!(decode_def_order(&bytes[..cut], stable).is_none(), "prefix {cut}");
        }
        let mut tail = bytes.clone();
        tail.push(0);
        assert!(decode_def_order(&tail, stable).is_none(), "trailing byte");
        // A file for a different crate identity is not trusted.
        assert!(decode_def_order(&bytes, StableCrateHash(43)).is_none(), "other crate");
        let mut wrong = bytes.clone();
        wrong[0] = b'X';
        assert!(decode_def_order(&wrong, stable).is_none(), "magic");
        // A hash listed twice is bad, in one list or across both, and
        // so is an instance key listed twice.
        let mut dup = encode_def_order(&order, stable);
        dup[28..36].copy_from_slice(&20u64.to_le_bytes());
        assert!(decode_def_order(&dup, stable).is_none(), "duplicate hash");
        let mut dup_inst = encode_def_order(&order, stable);
        let last = dup_inst.len() - 8;
        dup_inst[last..].copy_from_slice(&77u64.to_le_bytes());
        assert!(decode_def_order(&dup_inst, stable).is_none(), "duplicate instance key");
        order.statics = vec![DefPathHash(30)];
        assert!(decode_def_order(&encode_def_order(&order, stable), stable).is_none(), "hash in both lists");
    }

    /// A bad manifest never decodes to wrong slots.
    #[test]
    fn slot_manifest_rejects_bad_bytes() {
        let mut m = FxMap::default();
        m.insert(key(1, 10), 0);
        let bytes = encode_slot_manifest(&m, 16);
        assert_eq!(decode_slot_manifest(&bytes[..bytes.len() - 1]), None, "truncated");
        let mut tail = bytes.clone();
        tail.push(0);
        assert_eq!(decode_slot_manifest(&tail), None, "trailing byte");
        let mut wrong = bytes;
        wrong[0] = b'X';
        assert_eq!(decode_slot_manifest(&wrong), None, "magic");
    }
}
