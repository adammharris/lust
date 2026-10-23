// The compile pipeline, cold or incremental. State that an edit can reuse lives in
// `Session` (session.rs).
//
// Incremental rules, from cheapest to most expensive:
//   1. Only function bodies changed (same environment hash: all tokens outside bodies): re-parse,
//      re-check, and re-generate only those functions. One exception: a changed const fn body can
//      move const and static values, array lengths, and discriminants that unchanged bodies baked
//      in, so then every unchanged passing body joins the read-set dirty walk (rule 2's mechanism)
//      and the glue unit (which holds the statics) rebuilds.
//   2. Only top-level functions were added, removed, or changed signature (all other items the
//      same): re-parse the file, but re-check and re-generate only the changed functions and the
//      bodies that mention their names. A changed function always rechecks: its body is checked
//      against its own signature, which the body hash does not cover. A mention-only candidate
//      (own signature unchanged, body unchanged) whose recorded reads all still match the new
//      program (`Program::reads_dirty`, the section 8.3 step 5 dirty walk) is reused without a
//      recheck: per-name binding reads, method-set probes, and failed lookups are precise where
//      name mentions are not. Candidates with no stored reads always recheck.
//   3. Anything else (a type, an impl, a use changed), and any edit to a single file whose last
//      parse had items inside fn bodies: full mode. Every unchanged passing body
//      is a dirty-walk candidate; only bodies whose recorded reads changed recheck. The caches
//      clear instead when reuse is not provable (first compile, Adt sequence change, or slot
//      compaction; see `slot_update`).
use super::session::{Caches, Chunk, Front, Session};
use super::patch::fn_def_at_mut;
use super::span_shift;
use super::{Cmd, Request, Response};
use crate::ast::{Ast, ItemKind};
use crate::cgen::{self, FnOut, GlueSet};
use crate::check::collect::{self, LocalDefId};
use crate::def::{self, CrateIds, DiskDefId, StableCrateHash};
use crate::diag::{self, Diag, FileId, LineIndex, SourceMap};
use crate::expand;
use crate::intern::{FxMap, Interner, Sym};
use crate::lexer;
use crate::stdload::StdPlan;
use crate::scan;
use crate::{borrowck, check, ir, lower, parser};
use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// The session's one source file in its source map. A crate is one file today, so every
/// span the lexer makes in this pipeline names it (docs/ARCH.md section 9.2, S1).
const ROOT_FILE: FileId = FileId(0);

/// Runs macro expansion over one lexed chunk or file (for W-RESOLVE: this
/// is the spot that moves into the 6.1 outline worklist). Expansion is a
/// no-op for files with no macro definitions or non-parser macro calls,
/// so macro-free files keep the current path bit for bit.
fn expand_tokens(
    front: &Front,
    lexed: lexer::Lexed,
    file: &std::path::Path,
    src: &str,
    test: bool,
    profile: crate::protocol::ProfileFlags,
    session: &crate::protocol::SessionKey,
) -> Result<(lexer::Lexed, Vec<expand::Dep>), Diag> {
    let mut ctx = expand::ExpandCtx::for_file(&front.interner, &front.known, file, src, test);
    ctx.client = &front.client;
    // The root file sees the session target's cfg facts, as every other
    // file of a crate session does through the worklist: a foreign
    // `--target` must change `cfg!` and `#[cfg]` here too, not leave
    // the host facts of `for_file` in place.
    let env = crate::resolve::cfg::CfgEnv::new(&session.target_triple, &session.features, test, profile);
    ctx.cfg = crate::resolve::worklist::expand_cfg(&env);
    ctx.cfg.panic_unwind = !profile.panic_abort;
    ctx.cfg.debug_assertions = profile.debug_assertions;
    expand::expand_lexed_with_deps(lexed, &ctx)
}

/// True when `f` exists only after monomorphization: a generic fn
/// instance, or a closure body inside one.
fn post_mono(p: &collect::Program, f: LocalDefId) -> bool {
    use crate::check::generics::FnClass;
    let mut f = f;
    // Closure parents were made earlier, so the chain ends; the bound only guards it.
    for _ in 0..64 {
        match p.gx.fn_class.get(f.0 as usize) {
            Some(FnClass::Instance) => return true,
            Some(FnClass::Closure) => match p.gx.closure_fns.get(&f).and_then(|c| p.gx.closures.get(c)) {
                Some(c) => f = c.parent,
                None => return false,
            },
            _ => return false,
        }
    }
    false
}

/// The expansion view of `req`'s client (see `protocol::Client`): its env,
/// and paths shown relative to the root file as the user typed it. A
/// manifest-selected crate shows paths relative to the workspace root
/// instead, set once the graph is loaded (`resolved_setup`).
/// Fills build script outputs into path dependency units, recursively:
/// `OUT_DIR` and `rustc-env` pairs join the unit's Cargo env, and the
/// `rustc-cfg` values ride along for the resolver's per-crate cfg env.
/// Only path packages compile from source here; adapter and shim
/// units keep no Cargo env (their root is a lust-owned crate).
fn fill_dep_build_outputs(
    deps: &mut [crate::resolve::cargo::DepUnit],
    cache: &Path,
    env: super::buildscript::ClientEnv,
    memo: &mut FxMap<PathBuf, Option<super::buildscript::Outputs>>,
) -> Result<(), String> {
    for dep in deps {
        if dep.source.is_none() {
            let out = match memo.get(&dep.manifest_dir) {
                Some(o) => o.clone(),
                None => {
                    let o = super::buildscript::outputs(&dep.manifest_dir, cache, env)
                        .map_err(|e| format!("build script of `{}` failed: {e}", dep.package_name))?;
                    memo.insert(dep.manifest_dir.clone(), o.clone());
                    o
                }
            };
            if let Some(out) = out {
                if let Some(dir) = &out.out_dir {
                    dep.cargo_env.push(("OUT_DIR".into(), dir.to_string_lossy().into_owned()));
                }
                dep.cargo_env.extend(out.rustc_env);
                dep.build_cfgs = out.rustc_cfg;
                dep.build_check_cfgs = out.rustc_check_cfg;
            }
        }
        fill_dep_build_outputs(&mut dep.deps, cache, env, memo)?;
    }
    Ok(())
}

fn client_view(req: &Request) -> expand::ClientView {
    let shown_root = match (&req.client.shown, &req.session.krate.manifest_path) {
        (Some(typed), None) => req.file.parent().zip(typed.parent()).map(|(abs, shown)| (abs.to_path_buf(), shown.to_path_buf())),
        _ => None,
    };
    expand::ClientView { env: req.client.env.clone().map(std::sync::Arc::new), shown_root }
}

/// Wall time per stage.
struct Timer {
    stages: Vec<(&'static str, f64)>,
    last: Instant,
    start: Instant,
}

impl Timer {
    fn new() -> Timer {
        let now = Instant::now();
        Timer { stages: Vec::new(), last: now, start: now }
    }
    fn lap(&mut self, name: &'static str) {
        let now = Instant::now();
        self.stages.push((name, (now - self.last).as_secs_f64() * 1e3));
        self.last = now;
    }
    /// Records sub-stage times measured inside a stage that just
    /// finished (the worklist phases), in place of one `lap` for the
    /// whole stage, plus the time they leave out as `rest`.
    fn lap_parts(&mut self, parts: Vec<(&'static str, f64)>, rest: &'static str) {
        let now = Instant::now();
        let covered: f64 = parts.iter().map(|p| p.1).sum();
        self.stages.extend(parts);
        self.stages.push((rest, ((now - self.last).as_secs_f64() * 1e3 - covered).max(0.0)));
        self.last = now;
    }
    /// Records sub-stage times of a stage that already has its own lap
    /// (`laps.rs`: collect's phases), shown after it, nested by name.
    fn note_parts(&mut self, parts: Vec<(&'static str, f64)>) {
        self.stages.extend(parts);
    }
    fn render(&self, out: &mut String) {
        for (name, ms) in &self.stages {
            let _ = writeln!(out, "  {name:<24} {ms:>9.2} ms");
        }
        let _ = writeln!(out, "  {:<24} {:>9.2} ms", "total", self.start.elapsed().as_secs_f64() * 1e3);
    }
}

/// The release driver's cc step, parked by `compile` for an image run (`main::image_run`
/// turns `defer_cc` on for its last release build when the image saves in the background).
/// The run forks the image save first and then runs this step, so the image is written while
/// clang runs: after a merge, a new base took 11-21 s inside a CI job, after the artifact.
pub struct DeferredCc {
    job: Box<dyn FnOnce() -> Result<String, String>>,
    t: Timer,
    /// The build's summary line up to the cc summary.
    head: String,
    timings: bool,
}

enum Parked {
    Job(DeferredCc),
    /// The step ran: its exit code and the lines the build prints after it.
    Done(i32, String),
}

thread_local! {
    static DEFER_CC: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static PARKED: std::cell::RefCell<Option<Parked>> = const { std::cell::RefCell::new(None) };
}

/// Turns on or off the parking of the next release build's cc step (`DeferredCc`).
pub fn defer_cc(on: bool) {
    DEFER_CC.with(|d| d.set(on));
}

/// Runs a parked cc step now: an image save that cannot fork writes after it.
pub fn finish_parked_cc() {
    PARKED.with(|p| {
        let mut p = p.borrow_mut();
        if let Some(Parked::Job(job)) = p.take() {
            let DeferredCc { job, mut t, head, timings } = job;
            *p = Some(match job() {
                Ok(summary) => {
                    t.lap("cc compile + link");
                    let mut out = String::new();
                    if timings {
                        let _ = writeln!(out, "{head}{summary})");
                        t.render(&mut out);
                    }
                    Parked::Done(0, out)
                }
                Err(e) => Parked::Done(3, format!("error: {e}\n")),
            });
        }
    });
}

/// Drops a parked cc step: the image save's forked child, so the step's unit texts are
/// not live blocks of the image it writes.
pub fn drop_parked_cc() {
    PARKED.with(|p| drop(p.borrow_mut().take()));
}

/// The parked cc step's exit code and output, running it first if it has not run.
pub fn parked_cc_result() -> Option<(i32, String)> {
    finish_parked_cc();
    PARKED.with(|p| match p.borrow_mut().take() {
        Some(Parked::Done(code, out)) => Some((code, out)),
        _ => None,
    })
}

/// True when `LUST_STATS` is set to a value other than "" or "0". Stats go
/// to stderr as one `lust-stats:` line per compile; the scale gate
/// (scripts/scale-gate.py) parses them. Off by default: user output does
/// not change.
fn stats_on() -> bool {
    matches!(std::env::var("LUST_STATS"), Ok(v) if !v.is_empty() && v != "0")
}

/// One compile's scale-gate counters (docs/ARCH.md section 9.3 scale
/// gate), rendered as a single line. `c_bytes` counts C text emitted
/// this compile (units actually generated), `dirty_units` the fn units
/// whose objects were (re)compiled or served as overlays, and
/// `unit_cache_hits` the units whose object came from the disk unit
/// cache instead of tcc. Instance count is the live slot count: today
/// one instance per fn (mono instances join with generics). For a
/// generic program, `templates` counts the template checks collect
/// ran and `discovered` the bodies its instance discovery checked;
/// both are front-end work `rechecked` does not count.
#[derive(Default)]
struct Stats {
    mode: &'static str,
    fns: usize,
    rechecked: usize,
    reused: usize,
    invalidated: usize,
    c_bytes: usize,
    dirty_units: usize,
    units_compiled: usize,
    unit_cache_hits: usize,
    table_rebuilt: bool,
    instances: usize,
    reemitted: usize,
    templates: usize,
    discovered: usize,
}

impl Stats {
    fn render(&self, out: &mut String) {
        let _ = writeln!(
            out,
            "lust-stats: mode={} fns={} rechecked={} reused={} invalidated={} c_bytes={} dirty_units={} units_compiled={} unit_cache_hits={} table_rebuilt={} instances={} reemitted={} templates={} discovered={}",
            self.mode,
            self.fns,
            self.rechecked,
            self.reused,
            self.invalidated,
            self.c_bytes,
            self.dirty_units,
            self.units_compiled,
            self.unit_cache_hits,
            self.table_rebuilt as u8,
            self.instances,
            self.reemitted,
            self.templates,
            self.discovered,
        );
    }
}

/// What each front-end phase of one compile walked (W-INCR2), rendered
/// under `LUST_STATS` as one `lust-visits:` line after `lust-stats:`.
/// `Stats` counts checks; this counts the nodes and items each phase
/// touched, so a warm edit that costs work in proportion to the crate
/// shows here even when it rechecks one body. `path` is the front end:
/// `patch` (driver/patch.rs), `resolve` (a full resolve), or `chunks`
/// (the single-file path). `files`: files the front end lexed or
/// parsed again. `nodes`: Ast nodes it built or copied (expressions,
/// patterns, types, blocks). `spans`: spans the patch moved.
/// `scanned`: items rescanned structurally. `slot_fns`: fns the slot
/// update compared. `collect`: items and fns collect walked.
/// `discovery`: bodies instance discovery checked or replayed.
/// `checked`: bodies checked. `reads`: unchanged files the body patch
/// read from disk because it could not trust their stat. `why`: on a full resolve, the condition
/// that stopped the body patch (`no_base` on a first compile). `kept`:
/// `reuse` when a kept program stood in for collect (W-INCR3), else
/// why not; `prog_spans`: its spans moved. Error answers record the
/// line too (`Front::last_visits`, `LUST_VISITS_LOG`), never on stderr.
#[derive(Default)]
struct Visits {
    path: &'static str,
    /// Why a resolver-path request did not patch (`patch::try_patch`),
    /// or the chunk path's rule (`bodies`, `signatures`, `full`).
    why: &'static str,
    /// `reuse` when the kept program stood in for collect, else why not
    /// (`patch::reuse_kept`); `prog_spans` counts its spans moved.
    kept: &'static str,
    prog_spans: usize,
    files: usize,
    nodes: usize,
    spans: usize,
    scanned: usize,
    slot_fns: usize,
    collect: usize,
    discovery: usize,
    checked: usize,
    reads: usize,
    /// Slots the keyed walk after a header delta answered (`keyed_dirty`).
    keyed: usize,
    /// Generic reuse for this request: `on`, else why it was off (a
    /// generic program then rechecks and regenerates every concrete body).
    generic: &'static str,
    /// When collect started from the last program's type store (B1-PLAN.md):
    /// the types this collect interned, and all the store holds.
    pool: Option<(usize, usize)>,
}

impl Visits {
    fn render(&self, out: &mut String) {
        let _ = writeln!(
            out,
            "lust-visits: path={} why={} files={} nodes={} spans={} scanned={} slot_fns={} collect={} discovery={} checked={} kept={} prog_spans={} reads={} keyed={} generic={} pool={}",
            self.path,
            if self.why.is_empty() { "-".to_string() } else { self.why.replace(' ', "_") },
            self.files,
            self.nodes,
            self.spans,
            self.scanned,
            self.slot_fns,
            self.collect,
            self.discovery,
            self.checked,
            if self.kept.is_empty() { "-".to_string() } else { self.kept.replace(' ', "_") },
            self.prog_spans,
            self.reads,
            self.keyed,
            if self.generic.is_empty() { "-" } else { self.generic },
            self.pool.map_or_else(|| "-".to_string(), |(m, t)| format!("{m}/{t}"))
        );
    }
}

/// Appends one `lust-visits:` line to the file `LUST_VISITS_LOG` names,
/// when set: how a test or fuzz run measures which warm requests took
/// the body patch without changing any compile's output.
fn log_visits(line: &str) {
    if let Some(path) = std::env::var_os("LUST_VISITS_LOG") {
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = f.write_all(line.as_bytes());
        }
    }
}

/// The key under which a successful check's answer may be reused by
/// the next request when no source changed: every request field that
/// can change the answer (timings and stats only add lines, which a
/// reused answer makes fresh). None for requests that must run:
/// anything but a check, and a check that asks for C output.
fn check_fingerprint(req: &Request) -> Option<u64> {
    if req.cmd != Cmd::Check || req.emit_c.is_some() {
        return None;
    }
    let key =
        format!("{:?}", (&req.session, &req.file, &req.out, req.json, req.debug, req.max_errors, &req.run_args, req.harness, &req.client));
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&key, &mut h);
    Some(std::hash::Hasher::finish(&h))
}

/// Arena nodes of one Ast (expressions, patterns, types, blocks).
pub(super) fn ast_nodes(ast: &Ast) -> usize {
    ast.exprs.len() + ast.pats.len() + ast.tys.len() + ast.blocks.len()
}

/// The generic front-end work collect did for one program, for the
/// stats line: (template checks run, discovery checks run). Generic
/// reuse (driver/gen_reuse.rs) skips the bodies whose stored results
/// held; a program with no generics runs neither.
fn generic_work(reuse: &super::gen_reuse::GenReuse) -> (usize, usize) {
    (reuse.templates_checked, reuse.discovery_checked)
}

/// Folds each fn's own source text, from the start of its first line
/// to the end of its body, into its scan body hash. The token hash
/// misses whitespace and comment edits that move a panic site's line or
/// column inside the body, and a reused body's C embeds those positions
/// (relative to its first line). `src` is the text the tokens index.
fn fold_fn_text(sc: &mut scan::ChunkScan, lexed: &lexer::Lexed, src: &str) {
    for f in &mut sc.fns {
        let Some(last) = f.body.end.checked_sub(1).and_then(|k| lexed.tokens.get(k)) else { continue };
        let (lo, hi) = (f.fn_offset as usize, last.span.hi as usize);
        if lo > hi || hi > src.len() || !src.is_char_boundary(lo) || !src.is_char_boundary(hi) {
            continue;
        }
        let start = src[..lo].rfind('\n').map_or(0, |i| i + 1);
        let mut h = crate::intern::FxHasher::default();
        std::hash::Hash::hash(&f.body_hash, &mut h);
        std::hash::Hash::hash(&src.as_bytes()[start..hi], &mut h);
        f.body_hash = std::hash::Hasher::finish(&h);
    }
}

/// True when the chunk path's bodies mode can take a request exactly.
/// The request's one edit (old bytes `edit.0..edit.1`, now `delta` bytes
/// longer) moves every span edge at or after `edit.1` and no edge before
/// it, so a kept node with an edge inside the window would land wrong: an
/// edit must sit strictly inside one changed fn's body. That holds for a
/// window with `delta` 0 too: two edits in two fns whose lengths cancel
/// move every item between them (realish seed 112: a later body blank
/// then wiped a method signature there). Only a request with no text
/// change (failed fns checked again) needs no window. And each
/// changed fn must have no node between its parameters and its body
/// (parameter patterns, expressions in parameter or return types):
/// `FnDef::exprs` and `pats` start there in a cold parse, and the new
/// body's ranges would drop them (closure numbering reads the ranges).
/// The body patch (driver/patch.rs) applies the same two rules.
fn bodies_mode_ok(ast: &Ast, fn_loc: &[(usize, Option<usize>)], changed: &[usize], edit: (usize, usize), delta: i64) -> bool {
    let body_span = |i: usize| {
        let (item, sub) = fn_loc[i];
        fn_def_at(ast, item, sub).body.map(|b| ast.block(b).span)
    };
    let inside = |sp: diag::Span| sp.file == ROOT_FILE && (sp.lo as usize) < edit.0 && edit.1 < sp.hi as usize;
    let text_changed = delta != 0 || edit.0 < edit.1;
    if text_changed && !changed.iter().any(|&i| body_span(i).is_some_and(inside)) {
        return false;
    }
    changed.iter().all(|&i| {
        let (item, sub) = fn_loc[i];
        let def = fn_def_at(ast, item, sub);
        let Some(body) = body_span(i) else { return false };
        let starts_in_body = |(first, end): (u32, u32), spans: &[diag::Span]| {
            first == end || spans.get(first as usize).is_some_and(|s| s.file == body.file && body.lo <= s.lo && s.hi <= body.hi)
        };
        def.params.iter().all(|p| p.pat.is_none()) && starts_in_body(def.exprs, &ast.expr_spans) && starts_in_body(def.pats, &ast.pat_spans)
    })
}

/// The fn at one `fn_locations` entry.
pub(super) fn fn_def_at(ast: &Ast, item: usize, sub: Option<usize>) -> &crate::ast::FnDef {
    match (item != usize::MAX, sub) {
        (false, Some(k)) => match &ast.stmt_items[k].kind {
            ItemKind::Fn(d) => d,
            _ => unreachable!("fn_loc out of date"),
        },
        _ => match (&ast.items[item].kind, sub) {
            (ItemKind::Fn(d), None) => d,
            (ItemKind::Impl(imp), Some(k)) => &imp.fns[k],
            _ => unreachable!("fn_loc out of date"),
        },
    }
}

/// The local `DefId`s of AST fns (`Front::fn_loc` indexes), from their
/// slots' disk identities.
fn local_def_ids(front: &Front, fns: &[usize]) -> Vec<def::DefId> {
    let slots: Vec<u32> = fns.iter().filter_map(|&i| front.fn_slot.get(i).copied()).collect();
    front.slot_of.iter().filter(|(_, s)| slots.contains(s)).map(|(d, _)| def::DefId { krate: def::LOCAL_CRATE, hash: d.hash }).collect()
}

/// `fold_fn_text` for a resolver-path fn: `hash` folded with the fn's
/// text from the start of its name's line to the end of its body, and
/// with the distance from its base line (`line`, the line of its `fn`
/// keyword) to its name's line. A fn with no body or no kept file text
/// keeps `hash` as is.
pub(super) fn fn_text_hash(ast: &Ast, map: &SourceMap, def: &crate::ast::FnDef, line: u32, hash: u64) -> u64 {
    let Some(body) = def.body else { return hash };
    let (head, end) = (def.name_span, ast.blocks[body.0 as usize].span);
    let Some(text) = map.text(head.file) else { return hash };
    let (lo, hi) = (head.lo as usize, end.hi as usize);
    if end.file != head.file || lo > hi || hi > text.len() || !text.is_char_boundary(lo) || !text.is_char_boundary(hi) {
        return hash;
    }
    let start = text[..lo].rfind('\n').map_or(0, |i| i + 1);
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&hash, &mut h);
    std::hash::Hash::hash(&map.line_col(head).0.wrapping_sub(line), &mut h);
    std::hash::Hash::hash(&text.as_bytes()[start..hi], &mut h);
    std::hash::Hasher::finish(&h)
}

/// Empties one slot like a dead fn: no C, no reads, no IR.
fn wipe_slot(caches: &mut Caches, s: usize) {
    if caches.out[s].has_code() {
        caches.wiped_slots.push(s as u32);
    }
    caches.out[s] = FnOut::default();
    caches.has_out[s] = true;
    caches.ok[s] = true;
    caches.slot_reads[s] = None;
    caches.slot_ir[s] = None;
}

/// Each instance Adt's id with its stable instance key. C names Adts by
/// id (`A<id>`), so cached C of a generic program is reusable only while
/// every id it was made under names the same instance. Ids are session
/// places (`collect::InstOrder`), so a new instance keeps the others' ids.
/// The key is of the instance's region-free args: instances that differ
/// only in lifetimes share one C type (`GlobalTys::register_adt_instance`),
/// whose Adt is the variant registered first, which an image build and a
/// one-shot build may make in another order; its name must not depend on
/// which one that was.
fn inst_adt_ids(p: &collect::Program) -> Vec<(u32, u64)> {
    let mut out = Vec::new();
    for (a, inst) in p.gx.adt_instance_of.iter().enumerate() {
        if let Some((def, args)) = inst {
            let args = crate::ty::region_free_args_get(&p.tys, *args).unwrap_or(*args);
            out.push((a as u32, p.instance_key_hash(&crate::driver::graph::InstanceKey { def: *def, args }).0));
        }
    }
    out
}

/// The size of a def order as the disk file records it: every list only
/// grows and the instance base only rises, so a store is due when it moves.
fn def_order_size(order: &collect::DefOrder) -> usize {
    order.adts.len() + order.statics.len() + order.instances.keys.len() + order.instances.base as usize
}

/// Unique temp file sequence for base-dir writes in this process. Several
/// sessions here share one base dir (the warm session and guard workers,
/// on several threads in one daemon), so a pid alone does not make a
/// temp name unique.
fn base_tmp_seq() -> u64 {
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// True if `out` exists and still names `soname` (an overwritten output names its newer base instead).
fn output_names_base(out: &Path, soname: &str) -> bool {
    std::fs::read(out).is_ok_and(|bytes| bytes.windows(soname.len()).any(|w| w == soname.as_bytes()))
}

/// True if any known output file built against base file `soname` still exists and still names it.
fn base_still_used(users: &[(String, PathBuf)], soname: &str) -> bool {
    users.iter().filter(|(u, _)| u == soname).any(|(_, out)| output_names_base(out, soname))
}

/// Deletes the base files `session` built that no kept executable still
/// names. The daemon calls it when it evicts the session: nothing will
/// relink against those files, and the manifest sweep keeps a live
/// daemon's files, so without this they would stay until the daemon exits.
pub fn release_bases(session: &super::Session) {
    let caches = &session.caches;
    let Some(dir) = &caches.base_dir else { return };
    for soname in &caches.base_files {
        if !base_still_used(&caches.base_users, soname) {
            let _ = std::fs::remove_file(dir.join(soname));
        }
    }
}

/// True when the merged Ast holds many more nodes than its last fresh
/// parse. Bodies mode, signatures mode, and the body patch append the
/// re-parsed nodes and leave the replaced ones in the arenas, so a long
/// warm session grew without bound (about 650 nodes per edit of a small
/// crate that adds or removes a fn; hundreds of MB after a few thousand
/// edits). Past twice the fresh size (plus a margin, so a small crate
/// does not reparse often) the request takes the full parse, which
/// rebuilds the Ast from the chunks and resets the count.
fn ast_bloated(front: &Front) -> bool {
    front.ast.exprs.len() > front.fresh_exprs * 2 + 65_536
}

/// The persistent directory for this session's base libraries. Executables
/// load a base by absolute rpath, so the base must sit somewhere stable:
/// the disk cache dir's `bases/` subdir first (per source tree, next to
/// other lust state), then the user cache dir, and as a last resort the
/// session object dir (old behavior; those bases die with the daemon's
/// temp dir, like any file in temp space). The disk cache being off
/// (`LUST_NO_CACHE`) does not apply here: a base is a run-time part of a
/// built executable, not a cache entry. Resolved once per session.
fn resolve_base_dir(caches: &mut Caches, src_file: &Path) -> PathBuf {
    if let Some(dir) = &caches.base_dir {
        return dir.clone();
    }
    let mut candidates = vec![crate::driver::cache::cache_dir(src_file).join("bases")];
    if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME").filter(|v| !v.is_empty()) {
        candidates.push(PathBuf::from(xdg).join("lust").join("bases"));
    } else if let Some(home) = std::env::var_os("HOME").filter(|v| !v.is_empty()) {
        candidates.push(PathBuf::from(home).join(".cache").join("lust").join("bases"));
    }
    let dir = candidates.into_iter().find(|d| std::fs::create_dir_all(d).is_ok()).unwrap_or_else(|| caches.obj_dir.clone());
    caches.base_dir = Some(dir.clone());
    dir
}

/// Moves a freshly linked base temp file to its final name. If the final
/// file already exists (same content name, or a concurrent build won
/// the rename race), the temp copy is dropped.
fn install_base(tmp: &Path, dest: &Path) -> Result<(), String> {
    if dest.exists() {
        let _ = std::fs::remove_file(tmp);
        return Ok(());
    }
    match std::fs::rename(tmp, dest) {
        Ok(()) => Ok(()),
        Err(_) if dest.exists() => {
            let _ = std::fs::remove_file(tmp);
            Ok(())
        }
        Err(e) => Err(format!("cannot move the base library to {}: {e}", dest.display())),
    }
}

/// Records one executable's use of a base in `<base_dir>/manifest`
/// (`soname <TAB> output` per line), so a later daemon can tell which
/// base files a kept executable still needs after this daemon is gone.
fn record_base_user(base_dir: &Path, soname: &str, out: &Path) {
    use std::io::Write as _;
    let line = format!("{soname}\t{}\n", out.to_string_lossy());
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(base_dir.join("manifest")) {
        let _ = f.write_all(line.as_bytes());
    }
}

/// The extension of a base library file: tcc on macOS reads a Mach-O
/// library only under its own extension.
pub const BASE_EXT: &str = if cfg!(target_os = "macos") { "dylib" } else { "so" };

/// The pid in a base file name (`libbase-<pid>-<hash>.so`): the process
/// that built it. Base files are also unique per session instance (the
/// session's object dir is mixed into the hash), so one session never
/// links against, and must never delete, another live session's file.
fn base_owner_pid(soname: &str) -> Option<u32> {
    let rest = soname.strip_prefix("libbase-")?;
    let pid = rest.split('-').next()?;
    if !pid.is_empty() && pid.bytes().all(|b| b.is_ascii_digit()) { pid.parse().ok() } else { None }
}

/// Deletes base files in `base_dir` that the manifest proves dead: every
/// recorded output for the base is gone or now names a different base.
/// A base whose owning process is still alive is never deleted: it may
/// be a live session's current base, which the owner will load on its
/// next link even if the last executable was overwritten since.
/// `exiting_pid` names a live-but-exiting owner (this daemon at
/// shutdown) whose files count as ownerless. Files with no manifest
/// entry are kept (an entry is appended right after its executable
/// links, so an unrecorded file may be in use by a concurrent build).
/// Also deletes half-written rebuild temp files
/// (`libbase-tmp-<pid>-*.so`) whose pid is gone. The manifest is
/// rewritten with only the kept, deduplicated entries. Called on a
/// session's first base build and on daemon exit.
pub fn sweep_bases(base_dir: &Path, exiting_pid: u32) {
    // Half-written temp bases from crashed builds (`daemon::pid_alive`
    // is the liveness probe).
    if let Ok(rd) = std::fs::read_dir(base_dir) {
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            if let Some(rest) = name.strip_prefix("libbase-tmp-")
                && let Some(pid) = rest.split('-').next()
                && let Ok(pid) = pid.parse::<u32>()
                && pid != std::process::id()
                && !crate::daemon::pid_alive(pid)
            {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
    let manifest = base_dir.join("manifest");
    let Ok(text) = std::fs::read_to_string(&manifest) else { return };
    // (soname, outputs) in first-seen order, outputs deduplicated.
    let mut entries: Vec<(String, Vec<PathBuf>)> = Vec::new();
    for line in text.lines() {
        let Some((soname, out)) = line.split_once('\t') else { continue };
        if soname.is_empty() || out.is_empty() {
            continue;
        }
        match entries.iter_mut().find(|(s, _)| s == soname) {
            Some((_, outs)) => {
                let p = PathBuf::from(out);
                if !outs.contains(&p) {
                    outs.push(p);
                }
            }
            None => entries.push((soname.to_string(), vec![PathBuf::from(out)])),
        }
    }
    let owner_alive = |soname: &str| match base_owner_pid(soname) {
        Some(pid) if pid == exiting_pid => false,
        Some(pid) => pid == std::process::id() || crate::daemon::pid_alive(pid),
        None => false,
    };
    let mut kept = String::new();
    for (soname, outs) in &entries {
        if owner_alive(soname) || outs.iter().any(|o| output_names_base(o, soname)) {
            for o in outs {
                kept.push_str(&format!("{soname}\t{}\n", o.to_string_lossy()));
            }
        } else {
            let _ = std::fs::remove_file(base_dir.join(soname));
        }
    }
    let tmp = base_dir.join(format!("manifest.tmp{}-{}", std::process::id(), base_tmp_seq()));
    if std::fs::write(&tmp, kept).is_ok() && std::fs::rename(&tmp, &manifest).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

/// A thread a build starts early for an answer it takes later (`take`). Dropped untaken, it
/// is joined: no thread of a build outlives it (the image's background save forks after).
struct Joined<T>(Option<std::thread::JoinHandle<T>>);

impl<T> Joined<T> {
    /// The thread's answer; None when it panicked, or once taken.
    fn take(&mut self) -> Option<T> {
        self.0.take().and_then(|h| h.join().ok())
    }
}

impl<T> Drop for Joined<T> {
    fn drop(&mut self) {
        self.take();
    }
}

/// B1's record of the release statics pass (`cgen::names::statics_parts`): one for the index
/// (unit 1) and every part.
const STATICS_RECORD: &str = "release statics";

/// The cc fingerprint of unit `k` of a statics pass whose record has fingerprint `fp`: the
/// index for 0, part `k - 1` after. The record's reads make every text of the pass, so its
/// fingerprint stands for each of them.
fn statics_unit_fp(fp: u128, k: usize) -> u128 {
    let (a, b) = crate::driver::cache::hash128(&[&fp.to_le_bytes(), &(k as u64).to_le_bytes()], 19);
    (a as u128) << 64 | b as u128
}

/// The memo pre-check's name of unit `k` of the statics pass (`statics_unit_fp`).
fn statics_unit_name(k: usize) -> String {
    format!("{STATICS_RECORD} {k}")
}

/// B1: the last build's fingerprint of the unit recorded as `reg`, when its record has the
/// identity `id` and every read it holds kept its fingerprint (`now`, by read index).
fn b1_clean_by(records: &FxMap<String, cgen::record::UnitRecord>, now: &[Option<(u64, u64)>], reg: &str, id: (u64, u64)) -> Option<u128> {
    records.get(reg).filter(|old| old.id == id && old.reads.iter().all(|&(i, f)| now.get(i as usize).copied().flatten() == Some(f))).map(|old| old.fp)
}

/// Runs `f` for each item on all cores, on the persistent pool (src/pool.rs).
/// Results keep the input order.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    crate::pool::par_map(items, f)
}

/// The crates (by root module: the local crate, its source dependencies)
/// where no macro but the builtin can take a builtin macro's name
/// (`macro_scope::dep_macros_shut`), over each crate's files. Each file belongs to
/// the crate of the module the resolver gave it (a file two crates share
/// has one id per crate); one with no recorded module counts for every
/// crate. A dependency is clean when it compiles from source here and its
/// own files pass the scan, with its own dependencies judged the same way.
/// `root_text` is the root file without the std splice.
fn dep_macros_shut(front: &Front, tables: &crate::resolve::imports::ResolvedTables, root_text: &str) -> Vec<crate::ty::defs::ModuleId> {
    use crate::resolve::imports::ResolvedTables;
    use crate::ty::defs::ModuleId;
    let mut texts: FxMap<Option<ModuleId>, Vec<&str>> = FxMap::default();
    for k in 0..front.map.file_count() {
        let f = FileId(k as u32);
        let Some(text) = (if k == 0 { Some(root_text) } else { front.map.text(f) }) else { return Vec::new() };
        texts.entry(tables.macro_scopes.get(&f).map(|(m, _)| tables.root_of(*m))).or_default().push(text);
    }
    /// The scan of crate `root`, its dependencies judged recursively
    /// (memoized by crate root; the crate graph has no cycle).
    fn shut(
        root: ModuleId,
        front: &Front,
        tables: &ResolvedTables,
        texts: &FxMap<Option<ModuleId>, Vec<&str>>,
        memo: &std::cell::RefCell<FxMap<ModuleId, bool>>,
    ) -> bool {
        if let Some(&ok) = memo.borrow().get(&root) {
            return ok;
        }
        let deps: Vec<(Sym, Option<ModuleId>)> =
            tables.externs.iter().filter(|e| e.owner == root && !e.is_std_lib).map(|e| (front.interner.intern(&e.name), e.root_module)).collect();
        let names: Vec<Sym> = deps.iter().map(|d| d.0).collect();
        let crate_texts: Vec<&str> = texts.get(&Some(root)).into_iter().chain(texts.get(&None)).flatten().copied().collect();
        let clean = |d: Sym| deps.iter().any(|&(n, r)| n == d && r.is_some_and(|r| r != root && shut(r, front, tables, texts, memo)));
        let ok = super::macro_scope::dep_macros_shut(&crate_texts, &front.interner, &names, &clean);
        memo.borrow_mut().insert(root, ok);
        ok
    }
    let memo = Default::default();
    let mut roots: Vec<ModuleId> = tables.crate_cfgs.keys().copied().filter(|r| r.0 != 0).collect();
    roots.sort_unstable_by_key(|r| r.0);
    roots.insert(0, ModuleId(0));
    roots.into_iter().filter(|&r| shut(r, front, tables, &texts, &memo)).collect()
}

/// The dirty count of each stored read set in `sets` against `p` (None
/// for a slot with no stored reads), the answers
/// `Program::reads_dirty_memo` gives one set at a time (sigedit P4.4).
/// Many reads (a full-mode walk, every instance after an item-level
/// edit) go in parallel through `answers` (`KeyAnswers`), which the
/// request's walks share: a key's fingerprint is computed once for all of
/// them. Few stay on this thread.
fn reads_dirty_par(
    p: &collect::Program,
    sets: &[Option<&crate::driver::graph::Reads>],
    keys: &crate::driver::graph::ReadKeys,
    answers: &mut crate::driver::graph::KeyAnswers,
) -> Vec<Option<usize>> {
    let total: usize = sets.iter().flatten().map(|r| r.len()).sum();
    if total < 4096 || crate::pool::threads() < 2 {
        let mut memo = FxMap::default();
        return sets.iter().map(|r| r.map(|r| p.reads_dirty_memo(r, keys, &mut memo))).collect();
    }
    answers.dirty_counts(p, sets, keys)
}

static NEXT_VERIFIED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// A fresh program generation (`Program::verified`, `Reads::verified`).
fn next_verified() -> u64 {
    NEXT_VERIFIED.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// The process-wide counters a session's stored marks order against
/// (`next_verified`, the generic reuse stamp). A front image
/// (src/image.rs) carries them, so a restored session's marks never
/// collide with new ones.
pub struct Stamps {
    verified: u64,
    reuse: u64,
}

impl Stamps {
    pub fn now() -> Stamps {
        Stamps { verified: NEXT_VERIFIED.load(std::sync::atomic::Ordering::Relaxed), reuse: super::gen_reuse::stamp_now() }
    }
    /// Moves both counters up to these values (never down).
    pub fn restore(&self) {
        NEXT_VERIFIED.fetch_max(self.verified, std::sync::atomic::Ordering::Relaxed);
        super::gen_reuse::stamp_restore(self.reuse);
    }
}

/// The keyed dirty walk after a header delta (Sol review 2 item 1), by
/// slot: Some(dirty) for a read set that held against the delta's base
/// program (`Reads::verified` of its mode is `base`), where only the keys the delta can
/// move (`moved`: `kept_delta::Touched`, or only `Checked` keys after body
/// edits alone) may have moved, so only those compare (graph.rs
/// `keyed_dirty_slots`). None for any other slot: a read set of
/// another program, or none; the full walk decides it.
fn keyed_dirty(
    p: &collect::Program,
    front: &Front,
    caches: &mut Caches,
    moved: &(dyn Fn(&crate::driver::graph::ReadKey) -> bool + Sync),
    base: u64,
    answers: &mut FxMap<crate::driver::graph::ReadKey, crate::driver::graph::Read>,
) -> Vec<Option<bool>> {
    let mode = usize::from(p.gx.walk_instances);
    let def_slot = |d: def::DefId| p.local_def(d.hash).and_then(|l| front.fn_slot.get(l.0 as usize)).map(|&s| s as usize);
    // `moved` is a pure test: every key takes it on all cores.
    let quick = |k: &crate::driver::graph::ReadKey| Some(moved(k));
    let (dirty, _) = crate::driver::graph::keyed_dirty_slots(p, &caches.slot_reads, &caches.read_keys, &quick, &mut |k| moved(k), &def_slot, answers);
    caches.slot_reads.iter().zip(dirty).map(|(r, d)| r.as_ref().filter(|r| r.verified[mode] == base).map(|_| d)).collect()
}

/// The file's inner `allow` attributes, for seeding later chunks so a
/// chunk parse builds the same item attributes as a whole parse. Empty
/// when there is only one chunk (it reads them itself).
fn chunk_seed_allows(front: &Front) -> Vec<crate::ast::Attr> {
    if front.chunks.len() < 2 {
        return Vec::new();
    }
    parser::leading_allows(&front.chunks[0].lexed, &front.interner, &front.known)
}

/// Parses chunk `i`: the first chunk as a whole parse, later chunks
/// seeded with the file's inner allows.
fn parse_chunk(front: &Front, i: usize, seed: &[crate::ast::Attr]) -> Result<Ast, Diag> {
    if i == 0 {
        parser::parse(&front.chunks[i].lexed, &front.interner, &front.known)
    } else {
        parser::parse_seeded(&front.chunks[i].lexed, &front.interner, &front.known, seed)
    }
}

/// Splits source into chunks of whole top-level items, about `2 * cores` of them. Boundaries are
/// content-defined: the chunk is cut before an item when a hash of the item's header line hits a
/// mask. So editing or inserting an item only changes the chunk it is in, and every other chunk
/// keeps its exact text (and can be reused). A chunk only starts at a line that begins an item at
/// column 0, is a proven top-level boundary (`boundaries`, from `BoundaryScan`), and never
/// between an attribute and its item. `headers`, when given, are the `item_headers` of the whole
/// source (used on a session's first compile, where the region is the whole source and the mask
/// needed the same table).
fn split_items(
    src: &str,
    region: std::ops::Range<usize>,
    mask: u64,
    headers: Option<&[(usize, u64)]>,
    boundaries: &[usize],
) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut chunk_start = region.start;
    let cut = |at: usize, h: u64, ranges: &mut Vec<(usize, usize)>, chunk_start: &mut usize| {
        // The multiply spreads FxHash's low bits.
        if (h.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 40) & mask == 0 && boundaries.binary_search(&(region.start + at)).is_ok() {
            ranges.push((*chunk_start, region.start + at));
            *chunk_start = region.start + at;
        }
    };
    match headers {
        Some(headers) => {
            for &(at, h) in headers.iter().skip(1) {
                cut(at, h, &mut ranges, &mut chunk_start);
            }
        }
        None => {
            for (at, h) in item_headers(&src[region.clone()]).into_iter().skip(1) {
                cut(at, h, &mut ranges, &mut chunk_start);
            }
        }
    }
    ranges.push((chunk_start, region.end));
    ranges
}

/// The mask that makes `split_items` produce about `2 * cores` chunks for a source with
/// `item_count` top-level items.
fn split_mask(src_len: usize, item_count: usize, cores: usize) -> u64 {
    if src_len < 64 * 1024 {
        // Small files: one chunk (no item hash has all 24 masked bits zero in practice).
        return (1 << 24) - 1;
    }
    ((item_count / (cores * 2)).max(1).next_power_of_two() - 1) as u64
}

/// A byte scanner that mirrors the lexer's states (strings, chars, comments) and tracks bracket
/// depth. It proves chunk boundaries: a line start is a top-level item boundary only if the
/// scanner is in the normal state there with all depths at zero. A deleted brace, an inserted
/// `/*` or `"`, or a column-0 method line inside an impl all fail this test, so chunks are only
/// split or reused where the split is still real in the new text.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ScanState {
    Normal,
    Str,
    Char,
    LineComment,
    BlockComment(u32),
}

/// The bytes that can change `BoundaryScan`'s state in normal code: a newline (a line
/// start to record), comment and literal openers, and brackets.
const NORMAL_STOPS: [bool; 256] = {
    let mut t = [false; 256];
    let stops = b"\n/\"'{}()[]";
    let mut k = 0;
    while k < stops.len() {
        t[stops[k] as usize] = true;
        k += 1;
    }
    t
};

struct BoundaryScan {
    state: ScanState,
    brace: i64,
    paren: i64,
    bracket: i64,
}

impl BoundaryScan {
    fn new() -> BoundaryScan {
        BoundaryScan { state: ScanState::Normal, brace: 0, paren: 0, bracket: 0 }
    }
    fn clean(&self) -> bool {
        self.state == ScanState::Normal && self.brace == 0 && self.paren == 0 && self.bracket == 0
    }
    /// Feeds `b` (which starts at absolute offset `base`). Pushes every clean line start after a
    /// newline into `out`, when given.
    fn feed(&mut self, b: &[u8], base: usize, mut out: Option<&mut Vec<usize>>) {
        let mut i = 0;
        while i < b.len() {
            match self.state {
                ScanState::Normal => {
                    // Most bytes cannot change the state: skip them in a tight loop.
                    while i < b.len() && !NORMAL_STOPS[b[i] as usize] {
                        i += 1;
                    }
                    if i == b.len() {
                        break;
                    }
                    let c = b[i];
                    match c {
                        b'\n' => {
                            i += 1;
                            if self.clean() {
                                if let Some(out) = out.as_deref_mut() {
                                    out.push(base + i);
                                }
                            }
                            continue;
                        }
                        b'/' if b.get(i + 1) == Some(&b'/') => {
                            self.state = ScanState::LineComment;
                            i += 2;
                            continue;
                        }
                        b'/' if b.get(i + 1) == Some(&b'*') => {
                            self.state = ScanState::BlockComment(1);
                            i += 2;
                            continue;
                        }
                        b'"' => self.state = ScanState::Str,
                        b'\'' => {
                            // A char literal, or a lifetime (same test as the lexer).
                            let is_char = match b.get(i + 1) {
                                Some(b'\\') => true,
                                Some(&n) => {
                                    let len = if n < 0x80 {
                                        1
                                    } else if n < 0xE0 {
                                        2
                                    } else if n < 0xF0 {
                                        3
                                    } else {
                                        4
                                    };
                                    b.get(i + 1 + len) == Some(&b'\'')
                                }
                                None => false,
                            };
                            if is_char {
                                self.state = ScanState::Char;
                            }
                        }
                        b'{' => self.brace += 1,
                        b'}' => self.brace -= 1,
                        b'(' => self.paren += 1,
                        b')' => self.paren -= 1,
                        b'[' => self.bracket += 1,
                        b']' => self.bracket -= 1,
                        _ => {}
                    }
                    i += 1;
                }
                ScanState::Str => match b[i] {
                    b'\\' => i += 2,
                    b'"' => {
                        self.state = ScanState::Normal;
                        i += 1;
                    }
                    _ => i += 1,
                },
                ScanState::Char => match b[i] {
                    b'\\' => i += 2,
                    b'\'' => {
                        self.state = ScanState::Normal;
                        i += 1;
                    }
                    _ => i += 1,
                },
                ScanState::LineComment => {
                    if b[i] == b'\n' {
                        self.state = ScanState::Normal;
                        i += 1;
                        if self.clean() {
                            if let Some(out) = out.as_deref_mut() {
                                out.push(base + i);
                            }
                        }
                    } else {
                        i += 1;
                    }
                }
                ScanState::BlockComment(d) => {
                    let c = b[i];
                    if c == b'/' && b.get(i + 1) == Some(&b'*') {
                        self.state = ScanState::BlockComment(d + 1);
                        i += 2;
                    } else if c == b'*' && b.get(i + 1) == Some(&b'/') {
                        self.state = if d == 1 { ScanState::Normal } else { ScanState::BlockComment(d - 1) };
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
            }
        }
    }
}

/// True if lexing `text` from a clean top-level point ends in the normal state (not inside a
/// comment or string, all depths zero).
fn chunk_ends_clean(text: &str) -> bool {
    let mut scan = BoundaryScan::new();
    scan.feed(text.as_bytes(), 0, None);
    scan.clean()
}

/// True if a chunk may be reused in front of other text: it ends at a top-level item boundary
/// (token scan) and in a clean lex state. The lex test matters for a chunk that ends inside a
/// `//` comment with no trailing newline: its standalone tokens end there, but in the new text
/// the comment ends at the next newline and the bytes after it are code again. A chunk that
/// lexed without error can only end unclean inside a line comment, which a trailing newline
/// rules out, so the byte scan runs only for chunks without one.
fn chunk_end_ok(c: &Chunk) -> bool {
    c.scan.ends_at_boundary && (c.text.ends_with('\n') || chunk_ends_clean(&c.text))
}

/// True when a chunk's expansion reads token positions (`line!`,
/// `column!`, `file!`, `stringify!`, `dbg!`): its expanded tokens are
/// only valid at the position they were expanded at, so a kept chunk
/// that moved must be lexed and expanded again. The text scan is
/// deliberately loose (a name inside a longer identifier also hits);
/// a false hit costs one relex, a miss would serve a stale `line!`.
/// A chunk that began the file with `#!` is too: the lexer skips a
/// shebang only at offset 0, so moved later the same text lexes apart.
fn chunk_pos_sensitive(c: &Chunk) -> bool {
    (c.start == 0 && c.text.starts_with("#!")) || ["line!", "column!", "file!", "stringify!", "dbg!"].iter().any(|n| c.text.contains(n))
}

/// True when `lexed` holds an inner attribute opener (`#` then `!`). A file
/// with one compiles as one chunk, as the resolver keeps it one segment
/// (`item_segments`). Chunks parse on their own: a later chunk would take a
/// `#![..]` at its start as file attributes even after an item, and a kept
/// chunk would keep the file allows it was parsed under after an edit
/// changed them (`chunk_seed_allows` seeds re-parsed chunks only). Both
/// were warm false accepts. So a split file never has a leading inner run
/// to seed from.
fn has_inner_attr(lexed: &lexer::Lexed) -> bool {
    lexed.tokens.windows(2).any(|w| w[0].tok == lexer::Tok::Pound && w[1].tok == lexer::Tok::Bang)
}

/// True when a chunk's expansion reads files outside the source
/// (`include!` and kin): such a chunk is never reused, because the
/// included file can change while the source text stays the same.
fn chunk_reads_files(c: &Chunk) -> bool {
    c.text.contains("include")
}

/// Moves every AST span of the root file for the request's one edit:
/// old bytes `a..b` (the text between the common prefix and suffix) now
/// take `b - a + delta` bytes. The walk is `span_shift::shift_ast`, which
/// a test holds to a re-parse of edited text; a hand list of span fields
/// here once missed `ImplDef::span`, and a std impl spliced after the
/// edit fell out of `Ast::lang_methods` (fuzz realish seed 42, iter 135).
/// Runs before anything new is parsed in this compile, so every span in
/// the AST is still in old coordinates.
fn shift_ast_spans(front: &mut Front, a: usize, b: usize, delta: i64) {
    if delta == 0 {
        return;
    }
    let edit = span_shift::Edit { file: ROOT_FILE, a: a.min(b) as u32, b: b as u32, d: delta };
    span_shift::shift_ast(Arc::make_mut(&mut front.ast), edit, None, &mut Default::default());
}

/// True when a column-0 line starts an outer doc comment, which the lexer
/// emits as `#[doc = ..]` tokens: `///` (not `////`) or `/**` (not `/***`
/// or `/**/`). Same rule as the lexer.
fn is_doc_line(line: &str) -> bool {
    (line.starts_with("///") && !line[3..].starts_with('/'))
        || (line.starts_with("/**") && !line[3..].starts_with('*') && !line.starts_with("/**/"))
}

/// (offset of each top-level item's first line, hash of its header line).
/// An item preceded by attributes gets the first attribute line as its
/// offset, so a chunk cut at a header never falls between an attribute
/// and its item. Doc comments are attributes. A pending attribute run
/// carries across blank and comment lines and resolves at the next item
/// line; lines inside a block comment starting at column 0 are neither.
fn item_headers(src: &str) -> Vec<(usize, u64)> {
    let starts = ["fn ", "pub ", "struct ", "enum ", "impl ", "use "];
    let mut items = Vec::new();
    let mut pending: Option<usize> = None;
    let mut in_block = false;
    let mut pos = 0;
    for line in src.split_inclusive('\n') {
        if in_block {
            if line.contains("*/") {
                in_block = false;
            }
            pos += line.len();
            continue;
        }
        let is_attr = line.starts_with("#[") || is_doc_line(line);
        if is_attr && pending.is_none() {
            pending = Some(pos);
        } else if starts.iter().any(|s| line.starts_with(s)) {
            let at = pending.take().unwrap_or(pos);
            let mut h = crate::intern::FxHasher::default();
            std::hash::Hash::hash(line, &mut h);
            items.push((at, std::hash::Hasher::finish(&h)));
        }
        // A block comment that opens at column 0 and does not close on
        // this line hides the lines it spans from the tests above.
        if line.starts_with("/*") && !line[2..].contains("*/") {
            in_block = true;
        }
        pos += line.len();
    }
    items
}

/// Lengths of the common prefix and common suffix of two strings (not overlapping).
pub(super) fn common_ends(a: &[u8], b: &[u8]) -> (usize, usize) {
    // Compare in blocks first: slice equality is a fast memcmp.
    let n = a.len().min(b.len());
    let mut p = 0;
    while p + 4096 <= n && a[p..p + 4096] == b[p..p + 4096] {
        p += 4096;
    }
    while p < n && a[p] == b[p] {
        p += 1;
    }
    let max_s = n - p;
    let mut q = 0;
    while q + 4096 <= max_s && a[a.len() - q - 4096..a.len() - q] == b[b.len() - q - 4096..b.len() - q] {
        q += 4096;
    }
    while q < max_s && a[a.len() - q - 1] == b[b.len() - q - 1] {
        q += 1;
    }
    (p, q)
}

fn errors(diags: &mut [Diag], map: &SourceMap, src: &str, req: &Request) -> Response {
    // Exact duplicates first: a delta path and a full collect can
    // push the same diagnostic a different number of times, and
    // the daemon guard compares this answer byte for byte with a
    // fresh session's (render order itself is `diag::diag_order`).
    let n = diag::dedup_exact(diags, map);
    let diags = &mut diags[..n];
    let json = req.json;
    let text = diag::render(diags, map, src, json, req.max_errors);
    let mut r = Response { code: 1, ..Default::default() };
    if json {
        r.stdout = text;
    } else {
        r.stderr = text;
        let path = map.path(ROOT_FILE);
        let _ = writeln!(r.stderr, "error: could not compile `{path}` due to {} previous error(s)", diags.len());
    }
    r
}

/// FxHash of one source file's current text in the map: the guard
/// under which cached IR spans stay valid (`ir_cache::CachedBody`).
fn file_text_hash(map: &SourceMap, file: FileId) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(map.text(file).unwrap_or(""), &mut h);
    std::hash::Hasher::finish(&h)
}

/// The Adt and static indices `collect` will assign for one Ast under the
/// session `DefOrder`, predicted with the same hash and rank rules collect
/// uses: every Adt (body types included) and every static (nested ones by
/// `collect::nested_static_hashes` over `fns`, every fn's body and def
/// hash in LocalDefId order) ranks by identity, append-only, so an added
/// item moves no other item's index. Instance Adt ids are session places
/// that new instances do not move; the build checks them itself
/// (`inst_adt_ids`) and regenerates C if one ever names another instance.
/// The slot update compares the prediction with the last parse's indices:
/// cached output carries session-local indices (CTy in glue and type sets,
/// static indices in IR), so it is reusable only when every old def keeps
/// its index (a removed def moves the ranks after it).
fn predicted_def_ids(
    ast: &Ast,
    interner: &Interner,
    stable: StableCrateHash,
    order: &collect::DefOrder,
    fns: &[(Option<crate::ast::BlockId>, crate::def::DefPathHash)],
) -> (FxMap<crate::def::DefPathHash, u32>, FxMap<crate::def::DefPathHash, u32>) {
    let mut adt_hashes: Vec<crate::def::DefPathHash> = Vec::new();
    let mut static_hashes: Vec<crate::def::DefPathHash> = Vec::new();
    let mut counts: FxMap<Sym, u32> = FxMap::default();
    for item in &ast.items {
        match &item.kind {
            ItemKind::Struct(s) => {
                let disamb = *counts.entry(s.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(s.name), disamb));
            }
            ItemKind::Enum(e) => {
                let disamb = *counts.entry(e.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(e.name), disamb));
            }
            ItemKind::Union(u) => {
                // Collect numbers no Adt for a union today, but the
                // old sequence hash counted it as an Adt-shaped def:
                // keep it in the map so a union edit still guards.
                let disamb = *counts.entry(u.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(u.name), disamb));
            }
            ItemKind::Static(s) => {
                static_hashes.push(def::item_hash(stable, &[], def::DefKind::Static, interner.get(s.name), 0));
            }
            _ => {}
        }
    }
    // Structs and enums inside function bodies rank with the other
    // Adts (collect pass 1 folds the same hashes). Without one, the
    // fn hashes are not computed.
    if def::has_body_type_items(ast) {
        let top = collect::top_fn_hashes(ast, interner, stable);
        let fn_ids = def::nested_fn_ids(
            ast,
            interner,
            |b| top.get(&b).copied(),
            |parent, name, disamb| def::child_hash(*parent, def::DefKind::Fn, name, disamb),
            |seg, name| def::free_fn_hash(stable, &[seg], name),
        );
        let parent_of = |par: def::NestParent| match par {
            def::NestParent::Top(b) => top.get(&b).copied(),
            def::NestParent::Nested(k) => fn_ids.get(k as usize).copied().flatten(),
            def::NestParent::Unknown => None,
        };
        let type_ids = def::nested_type_ids(
            ast,
            interner,
            |par| parent_of(par),
            |parent, kind, name, disamb| def::child_hash(*parent, kind, name, disamb),
            |seg, kind, name| def::item_hash(stable, &[seg], kind, name, 0),
        );
        for (idx, item) in ast.stmt_items.iter().enumerate() {
            if matches!(item.kind, ItemKind::Struct(_) | ItemKind::Enum(_))
                && let Some(h) = type_ids[idx]
            {
                adt_hashes.push(h);
            }
        }
    }
    static_hashes.extend(collect::nested_static_hashes(ast, interner, stable, fns).into_iter().flatten());
    // Collect also numbers the synthetic std Adts (check/collect.rs
    // pass 1), always (a user type of the same name only shadows its
    // flat name): predict the same extra hashes.
    for (_, _, def, _) in crate::check::generics::std_adts() {
        adt_hashes.push(def.hash);
    }
    let to_map = |hashes: &[crate::def::DefPathHash], ranks: Vec<u32>| -> FxMap<crate::def::DefPathHash, u32> {
        hashes.iter().copied().zip(ranks).collect()
    };
    let adts = to_map(&adt_hashes, collect::stable_ranks_preview(&order.adts, &adt_hashes));
    let statics = to_map(&static_hashes, collect::stable_ranks_preview(&order.statics, &static_hashes));
    (adts, statics)
}

/// True when every static of `prev` that `new` still has keeps its index
/// (an index is a static's place in `Program::statics`).
fn statics_kept(prev: &[crate::def::DefId], new: &[crate::def::DefId]) -> bool {
    let at: FxMap<crate::def::DefId, usize> = new.iter().enumerate().map(|(i, d)| (*d, i)).collect();
    prev.iter().enumerate().all(|(i, d)| at.get(d).is_none_or(|&j| j == i))
}

/// Every fn's body and def hash in LocalDefId order (`fn_loc` and its
/// `fn_keys`), as `predicted_def_ids` takes them.
fn fn_bodies(ast: &Ast, fn_loc: &[(usize, Option<usize>)], keys: &[FnKey]) -> Vec<(Option<crate::ast::BlockId>, crate::def::DefPathHash)> {
    fn_loc.iter().zip(keys).map(|(&(item, sub), k)| (fn_def_at(ast, item, sub).body, k.disk.hash)).collect()
}

/// True when every def of `prev` that `new` still has keeps its index. A
/// removed def leaves a hole (`collect::stable_ranks`): the bodies that
/// named it read it (a failed lookup now), and nothing else moves.
fn ids_kept(prev: &FxMap<crate::def::DefPathHash, u32>, new: &FxMap<crate::def::DefPathHash, u32>) -> bool {
    prev.iter().all(|(h, id)| new.get(h).is_none_or(|n| n == id))
}

/// True when a disk-loaded `order` names none of this parse's defs:
/// a stale file for a different def set. The file's stable crate
/// hash already matched at decode, so zero overlap means the
/// crate's types were replaced wholesale; the caller drops the
/// order and numbers fresh. An empty order or an empty parse is
/// never stale (nothing to distrust, or nothing to number yet).
fn def_order_stale(
    order: &collect::DefOrder,
    adt_ids: &FxMap<crate::def::DefPathHash, u32>,
    static_ids: &FxMap<crate::def::DefPathHash, u32>,
) -> bool {
    let loaded_any = !order.adts.is_empty() || !order.statics.is_empty();
    let current_any = !adt_ids.is_empty() || !static_ids.is_empty();
    let overlap = order.adts.iter().any(|h| adt_ids.contains_key(h)) || order.statics.iter().any(|h| static_ids.contains_key(h));
    loaded_any && current_any && !overlap
}

/// True when the places of `ids` (Adt or static indices of one parse)
/// hold more than twice as many holes as defs, plus some slack.
fn def_order_sparse(ids: &FxMap<crate::def::DefPathHash, u32>) -> bool {
    let rows = ids.values().map(|&i| i as usize + 1).max().unwrap_or(0);
    rows > 3 * ids.len() + 64
}

/// True when the non-fn item hash sequence differs between two item
/// lists (a type, impl, const, or structure edit happened).
fn nonfn_items_changed(old: &[scan::ItemScan], new: &[scan::ItemScan]) -> bool {
    let others = |items: &[scan::ItemScan]| items.iter().filter(|i| i.fn_name.is_none()).map(|i| i.hash).collect::<Vec<_>>();
    others(old) != others(new)
}

/// After a parse that was not "bodies only": update item tables, assign slots by
/// stable def hash, and pick the functions to re-check. Returns (changed,
/// mention_only, const_fn_changed): changed local ids as indexes, plus the subset the read-set
/// dirty walk may still reuse after collect (body hash equal, last check
/// passed, own signature item unchanged), plus whether a const fn's body or
/// signature changed. A const fn change can move const and static values,
/// array lengths, and discriminants that other items baked in, so every
/// unchanged passing body becomes a walk candidate then, as in full mode;
/// the caller also rebuilds the glue unit (it holds the statics). In signatures mode the candidates
/// are the bodies that mention a changed name; in full mode every unchanged
/// passing body is a candidate and the walk decides from its recorded reads
/// (Binding, MethodSet, ImplSet, Sig, Layout; Sig fingerprints hash named
/// Adt layouts deeply, so type and impl edits dirty through them). Full
/// mode falls back to clearing every cache when reuse is not provable: the
/// first compile, an Adt or static index change (cached C and glue carry
/// session-local indices), or slot compaction (cached C carries slot
/// numbers). The one failure is a def hash collision (src/def.rs): an
/// internal error the caller turns into a code 3 response.
#[allow(clippy::too_many_arguments)]
fn slot_update(
    front: &mut Front,
    caches: &mut Caches,
    item_scans: Vec<scan::ItemScan>,
    env: u64,
    changed_names: Option<Vec<Sym>>,
    fn_at: &[(usize, usize)],
    crate_ids: CrateIds,
    scan_of: &dyn Fn(&Front, usize) -> (u64, u32),
    t: &mut Timer,
    narrow: Option<&[usize]>,
) -> Result<(Vec<usize>, Vec<usize>, bool), String> {
    let fn_count = fn_at.len();
    // A proven item patch in signatures mode (`Patched::item_fns`, the
    // edited fns): each new fn takes its old one's place with the same
    // outline (item_outline.rs: attributes, qualifiers, name, generic
    // names), and no item comes or goes. So fn locations, Adt and static
    // ids, slot keys, and every other fn's head stand; only the edited
    // fns' heads are new (`narrow_moved` proves it under the oracle).
    let narrow = narrow.filter(|_| changed_names.is_some() && !front.def_order_loaded && front.fn_loc.len() == fn_count && front.fn_slot.len() >= fn_count);
    if let Some(edited) = narrow
        && super::item_oracle::on()
        && let Some(why) = narrow_moved(front, crate_ids, edited)
    {
        super::item_oracle::fail("narrow slot update", "item", why);
    }
    if narrow.is_none() {
        front.fn_loc = fn_locations(&front.ast);
    }
    let after_reject = std::mem::take(&mut front.walk_after_reject);
    // The derive delta's keyed shortcuts hold only when derive keys are all
    // that moved since the last walk: not after a rejected collect.
    if after_reject {
        caches.derive_only = false;
    }
    let had_env = after_reject || front.env_hash.is_some();
    // Fn keys (stable fn identities) first: nested statics fold their
    // identity from the fn that holds them (`predicted_def_ids`).
    let keys = narrow.is_none().then(|| {
        let keys = fn_keys(&front.ast, &front.fn_loc, &front.interner, crate_ids.stable);
        t.lap("slots: fn keys");
        keys
    });
    let (changed_names, nonfn_changed, ids_stable) = if narrow.is_some() {
        front.ids_forced_full = false;
        (changed_names, false, had_env)
    } else {
        let fns = fn_bodies(&front.ast, &front.fn_loc, keys.as_deref().unwrap_or(&[]));
        // Cached output stays reusable in full mode when every Adt and
        // static of the last parse keeps its session-local index in
        // this parse: an added def takes a new place at the end of the
        // session order, a removed one leaves a hole, and body items rank
        // by identity like any other. (Instance Adt ids of a generic
        // program are session places; a build regenerates C when they
        // move.)
        let (mut adt_ids, mut static_ids) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order, &fns);
        // A def order loaded from disk is trusted only when it names at
        // least one def of this parse (`def_order_stale`).
        if front.def_order_loaded {
            front.def_order_loaded = false;
            if def_order_stale(&front.def_order, &adt_ids, &static_ids) {
                front.def_order = collect::DefOrder::default();
                front.def_order_stored = 0;
                (adt_ids, static_ids) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order, &fns);
            }
        }
        // Removed defs leave holes (`collect::stable_ranks`); once they
        // pile up, the order restarts dense: every index moves once, and
        // the caches reset (`ids_kept` below).
        if def_order_sparse(&adt_ids) || def_order_sparse(&static_ids) {
            front.def_order = collect::DefOrder::default();
            front.def_order_stored = 0;
            (adt_ids, static_ids) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order, &fns);
        }
        let ids_stable = had_env && ids_kept(&front.prev_adt_ids, &adt_ids) && ids_kept(&front.prev_static_ids, &static_ids);
        front.prev_adt_ids = adt_ids;
        front.prev_static_ids = static_ids;
        // Bodies and signatures modes keep cached C, which names Adts and
        // statics by index. A fn or body edit can move those indices when a
        // body holds a type item or a static (a removed fn or body item
        // takes its types along, and the ranks after it move down), so such
        // an edit takes the full path, as an item edit would.
        front.ids_forced_full = had_env && !ids_stable && changed_names.is_some();
        let changed_names = if front.ids_forced_full { None } else { changed_names };
        let nonfn_changed = had_env && nonfn_items_changed(&front.items, &item_scans);
        (changed_names, nonfn_changed, ids_stable)
    };
    t.lap("slots: def ids");
    front.env_hash = Some(env);
    front.items = item_scans;
    // Live slots: the AST fns and the last program's instances (a check
    // of a program with generic associated consts makes them too).
    let live_slots = fn_count + front.inst_live;
    let compact = front.slot_of.len() > live_slots * 2 + 64;
    // Full mode may keep the caches (and let the dirty walk pick the
    // work set) only when Adt and static ids are stable. Slot
    // compaction renumbers, but per-slot state remaps by stable
    // identity below and C re-emits from cached IR in the tail, so
    // it preserves too.
    let full_walk = changed_names.is_none() && ids_stable;
    // Per-slot state taken out for a compaction remap, keyed back in
    // by stable identity after assignment.
    struct SlotVecs {
        ok: Vec<bool>,
        out: Vec<FnOut>,
        has_out: Vec<bool>,
        reads: Vec<Option<crate::driver::graph::Reads>>,
        ir: Vec<Option<super::ir_cache::CachedBody>>,
        hash: Vec<u64>,
        head: Vec<u64>,
    }
    let mut remap: Option<(FxMap<DiskDefId, u32>, SlotVecs)> = None;
    if full_walk && compact {
        let old = SlotVecs {
            ok: std::mem::take(&mut caches.ok),
            out: std::mem::take(&mut caches.out),
            has_out: std::mem::take(&mut caches.has_out),
            reads: std::mem::take(&mut caches.slot_reads),
            ir: std::mem::take(&mut caches.slot_ir),
            hash: std::mem::take(&mut front.slot_hash),
            head: std::mem::take(&mut front.slot_head),
        };
        remap = Some((front.slot_of.clone(), old));
        // Full mode walks every passing body, so the pending slots
        // (old numbers) are covered.
        front.walk_pending.clear();
        // Instance slots are not remapped: they get new numbers after
        // collect and recheck there (`slots_renumbered`).
        front.inst_slot.clear();
        front.slots_renumbered = true;
        front.slot_of.clear();
        front.slot_paths.clear();
        front.slot_manifest_stored = 0;
        // The base relinks under the new numbers; renumbered C is
        // re-emitted from cached IR in the tail (or rechecked when no
        // IR is cached), never reused as-is.
        caches.objects = None;
        caches.overlays.clear();
    }
    if changed_names.is_none() && !full_walk {
        // Full rebuild: fresh caches, but slots stay append-only (section
        // 4.2): existing fns keep the slots the manifest gave them, a
        // seeded manifest from a previous daemon included, so slot
        // numbers are stable across restarts and load orders. Only when
        // dead slots outnumber live fns by a wide margin does a full
        // rebuild compact: it renumbers in def order and the stored
        // manifest is rewritten (the base rebuild of 4.2, in slot form).
        if front.slot_of.len() > live_slots * 2 + 64 {
            front.slot_of.clear();
            front.slot_paths.clear();
            front.slot_manifest_stored = 0;
            front.inst_slot.clear();
        }
        caches.ok.clear();
        caches.out.clear();
        caches.has_out.clear();
        caches.slot_reads.clear();
        caches.slot_ir.clear();
        front.slot_hash.clear();
        front.slot_head.clear();
        caches.glue = GlueSet::default();
        caches.objects = None;
        caches.overlays.clear();
        // Grouping restarts here: the build below regroups every slot
        // by C bytes. A persistent session that adopted the manifest's
        // recorded byte target keeps it: the stored objects were
        // grouped with it, and a different target would regroup them
        // into misses. With no recorded target, 0 asks the grouping
        // step to pick one from the total C size.
        caches.groups.clear();
        if caches.persistent && front.manifest_unit_bytes != 0 {
            caches.unit_bytes = front.manifest_unit_bytes as usize;
        } else if !caches.persistent {
            caches.unit_bytes = 0;
        }
    }
    if full_walk && nonfn_changed {
        // A type or impl edit can change the C type definitions and
        // glue that every unit header carries, even in units whose fns
        // the walk will reuse. Force a fresh base: all units reassemble
        // from the preserved per-fn C, and the per-unit disk cache
        // (whose key includes the C text) serves every unit whose text
        // did not in fact change, so tcc still sees only the units
        // whose types moved.
        caches.objects = None;
    }
    // Assign slots by stable identity, append-only. New functions get new slots;
    // a removed function's slot is emptied. A known hash with a different path
    // text is a hash collision: stop with an internal error (section 1.7). The
    // same path twice is a duplicate definition, which `collect` reports.
    let mut live = vec![false; front.slot_of.len()];
    let keys = if narrow.is_some() {
        front.fn_slot.truncate(fn_count);
        for &slot in &front.fn_slot {
            if let Some(l) = live.get_mut(slot as usize) {
                *l = true;
            }
        }
        None
    } else {
        let keys = keys.expect("fn keys are made when the update is not narrow");
        let mut fn_slot = Vec::with_capacity(keys.len());
        for k in &keys {
            if let Err(c) = def::insert_path(&mut front.slot_paths, k.disk, &k.path) {
                return Err(c.to_string());
            }
            let slot = match front.slot_of.get(&k.disk) {
                Some(&slot) => slot,
                None => {
                    let slot = front.slot_of.len() as u32;
                    front.slot_of.insert(k.disk, slot);
                    slot
                }
            };
            if slot as usize >= live.len() {
                live.resize(slot as usize + 1, false);
            }
            live[slot as usize] = true;
            fn_slot.push(slot);
        }
        front.fn_slot = fn_slot;
        Some(keys)
    };
    front.ast_fn_count = front.fn_slot.len();
    let n_slots = front.slot_of.len();
    caches.ok.resize(n_slots, false);
    caches.has_out.resize(n_slots, false);
    caches.out.resize_with(n_slots, FnOut::default);
    caches.slot_reads.resize_with(n_slots, || None);
    caches.slot_ir.resize_with(n_slots, || None);
    front.slot_hash.resize(n_slots, 0);
    front.slot_head.resize(n_slots, 0);
    front.inst_slot.resize(n_slots, false);
    // Compaction remap: move each live fn's per-slot state from its
    // old slot to its new one, by stable identity.
    if let Some((old_map, mut old)) = remap {
        for (i, k) in keys.iter().flatten().enumerate() {
            let Some(&old_slot) = old_map.get(&k.disk) else { continue };
            let old_slot = old_slot as usize;
            let new_slot = front.fn_slot[i] as usize;
            if old_slot >= old.ok.len() {
                continue;
            }
            caches.ok[new_slot] = old.ok[old_slot];
            caches.has_out[new_slot] = old.has_out[old_slot];
            caches.out[new_slot] = std::mem::take(&mut old.out[old_slot]);
            caches.slot_reads[new_slot] = old.reads[old_slot].take();
            caches.slot_ir[new_slot] = old.ir[old_slot].take();
            front.slot_hash[new_slot] = old.hash[old_slot];
            front.slot_head[new_slot] = old.head[old_slot];
        }
    }
    // Every fn's head hash at this parse (see `Front::slot_head`), and
    // whether it is a const fn (its body feeds const evaluation, so a
    // body edit can move values other items baked in).
    let head_ast = &front.ast;
    let (heads, is_const): (Vec<u64>, Vec<bool>) = match narrow {
        Some(edited) => (0..fn_count)
            .map(|i| {
                let (item, sub) = front.fn_loc[i];
                let f = fn_def_at(head_ast, item, sub);
                let head = if edited.contains(&i) { super::ast_hash::fn_head_hash(head_ast, f) } else { front.slot_head[front.fn_slot[i] as usize] };
                (head, f.qual.is_const)
            })
            .unzip(),
        None => par_map(&front.fn_loc, |&(item, sub)| {
            let f = fn_def_at(head_ast, item, sub);
            (super::ast_hash::fn_head_hash(head_ast, f), f.qual.is_const)
        })
        .into_iter()
        .unzip(),
    };
    t.lap("slots: assign+heads");
    // Instance slots are not AST fns: the generic block in `compile`
    // decides after collect which are live.
    for slot in (0..n_slots).filter(|&s| !live[s] && !front.inst_slot[s]) {
        if caches.out[slot].has_code() {
            caches.wiped_slots.push(slot as u32);
        }
        caches.out[slot] = FnOut::default();
        caches.has_out[slot] = true;
        caches.ok[slot] = true;
        caches.slot_reads[slot] = None;
        caches.slot_ir[slot] = None;
        // A fn of the same identity and text can come back (an edit
        // undone, a nested fn's ordinal among same-name fns of its
        // parent moving back). It must not look unchanged and passing
        // with this empty C.
        front.slot_hash[slot] = 0;
        front.slot_head[slot] = 0;
    }
    // Re-check a function if its body changed, or it is new, or its body mentions a changed
    // function's name (only possible in the "signatures" case). A function in the last
    // group only (same body hash, last check passed, and its own signature unchanged) is a
    // reuse candidate for the read-set dirty walk after collect; its `has_out` is cleared
    // only if the walk keeps it changed, which the caller does when it stays in the work
    // set (see the walk in `compile`). A function whose own signature item changed is
    // never a candidate: its body is checked against that signature (parameter names and
    // types bind the locals, the return type coerces the tail), and the body hash does
    // not cover the signature tokens, so no recorded read set can prove the old result
    // stands. It rechecks like a body change.
    let names = changed_names.unwrap_or_default();
    // A const fn whose body hash or signature item changed: its old
    // results may sit inside const and static values, array lengths,
    // and discriminants across the crate. Collect re-evaluates those
    // items, and their new values ride in `Sig` and `Layout`
    // fingerprints; making every unchanged passing body a candidate
    // lets the dirty walk find the readers. (A brand-new const fn also
    // sets this: one needless walk, no wrong reuse.)
    // The token scan and the Ast can disagree on the fn count for
    // unusual shapes (an impl inside a body, which collect rejects
    // with its own diagnostic): pair scan index i with Ast index i
    // only where both lists have an entry, and never index past
    // either list. `collect` runs next and gives the real answer;
    // the tail's count guard catches any remaining disagreement.
    // On disagreement the const-fn question answers "may have
    // changed", so no body is reused on a guess.
    // A changed name that is a top-level fn's own (not a method's).
    let own_sig = |i: usize| match &keys {
        Some(keys) => keys[i].free && names.contains(&keys[i].name),
        None => {
            let (item, sub) = front.fn_loc[i];
            (item == usize::MAX || sub.is_none()) && names.contains(&fn_def_at(&front.ast, item, sub).name)
        }
    };
    let paired = fn_count.min(front.fn_loc.len());
    let const_fn_changed = fn_count != front.fn_loc.len()
        || (0..paired).any(|i| {
            is_const[i]
                && (front.slot_hash.get(front.fn_slot[i] as usize).copied().unwrap_or(0) != scan_of(front, i).0
                    || own_sig(i))
        });
    let mut changed = Vec::new();
    let mut mention_only = Vec::new();
    for i in 0..paired {
        let slot = front.fn_slot[i] as usize;
        let (hash, _) = scan_of(front, i);
        let idents = &front.chunks[fn_at[i].0].scan.body_idents[fn_at[i].1];
        let own_sig_changed = own_sig(i);
        let mentions = own_sig_changed || idents.iter().any(|s| names.contains(s));
        let body_same = front.slot_hash[slot] == hash;
        // A changed head (parameter names, patterns, types) always
        // rechecks the fn itself: no read set covers the bindings its
        // own head creates. The stored hash advances with the body
        // hash below, before the check runs, under the same rule.
        let head_same = front.slot_head[slot] == heads[i];
        // A body whose C names a slot that is dead now rechecks, so its
        // C is made again. Slots are append-only, so that callee lives
        // at a new slot: its stable identity moved while this caller's
        // text stayed (a nested fn whose parent is not found by span
        // keeps its body item index, which moves when an earlier body
        // gains or loses an item; see `def::nested_fn_parents`). No
        // read covers it.
        let calls_dead = caches.out[slot].used.iter().any(|&u| live.get(u as usize) == Some(&false) && !front.inst_slot[u as usize]);
        if calls_dead {
            caches.ok[slot] = false;
        }
        if (full_walk || const_fn_changed) && body_same && head_same && caches.ok[slot] {
            // Full-mode (or const-fn-edit) candidate: the body is unchanged and passed
            // before, so only its recorded reads can dirty it. It
            // stays in `changed` (the walk in `compile` removes the
            // clean ones) and keeps its passing mark and C until the
            // walk decides, exactly like a mention-only candidate.
            mention_only.push(i);
            changed.push(i);
            continue;
        }
        if !body_same || !head_same || !caches.ok[slot] || mentions {
            if body_same && head_same && caches.ok[slot] && mentions && !own_sig_changed {
                mention_only.push(i);
            } else {
                // Same rule as the bodies-only path: `slot_hash` advances
                // below before the check runs, so clear the passing mark
                // now. An early return between here and the check loop
                // (a collect error, say) then leaves the function dirty,
                // never unchanged-and-passing with an unchecked body.
                caches.ok[slot] = false;
                caches.has_out[slot] = false;
                caches.slot_reads[slot] = None;
            }
            front.slot_hash[slot] = hash;
            front.slot_head[slot] = heads[i];
            changed.push(i);
        }
    }
    t.lap(if names.is_empty() { "parse (par)" } else { "parse changed chunks" });
    Ok((changed, mention_only, const_fn_changed))
}

/// Under the oracle: why `slot_update`'s narrow form for a proven item
/// patch (the edited fns `edited`) would differ from its full form, if it
/// would: fn locations, Adt or static ids, slot keys, or another fn's
/// head moved. Reads only.
fn narrow_moved(front: &Front, crate_ids: CrateIds, edited: &[usize]) -> Option<&'static str> {
    if fn_locations(&front.ast) != front.fn_loc {
        return Some("fn locations");
    }
    let keys = fn_keys(&front.ast, &front.fn_loc, &front.interner, crate_ids.stable);
    let (adts, statics) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order, &fn_bodies(&front.ast, &front.fn_loc, &keys));
    if adts != front.prev_adt_ids || statics != front.prev_static_ids {
        return Some("def ids");
    }
    if keys.len() != front.fn_loc.len() || keys.iter().zip(&front.fn_slot).any(|(k, &s)| front.slot_of.get(&k.disk) != Some(&s)) {
        return Some("slot keys");
    }
    let head = |i: usize| {
        let (item, sub) = front.fn_loc[i];
        super::ast_hash::fn_head_hash(&front.ast, fn_def_at(&front.ast, item, sub))
    };
    if (0..front.fn_loc.len()).any(|i| !edited.contains(&i) && head(i) != front.slot_head[front.fn_slot[i] as usize]) {
        return Some("heads");
    }
    None
}

/// Function names whose signature changed, or that were added or removed, if those are the only
/// changes between two item lists. None if anything else changed.
fn fn_only_changes(old: &[scan::ItemScan], new: &[scan::ItemScan]) -> Option<Vec<Sym>> {
    let others = |items: &[scan::ItemScan]| items.iter().filter(|i| i.fn_name.is_none()).map(|i| i.hash).collect::<Vec<_>>();
    if others(old) != others(new) {
        return None;
    }
    let fns = |items: &[scan::ItemScan]| items.iter().filter_map(|i| i.fn_name.map(|n| (n, i.hash))).collect::<FxMap<Sym, u64>>();
    let (a, b) = (fns(old), fns(new));
    let mut names: Vec<Sym> = a.iter().filter(|(n, h)| b.get(*n) != Some(*h)).map(|(n, _)| *n).collect();
    names.extend(b.keys().filter(|n| !a.contains_key(*n)));
    names.sort_unstable();
    names.dedup();
    Some(names)
}

/// One function's slot key: its stable disk identity, the canonical path text
/// (for collision checks), and the two facts the changed-name scan needs.
struct FnKey {
    disk: DiskDefId,
    path: String,
    /// A top-level function (not an impl method).
    free: bool,
    name: Sym,
}

/// The slot key of every function, in LocalDefId order. Identity comes from
/// name strings through src/def.rs (free fn: its name; method: its impl's path
/// plus its name), never from `Sym` values, so keys are the same in every
/// session. An impl whose self type is not a plain path gets a placeholder
/// header; `collect` rejects it later, so its slots are never used. The hashes
/// computed here must equal the ones `collect` stores in `Program::fn_defs`;
/// a test below checks both against one source.
fn fn_keys(ast: &Ast, fn_loc: &[(usize, Option<usize>)], interner: &Interner, stable: StableCrateHash) -> Vec<FnKey> {
    // Each impl's path and its methods' (`def::impl_ids`, as `collect` computes them).
    let impl_ids = def::impl_ids(stable, ast, interner);
    let key = |hash, path, free, name| FnKey { disk: DiskDefId { krate: stable, hash }, path, free, name };
    let mut keys = par_map(fn_loc, |&(item, sub)| match (item != usize::MAX, sub) {
        (false, Some(k)) => {
            let d = match &ast.stmt_items[k].kind {
                ItemKind::Fn(d) => d,
                _ => unreachable!("fn_loc points at a function"),
            };
            // A nested fn's identity folds from its parent's, below.
            key(def::DefPathHash(0), String::new(), true, d.name)
        }
        _ => match (&ast.items[item].kind, sub) {
            (ItemKind::Fn(d), None) => {
                let (hash, path) = def::free_fn_path(stable, &[], interner.get(d.name));
                key(hash, path, true, d.name)
            }
            (ItemKind::Impl(imp), Some(k)) => {
                let (hash, path) = impl_ids[item].as_ref().unwrap().methods[k].clone();
                key(hash, path, false, imp.fns[k].name)
            }
            _ => unreachable!("fn_loc points at a function"),
        },
    });
    // Nested fns: the parent fn's identity plus the name (section 1.7),
    // exactly as `collect` folds its def ids.
    let mut nested_at: Vec<Option<usize>> = vec![None; ast.stmt_items.len()];
    let mut top_at: FxMap<crate::ast::BlockId, usize> = FxMap::default();
    for (i, &(item, sub)) in fn_loc.iter().enumerate() {
        match (item != usize::MAX, sub) {
            (false, Some(k)) => nested_at[k] = Some(i),
            _ => {
                if let Some(b) = fn_def_at(ast, item, sub).body {
                    top_at.insert(b, i);
                }
            }
        }
    }
    if nested_at.iter().any(Option::is_some) {
        // Trait default methods have no slot of their own, but parent the
        // fns nested in their bodies.
        let trait_tops: FxMap<crate::ast::BlockId, (def::DefPathHash, String)> =
            def::trait_body_paths(stable, ast, interner).into_iter().map(|(b, hash, path)| (b, (hash, path))).collect();
        let ids = def::nested_fn_ids(
            ast,
            interner,
            |b| top_at.get(&b).map(|&i| (keys[i].disk.hash, keys[i].path.clone())).or_else(|| trait_tops.get(&b).cloned()),
            |(hash, path), name, disamb| def::child_path(*hash, path, def::DefKind::Fn, name, disamb),
            |seg, name| def::free_fn_path(stable, &[seg], name),
        );
        for (k, id) in ids.into_iter().enumerate() {
            if let (Some(i), Some((hash, path))) = (nested_at[k], id) {
                keys[i].disk.hash = hash;
                keys[i].path = path;
            }
        }
    }
    keys
}

/// LocalDefId order: top-level functions and impl methods, in item order. Same as `collect`.
pub(super) fn fn_locations(ast: &Ast) -> Vec<(usize, Option<usize>)> {
    let mut out = Vec::new();
    for (i, item) in ast.items.iter().enumerate() {
        match &item.kind {
            ItemKind::Fn(_) => out.push((i, None)),
            ItemKind::Impl(imp) => out.extend((0..imp.fns.len()).map(|k| (i, Some(k)))),
            _ => {}
        }
    }
    // Nested fns follow, in stmt item order, marked with a usize::MAX item
    // index and the stmt item index as the sub index (collect's order).
    for (i, item) in ast.stmt_items.iter().enumerate() {
        if matches!(item.kind, ItemKind::Fn(_)) {
            out.push((usize::MAX, Some(i)));
        }
    }
    out
}

/// Compiles one request, reusing whatever `session` holds. The session
/// serves one `SessionKey`: a request for another key is a routing bug and
/// gets an internal error, never this session's state.

/// One std splice into a compile's source (see `splice_std`).
struct Spliced {
    /// The shipped byte ranges of the combined source, by crate.
    ranges: Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
    /// The `STD_FNS` rows the splice defines.
    routes: Vec<&'static crate::ty::lang::StdFnDef>,
    /// The byte range of the lang method chunks (`Ast::lang_methods`).
    methods: (u32, u32),
}

/// Splices the checked source std that `needs` asks for after `src`
/// (see the call site in `compile`).
fn splice_std(
    src: &mut String,
    std_cache: &mut Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    needs: crate::ty::lang::StdNeeds,
) -> Result<Spliced, Response> {
    let load = std_cache.get_or_insert_with(|| crate::stdload::load_std().map(std::sync::Arc::new)).clone();
    let load = match load {
        Ok(l) => l,
        Err(e) => return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() }),
    };
    let mut ranges = Vec::new();
    if !src.ends_with('\n') {
        src.push('\n');
    }
    let splice = match load.splice(needs) {
        Ok(s) => s,
        Err(e) => return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() }),
    };
    let mut methods = (0, 0);
    for (i, (krate, text)) in splice.blocks.iter().enumerate() {
        let lo = src.len() as u32;
        src.push_str(text);
        if !src.ends_with('\n') {
            src.push('\n');
        }
        ranges.push((lo, src.len() as u32, *krate));
        if splice.methods_block == Some(i) {
            methods = (lo, src.len() as u32);
        }
    }
    Ok(Spliced { ranges, routes: splice.routes, methods })
}

/// `StdLoad::close`, loading std only when the plan splices some.
fn close_std_plan(
    std_cache: &mut Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    user: StdPlan,
    platform: Option<StdPlan>,
) -> Result<StdPlan, Response> {
    let first = if user.platform { user.or(platform.unwrap_or_default()) } else { user };
    if !first.needs.any() {
        return Ok(first); // An empty splice asks nothing.
    }
    let load = std_cache.get_or_insert_with(|| crate::stdload::load_std().map(std::sync::Arc::new)).clone();
    load.and_then(|l| l.close(user, platform)).map_err(|e| Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() })
}

/// The resolver front end (W-RESOLVE): Cargo graph selection, the
/// outline worklist, and the session setup the shared tail consumes.
/// The worklist reruns per request (per-file caches inside it are
/// W-DRIVER phase 2 step B), but checking and codegen are incremental:
/// the merged Ast is scanned structurally (`ast_hash`), the same
/// bodies/signatures/full mode split as the single-file path picks
/// the slot update, and the shared tail's read-set dirty walk reuses
/// every body whose recorded reads still match. Returns the tail
/// tuple (map, changed, mention-only, const-fn-changed, fn count,
/// mode, fn lines, body hashes, tables).
#[allow(clippy::too_many_arguments)]
fn resolved_setup(
    req: &Request,
    front: &mut Front,
    caches: &mut Caches,
    std_cache: &mut Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    user_src: &str,
    root_lexed: Option<lexer::Lexed>,
    route_std_mods: Option<u32>,
    crate_ids_default: CrateIds,
    std_ranges: &mut Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
    std_routes: &mut Vec<&'static crate::ty::lang::StdFnDef>,
    std_methods: &mut (u32, u32),
    t: &mut Timer,
    visits: &mut Visits,
    reusable: Option<(u64, Response)>,
) -> Result<(SourceMap, Vec<usize>, Vec<usize>, bool, usize, &'static str, Vec<u32>, Vec<u64>, Option<std::sync::Arc<crate::resolve::imports::ResolvedTables>>), Response> {
    use crate::resolve::cargo::{self, GraphRequest};
    use crate::resolve::cfg::CfgEnv;
    use crate::resolve::worklist::{self, CrateInput};
    front.resolved_crate = true;
    let request_start = std::time::SystemTime::now();
    let key = &req.session;
    let code2 = |msg: String| Response { stderr: format!("error: {msg}\n"), code: 2, ..Default::default() };
    // Crate selection: through the Cargo graph when a manifest names the
    // crate, else the synthetic one-file package of the session key.
    let (root_path, mut root_text, crate_ids, env, externs, crate_name, cargo_env) = if let Some(manifest) = &key.krate.manifest_path {
        let greq = GraphRequest {
            manifest_path: manifest.clone(),
            package: None,
            features: key.features.clone(),
            default_features: key.default_features,
            all_features: key.all_features,
            target_triple: key.target_triple.clone(),
            cargo_net: key.cargo_net,
            env: req.client.env.as_deref().map(cargo::cargo_env_of),
            cache_dir: Some(crate::driver::cache::cache_dir(&key.krate.root)),
        };
        let graph = cargo::load_graph(&greq).map_err(code2)?;
        t.lap("cargo graph");
        front.display_root = Some(graph.workspace_root.clone());
        let pre_env = CfgEnv::new(&key.target_triple, &key.features, key.krate.test, key.profile);
        let mut unit =
            cargo::select_unit(&graph, &greq, &key.krate.target_kind, &key.krate.target_name, &pre_env, &front.interner, key.krate.test)
                .map_err(code2)?;
        cargo::mark_source_deps(&mut unit.deps, &key.source_deps);
        let root_text = crate::driver::read_source(&unit.target.src_path)
            .map_err(|e| code2(format!("cannot read {}: {e}", unit.target.src_path.display())))?;
        // Edition and lint gates for the selected unit (section 1.1),
        // rendered against the crate root file.
        let mut gate_map = SourceMap::default();
        gate_map.add_file_with_text(&unit.target.src_path.to_string_lossy(), &root_text);
        for check in [cargo::check_edition(&unit), cargo::check_lints(&graph, &unit)] {
            if let Err(mut d) = check {
                return Err(errors(std::slice::from_mut(&mut d), &gate_map, &root_text, req));
            }
        }
        let mut env = CfgEnv::new(&key.target_triple, &unit.features, key.krate.test, key.profile);
        // Cargo env for the selected unit plus its build script
        // outputs (section 1.1): `OUT_DIR` and `rustc-env` pairs for
        // `env!`, `rustc-cfg` values for `#[cfg]`. The script re-runs
        // through Cargo when its recorded inputs changed.
        let cache = super::cache::cache_dir(&req.file);
        let manifest_dir = unit.package.manifest_path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
        let mut cargo_env = unit.cargo_env.clone();
        let client_env = req.client.env.as_deref();
        let selected_out = super::buildscript::outputs(&manifest_dir, &cache, client_env)
            .map_err(|e| code2(format!("build script of `{}` failed: {e}", unit.package.name)))?;
        if let Some(out) = &selected_out {
            if let Some(dir) = &out.out_dir {
                cargo_env.push(("OUT_DIR".into(), dir.to_string_lossy().into_owned()));
            }
            cargo_env.extend(out.rustc_env.iter().cloned());
            for c in &out.rustc_cfg {
                env.add_rustc_cfg(c);
            }
            for c in &out.rustc_check_cfg {
                env.add_check_cfg(c);
            }
        }
        let mut deps = unit.deps.clone();
        let mut memo: FxMap<PathBuf, Option<super::buildscript::Outputs>> = FxMap::default();
        memo.insert(manifest_dir, selected_out);
        fill_dep_build_outputs(&mut deps, &cache, client_env, &mut memo).map_err(code2)?;
        t.lap("build script outputs");
        // Cargo runs rustc from the workspace root, so `file!` shows member paths relative to it.
        front.client.shown_root = Some((graph.workspace_root.clone(), PathBuf::new()));
        let ids = CrateIds {
            local: def::LOCAL_CRATE,
            stable: def::stable_crate_hash(&unit.package_id, &key.krate.target_kind, &unit.target.name, key.krate.test),
        };
        (unit.target.src_path.clone(), root_text, ids, env, deps, unit.package.name.replace('-', "_"), cargo_env)
    } else {
        front.display_root = None;
        let stem = key.krate.root.file_stem().and_then(|s| s.to_str()).unwrap_or("main").to_string();
        let env = CfgEnv::new(&key.target_triple, &key.features, key.krate.test, key.profile);
        (key.krate.root.clone(), user_src.to_string(), crate_ids_default, env, Vec::new(), stem, Vec::new())
    };
    // Body patch (driver/patch.rs): when every edit since the last full
    // resolve sits inside a fn body, edit the merged Ast in place.
    let inputs = super::patch::inputs_fingerprint(&(
        &root_path,
        crate_ids.stable,
        &env,
        &externs,
        &crate_name,
        &cargo_env,
        &front.display_root,
        &front.client.shown_root,
        key.krate.test,
    ));
    // What a later patch needs to expand a body alone. With dependencies,
    // only when none of their macros can take a builtin's name (the
    // PatchBase below asks `macro_scope::dep_macros_shut`).
    let patch_expand = (env.clone(), crate_name.clone());
    let has_deps = !externs.is_empty();
    let patched =
        if ast_bloated(front) { Err("ast compaction") } else { super::patch::try_patch(front, caches, inputs, &root_text, request_start) };
    if super::resolve_oracle::on()
        && let Ok(p) = &patched
    {
        let items = p.item_scans.as_deref().unwrap_or(&front.items);
        let reused = reusable.as_ref().filter(|_| p.files == 0).map(|r| &r.1);
        super::resolve_oracle::check_patch(front, &p.tables, items, &p.fn_lines, reused);
    }
    match patched {
        // Nothing changed since the last check of this same request:
        // its answer stands (`check_fingerprint`).
        Ok(p) if p.files == 0 && reusable.is_some() => {
            let (fp, mut resp) = reusable.unwrap();
            front.last_check = Some((fp, resp.clone()));
            front.last_visits.clear();
            Visits { path: "reuse", ..Default::default() }.render(&mut front.last_visits);
            log_visits(&front.last_visits);
            if stats_on() {
                Stats { mode: "reuse", fns: p.fn_count, ..Default::default() }.render(&mut resp.stderr);
                resp.stderr.push_str(&front.last_visits);
            }
            if req.timings {
                t.lap("reuse last answer");
                let _ = writeln!(resp.stderr, "lust check {}: ok (no change since the last check)", req.file.to_string_lossy());
                t.render(&mut resp.stderr);
            }
            return Err(resp);
        }
        // An item patch (sigedit P1.3): the new item scans take the
        // resolve path's slot update, in signatures mode with the edited
        // fns' names, and the tail collects.
        Ok(mut p) if p.item_scans.is_some() => {
            *std_ranges = std::mem::take(&mut p.std_ranges);
            *std_routes = std::mem::take(&mut p.std_routes);
            *std_methods = p.std_methods;
            front.resolved_crate_ids = Some(crate_ids);
            let (files, nodes, spans, scanned, slot_fns, reads) = (p.files, p.nodes, p.spans, p.bodies, p.fn_count, p.reads);
            *visits = Visits { path: "item", files, nodes, spans, scanned, slot_fns, reads, ..Default::default() };
            t.lap("item patch");
            let scans = p.item_scans.take().unwrap_or_default();
            let env = scan::env_hash(scans.iter());
            let mut names = std::mem::take(&mut p.item_names);
            names.sort_unstable();
            names.dedup();
            let fn_at: Vec<(usize, usize)> = (0..p.fn_count).map(|i| (0, i)).collect();
            let (hashes, lines) = (p.body_hashes.clone(), p.fn_lines.clone());
            let scan_of = |_: &Front, i: usize| (hashes[i], lines[i]);
            // A derive list edit (any body may read the derives) or a trait
            // impl method edit (callers need not name it): full mode.
            let names = (!p.item_full).then_some(names);
            let mode = if p.item_full { "full" } else { "signatures" };
            caches.derive_only = p.derive_only;
            let narrow = (!p.item_full).then_some(&p.item_fns[..]);
            let slots = slot_update(front, caches, scans, env, names, &fn_at, crate_ids, &scan_of, t, narrow);
            let (changed, mention_only, const_fn) = match slots {
                Ok(c) => c,
                Err(e) => {
                    front.env_hash = None;
                    return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() });
                }
            };
            return Ok((p.map, changed, mention_only, const_fn, p.fn_count, mode, p.fn_lines, p.body_hashes, Some(p.tables)));
        }
        Ok(p) => {
            (*std_ranges, *std_routes, *std_methods) = (p.std_ranges, p.std_routes, p.std_methods);
            front.resolved_crate_ids = Some(crate_ids);
            *visits = Visits {
                path: "patch",
                files: p.files,
                nodes: p.nodes,
                spans: p.spans,
                scanned: p.bodies,
                slot_fns: p.fn_count,
                reads: p.reads,
                ..Default::default()
            };
            t.lap("body patch");
            // A const fn body edit that a const evaluation may run: as
            // `slot_update` with `const_fn_changed`, every unchanged
            // passing body joins as a read-set candidate. One no
            // evaluation can run (`const_reach.rs`) is a plain body edit,
            // unless a stored check ran it anyway (a `Checked` read: a
            // `thread_local!` const initializer). One only const and
            // static values read is a plain body edit once their values
            // hold (`revalue_consts`, after the kept program).
            let (mut changed, mut mention_only, mut const_fn) = (p.changed, Vec::new(), p.const_fn);
            if !const_fn && !p.const_edits.is_empty() {
                let defs = local_def_ids(front, &p.const_edits);
                let read = |r: &Option<crate::driver::graph::Reads>| {
                    r.as_ref().is_some_and(|r| defs.iter().any(|&d| r.contains(&caches.read_keys, &crate::driver::graph::ReadKey::Checked(d))))
                };
                const_fn = caches.slot_reads.iter().any(read) || caches.gen_reuse.reads_checked(&defs);
            }
            front.revalue_consts = p.revalue && !const_fn;
            if const_fn {
                mention_only = (0..p.fn_count).filter(|&i| caches.ok[front.fn_slot[i] as usize] && !changed.contains(&i)).collect();
                changed.extend_from_slice(&mention_only);
                changed.sort_unstable();
            }
            return Ok((p.map, changed, mention_only, const_fn, p.fn_count, "bodies", p.fn_lines, p.body_hashes, Some(p.tables)));
        }
        Err(why) => visits.why = why,
    }
    // Std splice, in the root file text, exactly as the single-file path
    // (user spans do not move), and the std platform crate: both by the
    // std plan (`StdPlan`). The first pass takes the session's last plan
    // (a daemon request) or a guess from the module files of the root
    // and of every source dependency (a new session); another pass runs
    // only when the plan of the files the pass saw differs.
    let unspliced_root = std::mem::take(&mut root_text);
    // A single-file root is the routed text: routing scanned it for std
    // source modules already.
    let root_needs = match route_std_mods {
        Some(m) if key.krate.manifest_path.is_none() => crate::ty::lang::std_needs_known(&unspliced_root, m),
        _ => crate::ty::lang::std_needs(&unspliced_root),
    };
    let root_asks = StdPlan { needs: root_needs, platform: crate::resolve::worklist::mentions_std_platform(&unspliced_root) };
    let mut plan = match front.std_plan {
        Some(p) => p,
        None => {
            let mut user = StdPlan::guess_crate(&root_path, &unspliced_root, root_asks);
            for dep in crate::resolve::worklist::dep_roots(&externs) {
                if let Ok(text) = std::fs::read_to_string(&dep) {
                    user = user.or(StdPlan::guess_crate(&dep, &text, StdPlan::asks(&text)));
                }
            }
            let plan = close_std_plan(std_cache, user, user.platform.then(crate::stdload::guess_platform))?;
            t.lap("std plan guess");
            plan
        }
    };
    let mut root_lexed = root_lexed;
    let mut passes = 0;
    let mut oracle_input = None;
    let resolved = loop {
        passes += 1;
        root_text.clone_from(&unspliced_root);
        if plan.needs.any() {
            let sp = splice_std(&mut root_text, std_cache, plan.needs)?;
            (*std_ranges, *std_routes, *std_methods) = (sp.ranges, sp.routes, sp.methods);
        } else {
            (*std_ranges, *std_routes, *std_methods) = (Vec::new(), Vec::new(), (0, 0));
        }
        t.lap("std load+splice");
        // Routing lexed the single-file root already: hand its tokens to
        // discovery, unless a std splice changed the text.
        if !plan.needs.any()
            && key.krate.manifest_path.is_none()
            && let Some(lexed) = root_lexed.take()
        {
            front.resolve_cache.seed_root(&root_path, &root_text, lexed);
        }
        let input = CrateInput {
            root_path: root_path.clone(),
            root_text: root_text.clone(),
            env: env.clone(),
            crate_ids,
            crate_name: crate_name.clone(),
            cargo_env: cargo_env.clone(),
            deps: externs.clone(),
            client: front.client.clone(),
            std_splice_lo: std_ranges.first().map(|r| r.0),
            display_root: front.display_root.clone(),
        };
        // The cache's final chunks are parts of the session's merged Ast: the resolve takes
        // its hits out of it, and lets go of it before any patch writes it.
        front.resolve_cache.set_merged(front.ast.clone(), front.ast_gen);
        let out = worklist::resolve_crate_with(&input, &front.interner, &front.known, &mut front.resolve_cache, plan.platform);
        front.resolve_cache.clear_merged();
        if super::item_oracle::on() || super::resolve_oracle::on() {
            oracle_input = Some(super::item_oracle::ColdInput { input: input.clone(), platform: plan.platform });
        }
        let (user, platform) = match &out {
            Ok(r) => (r.std_asks, r.platform_asks),
            Err(e) => (e.std_asks, e.platform_asks),
        };
        let seen = close_std_plan(std_cache, user, platform)?;
        // Each pass's plan is the same function of the same user files,
        // so the second pass agrees; the cap only guards a broken rule.
        if seen == plan || passes == 3 {
            front.std_plan = Some(seen);
            break out;
        }
        plan = seen;
        t.lap("resolve: std plan retry");
    };
    if super::resolve_oracle::on()
        && caches.persistent
        && let Some(cold_in) = &oracle_input
    {
        super::resolve_oracle::check_full(front, cold_in, &resolved, visits.why);
    }
    let resolved = match resolved {
        Ok(r) => r,
        Err(e) => {
            let mut diags = e.diags;
            return Err(errors(&mut diags, &e.map, &e.all_text, req));
        }
    };
    let worklist::ResolvedCrate {
        ast, map, tables, fn_lines, body_hashes: _, structure_hash, expand_deps, timings: resolve_timings, scans, mdr, generation, ..
    } =
        resolved;
    // B3 step 2 (`LUST_B3_OBSERVE=1`): what a warm resolve would have had to
    // redo since the last full resolve (resolve/mdr.rs).
    if let Some(m) = mdr {
        if let Some(prev) = &front.mdr {
            eprintln!("{}", crate::resolve::mdr::observe(prev, &m).line());
        }
        front.mdr = Some(m);
    }
    t.lap_parts(resolve_timings, "resolve: other");
    let fn_count = fn_lines.len();
    // Dropping the previous merged Ast walks every node string and
    // Vec; at crate scale that is milliseconds on the request path.
    // A large old Ast drops on a side thread in a daemon session. A
    // one-shot session drops it here: its process may fork for an
    // in-memory run, and no other thread may live at the fork (tcc.rs).
    // The patch base and a kept program describe the Ast being replaced.
    // (A resolve error above leaves them in place, so the request after
    // it can patch.)
    front.patch = None;
    let old_kept = std::mem::take(&mut front.kept);
    let old_ast = std::mem::replace(&mut front.ast, Arc::new(ast));
    front.ast_gen = generation;
    front.fresh_exprs = front.ast.exprs.len();
    if (old_ast.exprs.len() > 20_000 || old_kept.iter().any(Option::is_some)) && caches.persistent {
        // Nested token trees in the Ast drop recursively; use the
        // compiler stack size like every other compiler thread.
        crate::pool::drop_detached("lust-drop", (old_ast, old_kept));
    }
    front.map = map.clone();
    front.src.clone_from(&root_text);
    front.resolved_crate_ids = Some(crate_ids);
    // Structural scan of the merged Ast, assembled by the worklist
    // from per-file chunk scans (real per-item hashes without
    // bodies, per-fn body hashes, and body identifier sets). The
    // worklist's module/import structure hash rides in as one extra
    // non-fn item scan at the end: flattening dropped the `mod` and
    // `use` items from the Ast, so without it an import-only edit
    // would look like a body-only edit (or no edit at all).
    if scans.bodies.len() != fn_count {
        // The worklist and the Ast scan disagree on the fn list: an
        // internal error, never a guess at reuse.
        front.env_hash = None;
        return Err(Response { stderr: "error: internal: resolver function count mismatch; run again\n".into(), code: 3, ..Default::default() });
    }
    // Each fn's own text joins its structural body hash, for the
    // same reason as `fold_fn_text` on the chunk path: the structural
    // hash has no positions, and a reused body's C embeds them. On the
    // pool: every fn's text is hashed (28 MB on tsgo).
    let fn_at: Vec<((usize, Option<usize>), u64, u32)> =
        fn_locations(&front.ast).into_iter().zip(&scans.bodies).zip(&fn_lines).map(|((at, b), &line)| (at, b.0, line)).collect();
    let body_hashes: Vec<u64> = par_map(&fn_at, |&((item, sub), body, line)| fn_text_hash(&front.ast, &map, fn_def_at(&front.ast, item, sub), line, body));
    let mut item_scans = scans.items;
    item_scans.push(scan::ItemScan { hash: structure_hash, fn_name: None });
    t.lap("ast scan");
    // One synthetic chunk: the tail's slot update reads body idents
    // from chunk scans; per-fn hashes and lines ride in through
    // `scan_of` below. Its token list stays empty: only the chunk path
    // reads chunk tokens, and a route change to that path drops these
    // chunks first. (Lexing the root again here cost a full serial lex.)
    let n_items = front.ast.items.len();
    let n_stmt_items = front.ast.stmt_items.len();
    let n_inner_attrs = front.ast.inner_attrs.len();
    front.chunks = vec![Chunk {
        start: 0,
        text: root_text,
        lexed: lexer::Lexed { tokens: Vec::new(), strings: Vec::new() },
        lexed_start: 0,
        scan: scan::ChunkScan {
            fns: body_hashes.iter().map(|&body_hash| scan::FnScan { body_hash, nested: false, fn_offset: 0, body: 0..0 }).collect(),
            items: item_scans.clone(),
            body_idents: scans.bodies.into_iter().map(|b| b.1).collect(),
            ends_at_boundary: true,
        },
        items: Some(0..n_items),
        stmt_items: Some(0..n_stmt_items),
        inner_attrs: Some(0..n_inner_attrs),
        expand_deps,
        inner_attr: false,
    }];
    let env = scan::env_hash(item_scans.iter());
    // The same mode split as the single-file path. Bodies mode goes
    // through `slot_update` with no changed names to name: a changed
    // body hash (or a fn whose last check failed) is exactly its
    // recheck rule, and the Ast is already freshly parsed here.
    let bodies_only = front.env_hash == Some(env) && front.ast_fn_count == fn_count;
    let changed_names = if bodies_only {
        Some(Vec::new())
    } else if front.env_hash.is_none() {
        None
    } else {
        fn_only_changes(&front.items, &item_scans)
    };
    let mode = if bodies_only {
        "bodies"
    } else if changed_names.is_some() {
        "signatures"
    } else {
        "full"
    };
    let fn_at: Vec<(usize, usize)> = (0..fn_count).map(|i| (0, i)).collect();
    let lines = fn_lines.clone();
    let hashes = body_hashes.clone();
    let scan_of = |_: &Front, i: usize| (hashes[i], lines[i]);
    let (changed, mention_only, const_fn_changed) =
        match slot_update(front, caches, item_scans, env, changed_names, &fn_at, crate_ids, &scan_of, t, None) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() });
            }
        };
    // Collect reads the splice ranges from the tables before it sets
    // `Program::shipped_ranges` (generic std bodies check in collect).
    let mut tables = tables;
    tables.std_ranges = std_ranges.clone();
    let tables = std::sync::Arc::new(tables);
    *visits = Visits {
        path: "resolve",
        why: visits.why,
        files: map.file_count(),
        nodes: ast_nodes(&front.ast),
        scanned: front.ast.items.len(),
        slot_fns: fn_count,
        ..Default::default()
    };
    if caches.persistent {
        // With no dependency, any user macro named like a builtin (or a
        // rename to one) in any file refuses (patch.rs `shadows_builtin`).
        // With dependencies, each source crate whose own scan passes may
        // expand its bodies alone, under its own cfg (`dep_macros_shut`).
        let shut: Vec<crate::ty::defs::ModuleId> = match has_deps {
            true => dep_macros_shut(front, &tables, &unspliced_root),
            false => {
                let texts = (1..front.map.file_count()).filter_map(|k| front.map.text(FileId(k as u32)));
                let texts: Vec<&str> = std::iter::once(unspliced_root.as_str()).chain(texts).collect();
                let ok = !texts.iter().any(|t| t.contains("macro_rules")) || !texts.iter().any(|t| super::patch::shadows_builtin(t));
                if ok { vec![crate::ty::defs::ModuleId(0)] } else { Vec::new() }
            }
        };
        let patch_expand: FxMap<_, _> = shut
            .into_iter()
            .filter_map(|r| match r.0 {
                0 => Some((r, patch_expand.clone())),
                _ => tables.crate_cfgs.get(&r).map(|c| (r, c.clone())),
            })
            .collect();
        // The span probe and the const reach serve the next request's patch: a
        // one-shot image build leaves them to that patch (patch.rs makes both
        // when it needs them), since the next build may never patch.
        let eager = !caches.image_one_shot;
        let reach = eager.then(|| super::const_reach::ConstReach::build(front));
        front.patch = Some(super::patch::PatchBase::new(
            front,
            inputs,
            unspliced_root,
            !std_ranges.is_empty(),
            tables.clone(),
            (&std_ranges[..], &std_routes[..], *std_methods),
            fn_lines.clone(),
            body_hashes.clone(),
            request_start,
            patch_expand,
        ));
        if let Some(b) = front.patch.as_mut() {
            b.oracle_input = oracle_input;
            // The span probe of a crate with macros or includes, here where
            // the new Ast is not shared yet, and the const reach, not on the
            // first patch (ts_goport: about 60 and 24 ms of the first header
            // edit after a full resolve). Later patches update the reach.
            if eager && let Some(ast) = Arc::get_mut(&mut front.ast) {
                b.probe(ast, front.map.file_count());
            }
            b.reach = reach;
        }
    }
    t.lap("patch base");
    Ok((map, changed, mention_only, const_fn_changed, fn_count, mode, fn_lines, body_hashes, Some(tables)))
}

/// Source file `p` as a binary's panic locations name it (the location unit): lust's own
/// library files (adapter and shim crates, the std platform crate) as `library/<path>`, as
/// lust's messages name them, so a binary does not depend on where lust is installed; under
/// Cargo, relative to the workspace root, as rustc prints it; else as the user typed the root
/// path (`client_view`).
fn location_path(p: &str, library: &Path, display_root: Option<&Path>, client: &expand::ClientView) -> String {
    if let Ok(rel) = Path::new(p).strip_prefix(library) {
        return format!("library/{}", rel.to_string_lossy());
    }
    match display_root.and_then(|r| Path::new(p).strip_prefix(r).ok()) {
        Some(rel) => rel.to_string_lossy().into_owned(),
        None => client.shown(p),
    }
}

pub fn compile(req: &Request, session: &mut Session) -> Response {
    let mut t = Timer::new();
    crate::driver::cache::begin_build(&req.file);
    if req.session != session.key {
        return Response {
            stderr: format!(
                "error: internal: request routed to the wrong session\n  request: {}\n  session: {}\n",
                req.session.describe(),
                session.key.describe()
            ),
            code: 3,
            ..Default::default()
        };
    }
    // A lib target has no `main` to link and lust has no rlib format: `check --lib` works,
    // `build`/`run --lib` is a clear error (Cargo release builds still build libs).
    if req.session.krate.target_kind == "lib" && !req.harness && !matches!(req.cmd, crate::protocol::Cmd::Check) {
        return Response {
            stderr: "error: lust builds bin targets only: use `lust check --lib` for a lib target\n".into(),
            code: 1,
            ..Default::default()
        };
    }
    // Lust links for the host target only (tcc). A named non-host triple
    // is a clear error for a link, not a host binary under a foreign
    // name. A check may name a release triple
    // (cfg::CfgEnv::is_release_target): its full cfg table matches
    // rustc, so the check sees the same code rustc would for that
    // target. A build that only emits C (`--emit-c`) may also use a
    // foreign triple: the C then builds with an external compiler
    // (the release cross path; rel-win owns the windows-gnu runtime).
    let triple = &req.session.target_triple;
    let foreign = !triple.is_empty() && triple != crate::protocol::host_triple();
    let foreign_check = matches!(req.cmd, crate::protocol::Cmd::Check) && crate::resolve::cfg::CfgEnv::is_release_target(triple);
    // A release-driver build (cc backend) may name a release triple (or
    // the host): its C goes to the cross compiler, never to tcc. A plain
    // `--emit-c` build may also use a foreign triple (the C is the
    // product; no link runs).
    let cc_build = req.cc && (triple.is_empty() || crate::resolve::cfg::CfgEnv::is_release_target(triple));
    if foreign && !foreign_check && !cc_build && req.emit_c.is_none() {
        return Response {
            stderr: format!(
                "error: unsupported target `{triple}`: lust builds for the host target `{}` today\n",
                crate::protocol::host_triple()
            ),
            code: 2,
            ..Default::default()
        };
    }
    let path = req.file.to_string_lossy().to_string();
    let mut src = match crate::driver::read_source(&req.file) {
        Ok(s) => s,
        Err(e) => return Response { stderr: format!("error: cannot read {path}: {e}\n"), code: 2, ..Default::default() },
    };
    // The crate identity for stable defs comes from the session's key (its
    // package and target identity, `Session::crate_ids`). For a single-file
    // program that is the synthetic one-file bin crate, as before.
    let crate_ids = session.crate_ids();
    // Open the disk cache once per session and seed slot assignment from
    // the stored manifest, so a restarted daemon gives every fn the slot
    // it had before, in any load or discovery order (sections 4.2, 8.4).
    if !session.cache_tried {
        session.cache_tried = true;
        session.disk_cache = crate::driver::cache::Cache::open(&req.file);
        if session.front.slot_of.is_empty()
            && let Some(cache) = &session.disk_cache
            && let Some((manifest, unit_bytes)) = cache.load_slot_manifest(&session.key)
        {
            session.front.slot_manifest_stored = manifest.len();
            session.front.slot_of = manifest;
            session.front.manifest_unit_bytes = unit_bytes;
            // A restarted daemon groups fns into units with the same
            // byte target as the daemon that stored the disk objects,
            // or every unit key moves and the objects orphan. A one-shot
            // session keeps its own grouping and only preserves
            // the recorded value across its stores.
            if session.caches.persistent && unit_bytes != 0 {
                session.caches.unit_bytes = unit_bytes as usize;
            }
        }
        if session.front.def_order.adts.is_empty()
            && session.front.def_order.statics.is_empty()
            && let Some(cache) = &session.disk_cache
            && let Some(order) = cache.load_def_order(&session.key, crate_ids.stable)
        {
            session.front.def_order_stored = def_order_size(&order);
            session.front.def_order = order;
            session.front.def_order_loaded = true;
        }
    }
    let session_key = session.key.clone();
    session.front.client = client_view(req);
    let Session { front, caches, std_cache, disk_cache, .. } = session;
    // The last check's answer, kept only for this same request (a no-op
    // check reuses it on the resolver path; anything else recomputes).
    let check_fp = check_fingerprint(req);
    let reusable = front.last_check.take().filter(|(fp, _)| Some(*fp) == check_fp);
    t.lap("read");

    // Resolver routing (W-RESOLVE): a manifest-selected crate, or a root
    // file that mentions modules, imports, cfg, or const/static/type
    // items, compiles through the outline worklist. Routing follows the current text, never just the
    // session's past: a fresh session routes by these same two facts, so
    // a warm session that stayed on the worklist after an edit removed
    // the trigger would answer through a different front end than a cold
    // compile for the same bytes (the two front ends order expansion and
    // parse errors differently; fuzz realish seed 107, iter 585). When
    // the route falls back, drop the resolver-built front state (merged
    // AST, synthetic chunk, spliced source): the chunk path must never
    // reuse it, and with `env_hash` cleared the request rebuilds in full
    // mode, which resets the caches in `slot_update`.
    // A std source module splices as an inline `mod` (src/stdmods.rs),
    // which only the resolver front end understands (W-STD-C). Routing
    // finds that word scan in its own parallel pass.
    let (wants_resolver, std_mods, root_lexed) = if req.session.krate.manifest_path.is_some() {
        (true, 0, None)
    } else {
        crate::resolve::worklist::route_root_std(&src, &front.interner, true)
    };
    let wants_resolver = wants_resolver || std_mods != 0;
    let route_std_mods = req.session.krate.manifest_path.is_none().then_some(std_mods);
    if front.resolved_crate && !wants_resolver {
        front.ast = Arc::default();
        front.ast_gen = 0;
        front.env_hash = None;
        front.walk_after_reject = false;
        front.walk_pending.clear();
        front.const_fn_pending = false;
        front.prev_adt_ids.clear();
        front.prev_static_ids.clear();
        front.prev_static_defs = None;
        front.items.clear();
        front.fn_loc.clear();
        front.fn_slot.clear();
        front.slot_hash.clear();
        front.slot_head.clear();
        front.ast_fn_count = 0;
        front.chunks.clear();
        front.src.clear();
        front.map = SourceMap::default();
        front.resolved_crate = false;
        front.resolved_crate_ids = None;
        front.patch = None;
    }
    let use_resolver = front.resolved_crate || wants_resolver;
    // The chunk path edits the Ast in place and never reuses a kept
    // program (only the body patch does).
    if !use_resolver {
        super::patch::drop_kept(front, caches);
    }
    t.lap("route");
    let mut visits = Visits { path: "chunks", files: 1, ..Default::default() };

    // Source std (S5): if this file can mention a source std fn, load the
    // checked shipped library (once per session) and splice its fns after
    // the user text. User spans do not move. `std_ranges` records which
    // byte ranges of the combined source belong to which shipped crate;
    // intrinsic privilege keys on them after collect. A file that cannot
    // mention a source std fn pays one byte scan and nothing else.
    let mut std_ranges: Vec<(u32, u32, crate::ty::lang::ShippedCrate)> = Vec::new();
    let mut std_routes: Vec<&'static crate::ty::lang::StdFnDef> = Vec::new();
    let mut std_methods = (0u32, 0u32);
    // Off the resolver only: the resolver path scans its own root text.
    // Routing found `stdmods::needs` already (false off the resolver).
    let needs = if use_resolver { crate::ty::lang::StdNeeds::default() } else { crate::ty::lang::std_needs_known(&src, std_mods) };
    if needs.any() {
        match splice_std(&mut src, std_cache, needs) {
            Ok(sp) => (std_ranges, std_routes, std_methods) = (sp.ranges, sp.routes, sp.methods),
            Err(resp) => return resp,
        }
        t.lap("std load+splice");
    }

    // Both front ends produce the same locals for the shared tail.
    let (map, mut changed, mut mention_only, mut const_fn_changed, fn_count, mode, fn_lines_all, body_hashes_all, resolved_tables) = if use_resolver {
        match resolved_setup(req, front, caches, std_cache, &src, root_lexed, route_std_mods, crate_ids, &mut std_ranges, &mut std_routes, &mut std_methods, &mut t, &mut visits, reusable) {
            Ok(x) => x,
            Err(resp) => return resp,
        }
    } else {
    // Lex and scan in chunks of whole items, in parallel. Only the region an edit touched is
    // split and lexed again: chunks entirely before it are kept as they are, and chunks entirely
    // after it are kept with shifted offsets.
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    // On the first compile the mask needs the item header table, and so does the split below
    // (the region is then the whole source). Compute it once. It cost a full serial source
    // scan, about 2 ms on a 48k-line file (front-end probe, milestone 2).
    let mut fresh_headers: Option<Vec<(usize, u64)>> = None;
    let mask = match front.split_mask {
        Some(m) => m,
        None => {
            let headers = item_headers(&src);
            // A file with macro definitions lexes as one chunk for now:
            // expansion is per chunk, and a def must be in the chunk that
            // uses it until the 6.1 worklist owns crate-level expansion.
            let m = if src.contains("macro_rules") { (1 << 24) - 1 } else { split_mask(src.len(), headers.len(), cores) };
            fresh_headers = Some(headers);
            front.split_mask = Some(m);
            m
        }
    };
    let old_len = front.src.len();
    let (prefix, suffix) = common_ends(front.src.as_bytes(), src.as_bytes());
    let delta = src.len() as i64 - old_len as i64;
    // A chunk whose expansion read a file or env value that has since
    // changed expands differently now, so no chunk is reused this
    // request (expansion is per chunk, but a changed include can hold
    // macro definitions other chunks used; dropping all is the simple
    // sound rule). Added for W-MACRO (docs/ARCH.md section 6.4).
    // Same for a chunk whose expansion baked in a position (`line!`):
    // reused at a different start line its baked values are wrong.
    let line_of = |text: &str, at: usize| text.as_bytes()[..at.min(text.len())].iter().filter(|&&b| b == b'\n').count();
    let pos_stale = front.chunks.iter().any(|c| {
        if !c.expand_deps.contains(&expand::Dep::Position) {
            return false;
        }
        if c.start + c.text.len() <= prefix {
            false
        } else if c.start >= old_len - suffix && suffix > 0 {
            line_of(&front.src, c.start) != line_of(&src, (c.start as i64 + delta) as usize)
        } else {
            false
        }
    });
    let deps_stale = pos_stale || front.chunks.iter().any(|c| expand::deps_stale(&c.expand_deps, &front.client));
    let mut kept_front = Vec::new();
    let mut kept_back = Vec::new();
    for c in std::mem::take(&mut front.chunks) {
        if deps_stale {
            continue;
        }
        if c.start + c.text.len() <= prefix {
            kept_front.push(c);
        } else if c.start >= old_len - suffix && suffix > 0 {
            kept_back.push(c);
        }
    }
    // A kept chunk holds expanded tokens, and expansion can read more
    // than the chunk text: token positions and included files. A chunk
    // that reads included files is never kept. A position-sensitive
    // back chunk that moved is not kept either; front chunks sit at
    // their old offsets, where their positions still hold. Keep the
    // lists a prefix and a suffix, as the boundary proof below needs.
    if let Some(i) = kept_front.iter().position(chunk_reads_files) {
        kept_front.truncate(i);
    }
    if let Some(i) = kept_back.iter().rposition(|c| chunk_reads_files(c) || (delta != 0 && chunk_pos_sensitive(c))) {
        kept_back.drain(..=i);
    }
    // A chunk may be reused only if its edges are still top-level item boundaries in the new
    // text: `chunk_end_ok` proves the end edge (complete items, clean lex state). A chunk that
    // ended at the old end of file may end mid-item (a half-written `fn added`) or inside a
    // `//` comment, and then it must not be kept in front of other text. It may still be kept
    // when it reaches the new end of file, where a cold compile scans it the same way. Cut the
    // kept front list at the first chunk that fails the test.
    if let Some(i) = kept_front.iter().position(|c| !chunk_end_ok(c)) {
        let end = kept_front[i].start + kept_front[i].text.len();
        if end < src.len() {
            kept_front.truncate(i);
        }
    }
    // The same test between kept back chunks: if a non-final back chunk does not end at an item
    // boundary, the next back chunk does not start at one. Drop everything up to it.
    while let Some(i) = (0..kept_back.len().saturating_sub(1)).find(|&i| !chunk_end_ok(&kept_back[i])) {
        kept_back.drain(..=i);
    }
    let region_start = kept_front.last().map_or(0, |c| c.start + c.text.len());
    // Prove the changed region's split points, and that the first kept back chunk still starts
    // at a top-level boundary. If the region does not end clean (an inserted `/*` or `"`, a
    // deleted brace), or does not end at a line start (its last token could merge with the back
    // chunk's first token), the back chunk starts inside a comment, string, item, or token:
    // drop it into the region and keep scanning.
    let mut boundaries: Vec<usize> = vec![region_start];
    let mut bscan = BoundaryScan::new();
    let mut scanned_to = region_start;
    let (region_end_old, region_end) = loop {
        let end_old = kept_back.first().map_or(old_len, |c| c.start);
        let end = (end_old as i64 + delta) as usize;
        if end > scanned_to {
            bscan.feed(&src.as_bytes()[scanned_to..end], scanned_to, Some(&mut boundaries));
            scanned_to = end;
        }
        let at_line_start = end == region_start || src.as_bytes()[end - 1] == b'\n';
        if (bscan.clean() && at_line_start) || kept_back.is_empty() {
            break (end_old, end);
        }
        kept_back.remove(0);
    };
    // The source map for this request: the session's one file under the request's path,
    // its line index spliced from the last request's index when there is one.
    let mut map = front.map.clone();
    if map.is_empty() {
        map.add_file(&path, &src);
    } else {
        let lines =
            if old_len == 0 { LineIndex::new(&src) } else { map.lines(ROOT_FILE).splice(&src, region_start, region_end_old, region_end) };
        map.set_file(ROOT_FILE, &path, lines, &src);
    }
    let mut ranges: Vec<(usize, usize)> = kept_front.iter().map(|c| (c.start, c.start + c.text.len())).collect();
    let headers = if region_start == 0 && region_end == src.len() { fresh_headers.as_deref() } else { None };
    let middle =
        if region_start < region_end { split_items(&src, region_start..region_end, mask, headers, &boundaries) } else { Vec::new() };
    ranges.extend(middle.iter().copied());
    ranges.extend(kept_back.iter().map(|c| ((c.start as i64 + delta) as usize, (c.start as i64 + delta) as usize + c.text.len())));
    let mut reused: Vec<Option<Chunk>> =
        kept_front.into_iter().map(Some).chain(middle.iter().map(|_| None)).chain(kept_back.into_iter().map(Some)).collect();
    let need: Vec<usize> = (0..ranges.len()).filter(|&i| reused[i].is_none()).collect();
    let test_mode = req.harness || req.session.krate.test;
    let fresh = par_map(&need, |&i| {
        let (a, b) = ranges[i];
        lexer::lex(&src[a..b], ROOT_FILE, a as u32, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode, req.session.profile, &req.session)).map(
            |(l, deps)| {
                let mut sc = scan::scan(&l);
                fold_fn_text(&mut sc, &l, &src);
                let inner_attr = has_inner_attr(&l);
                (l, sc, deps, inner_attr)
            },
        )
    });
    // A macro error in a chunk is the answer, not a lexing fallback.
    if let Some(Err(d)) = fresh.iter().find(|l| matches!(l, Err(d) if d.code.starts_with("L08"))) {
        let mut d = d.clone();
        return errors(std::slice::from_mut(&mut d), &map, &src, req);
    }
    let split_inner_attr = ranges.len() > 1
        && (reused.iter().flatten().any(|c| c.inner_attr) || fresh.iter().flatten().any(|&(_, _, _, inner_attr)| inner_attr));
    // An unbalanced chunk parsed alone fails at its own first bad token; the whole file
    // (as a cold compile sees it) reports the delimiter first, before macro errors elsewhere.
    let unbalanced = ranges.len() > 1 && fresh.iter().flatten().any(|(l, ..)| expand::delimiter_error(&l.tokens).is_some());
    // Per chunk of this request, true when its text was lexed fresh, and
    // the old bytes whose items the fresh chunks replace.
    let mut fresh_chunks: Vec<bool> = Vec::with_capacity(ranges.len());
    let mut replaced_old = (region_start, region_end_old);
    if split_inner_attr || unbalanced || fresh.iter().any(|l| l.is_err()) {
        // A chunk cut a comment or string the scanner did not see, or the text is bad, or the
        // file has an inner attribute (`has_inner_attr`): lex the whole file. Its error is the
        // answer; if it lexes, compile as one chunk. Never panic.
        match lexer::lex(&src, ROOT_FILE, 0, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode, req.session.profile, &req.session)) {
            Err(mut d) => return errors(std::slice::from_mut(&mut d), &map, &src, req),
            Ok((whole, deps)) => {
                let mut sc = scan::scan(&whole);
                fold_fn_text(&mut sc, &whole, &src);
                let inner_attr = has_inner_attr(&whole);
                fresh_chunks.push(true);
                replaced_old = (0, old_len);
                front.chunks = vec![Chunk {
                    start: 0,
                    text: src.clone(),
                    lexed: whole,
                    lexed_start: 0,
                    scan: sc,
                    items: None,
                    stmt_items: None,
                    inner_attrs: None,
                    expand_deps: deps,
                    inner_attr,
                }];
            }
        }
    } else {
        let mut fresh = need.iter().zip(fresh).map(|(&i, r)| (i, r.unwrap())).collect::<Vec<_>>().into_iter();
        let mut next_fresh = fresh.next();
        for (i, &(a, b)) in ranges.iter().enumerate() {
            fresh_chunks.push(reused[i].is_none());
            let chunk = match reused[i].take() {
                Some(mut c) => {
                    // Same text at a new position, and the edges are proven boundaries, so the
                    // tokens are the same: shift their spans and the function offsets.
                    let delta = a as i64 - c.start as i64;
                    if delta != 0 {
                        for f in &mut c.scan.fns {
                            f.fn_offset = (f.fn_offset as i64 + delta) as u32;
                        }
                        for t in &mut c.lexed.tokens {
                            t.span = t.span.shifted(delta);
                        }
                        c.lexed_start = a;
                    }
                    c.start = a;
                    c
                }
                None => {
                    let (_, (lexed, sc, deps, inner_attr)) = next_fresh.take().unwrap();
                    next_fresh = fresh.next();
                    Chunk { start: a, text: src[a..b].to_string(), lexed, lexed_start: a, scan: sc, items: None, stmt_items: None, inner_attrs: None, expand_deps: deps, inner_attr }
                }
            };
            front.chunks.push(chunk);
        }
    }
    let item_scans: Vec<scan::ItemScan> = front.chunks.iter().flat_map(|c| c.scan.items.iter().copied()).collect();
    let env = scan::env_hash(item_scans.iter());
    let fn_count = front.chunks.iter().map(|c| c.scan.fns.len()).sum::<usize>();
    // (chunk, index in chunk) for every function, in LocalDefId order.
    let fn_at: Vec<(usize, usize)> = {
        // Collect's LocalDefId order: top-level fns first, then nested.
        let mut tops: Vec<(usize, usize)> = Vec::new();
        let mut nested: Vec<(usize, usize)> = Vec::new();
        for (c, ch) in front.chunks.iter().enumerate() {
            for k in 0..ch.scan.fns.len() {
                if ch.scan.fns[k].nested {
                    nested.push((c, k));
                } else {
                    tops.push((c, k));
                }
            }
        }
        tops.extend(nested);
        tops
    };
    let scan_of = |front: &Front, i: usize| -> (u64, u32) {
        let f = &front.chunks[fn_at[i].0].scan.fns[fn_at[i].1];
        (f.body_hash, map.line_col_at(ROOT_FILE, f.fn_offset).0)
    };
    t.lap(if need.len() == ranges.len() { "lex+scan (par)" } else { "lex+scan changed chunks" });
    front.src.clone_from(&src);
    front.map = map.clone();

    // Which rule applies (see the top of this file). Bodies and
    // signatures mode parse into the old Ast: new nodes go at the end
    // and the replaced ones stay. `stmt_items` is also the list of body
    // items that collect numbers in order, so once the Ast has one, a
    // re-parsed body adds a second copy (a fn that no slot maps to and
    // that is never checked: a warm false accept) or puts it out of
    // file order. Such a file takes the full parse. (The signatures
    // splice below does replace a re-parsed chunk's body items; this
    // guard stays as the driver's rule until reuse there is proven.)
    // Bodies mode parses no chunk, so it needs an Ast with live nodes for
    // every item (`Front::chunks_blanked`).
    // A bloated arena (`ast_bloated`) takes the full parse too: it
    // builds the Ast fresh and drops the replaced nodes.
    let compact = ast_bloated(front);
    let splice = front.ast.stmt_items.is_empty();
    let bodies_only = splice && !compact && !front.chunks_blanked && front.env_hash == Some(env) && front.ast_fn_count == fn_count;
    // The edit window in old coordinates: old bytes `edit.0..edit.1`
    // changed; everything before and after is the same text.
    let edit = (prefix, old_len - suffix);
    // Bodies mode re-parses the changed bodies into the live Ast and moves
    // every other span for the one edit. It applies only when that is
    // exact (`bodies_mode_ok`); else the request takes signatures mode,
    // which re-parses the chunks the edit touched.
    let bodies_changed: Option<Vec<usize>> = bodies_only
        .then(|| {
            (0..fn_count)
                .filter(|&i| {
                    let slot = front.fn_slot[i] as usize;
                    front.slot_hash[slot] != scan_of(front, i).0 || !caches.ok[slot]
                })
                .collect::<Vec<usize>>()
        })
        .filter(|changed| bodies_mode_ok(&front.ast, &front.fn_loc, changed, edit, delta));
    let changed_names =
        if bodies_changed.is_some() || !splice || compact || front.env_hash.is_none() { None } else { fn_only_changes(&front.items, &item_scans) };
    let mut mode = if bodies_changed.is_some() {
        "bodies"
    } else if changed_names.is_some() {
        "signatures"
    } else {
        "full"
    };

    // Bodies mode: parse every changed body on its own first (as the body
    // patch does), so a parse error or a new body item is known before the
    // live Ast changes. `bodies_out` is None when bodies mode does not
    // apply, or when a new body gained body items (a nested fn, const,
    // static, or `use`): `parse_body` cannot place those in `stmt_items`
    // in parser order, so that request takes the full parse.
    let bodies_out: Option<(Vec<usize>, Vec<usize>, bool)> = if let Some(mut changed) = bodies_changed {
        for &i in &changed {
            let slot = front.fn_slot[i] as usize;
            // The hash now names a body that has not been checked yet, so
            // the old passing mark goes with it: after a parse error below
            // this function must not look unchanged and passing (fuzz seed
            // 29, iter 562). The check loop rewrites `ok` for every changed
            // function it reaches.
            front.slot_hash[slot] = scan_of(front, i).0;
            caches.ok[slot] = false;
            caches.has_out[slot] = false;
            if let Some(r) = caches.slot_reads.get_mut(slot) {
                *r = None;
            }
        }
        let mut parsed = Vec::with_capacity(changed.len());
        let mut failed = None;
        for &i in &changed {
            let chunk = &front.chunks[fn_at[i].0];
            let f = &chunk.scan.fns[fn_at[i].1];
            let mut body_ast = Ast::default();
            match parser::parse_body(&chunk.lexed.tokens[f.body.clone()], &chunk.lexed.strings, &mut body_ast, &front.interner, &front.known) {
                Ok((body, exprs, pats)) => parsed.push((body_ast, body, exprs, pats)),
                Err(d) => {
                    failed = Some(d);
                    break;
                }
            }
        }
        t.lap("parse changed bodies");
        if failed.is_none() && parsed.iter().any(|(a, ..)| !a.stmt_items.is_empty()) {
            mode = "full";
            None
        } else {
            // The old bodies' nodes stay in the arenas, unreachable: blank
            // them while their spans are in old coordinates, because some
            // passes scan whole arenas (closures, `dyn`, type paths).
            for &i in &changed {
                let (item, sub) = front.fn_loc[i];
                if let Some(b) = fn_def_at(&front.ast, item, sub).body {
                    let sp = front.ast.block(b).span;
                    span_shift::blank_nodes(Arc::make_mut(&mut front.ast), sp.file, (sp.lo, sp.hi), None);
                }
            }
            shift_ast_spans(front, edit.0, edit.1, delta);
            t.lap("blank+shift");
            if let Some(d) = failed {
                // The changed bodies are blank and not replaced: their
                // chunks lose their items, so the next request parses them
                // again (in signatures or full mode).
                for &i in &changed {
                    front.chunks[fn_at[i].0].items = None;
                }
                front.chunks_blanked = true;
                return errors(&mut [d], &map, &src, req);
            }
            for (&i, (body_ast, body, exprs, pats)) in changed.iter().zip(parsed) {
                let before = (front.ast.exprs.len() as u32, front.ast.pats.len() as u32, front.ast.blocks.len() as u32);
                let stmt_base = front.ast.stmt_items.len() as u32;
                let _ = Arc::make_mut(&mut front.ast).append_chunk(body_ast, stmt_base);
                let (item, sub) = front.fn_loc[i];
                let def = fn_def_at_mut(Arc::make_mut(&mut front.ast), item, sub);
                def.body = Some(crate::ast::BlockId(body.0 + before.2));
                // `bodies_mode_ok` proved no node sits between the
                // parameters and the body, so these are the cold ranges.
                def.exprs = (exprs.0 + before.0, exprs.1 + before.0);
                def.pats = (pats.0 + before.1, pats.1 + before.1);
            }
        // A changed const fn body can move const and static values,
        // array lengths, and discriminants that unchanged bodies baked
        // in. Make every unchanged passing body a dirty-walk candidate,
        // as `slot_update` does in the other modes: the walk replays
        // their recorded reads against the re-collected program, whose
        // `Sig` fingerprints fold the new values.
        let const_fn_changed = changed.iter().any(|&i| {
            let (item, sub) = front.fn_loc[i];
            fn_def_at(&front.ast, item, sub).qual.is_const
        });
        let mut mention_only = Vec::new();
        if const_fn_changed {
            let mut listed = vec![false; fn_count];
            changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
            for i in 0..fn_count {
                if !listed[i] && caches.ok[front.fn_slot[i] as usize] {
                    mention_only.push(i);
                    changed.push(i);
                }
            }
        }
        Some((changed, mention_only, const_fn_changed))
        }
    } else {
        None
    };
    let (changed, mention_only, const_fn_changed): (Vec<usize>, Vec<usize>, bool) = if let Some(r) = bodies_out {
        r
    } else if changed_names.is_some() {
        // Only top-level functions changed: parse just the chunks with new text, and splice their
        // items between the unchanged chunks' items.
        let todo: Vec<usize> = (0..front.chunks.len()).filter(|&i| front.chunks[i].items.is_none()).collect();
        // Later chunks start under the file's inner allows, as a whole
        // parse scopes them (the first chunk reads them itself).
        let seed = chunk_seed_allows(front);
        let parsed = par_map(&todo, |&i| parse_chunk(front, i, &seed));
        // The replaced items' nodes go (see the bodies mode blank) while
        // their spans are in old coordinates, then every span moves. On a
        // parse error too: the fresh chunks then stay without items, so
        // the next request parses them again (`Front::chunks_blanked`).
        // Fresh chunks replace old bytes `replaced_old`; a stale kept
        // chunk replaces its own old bytes (it moved by `delta` if it sits
        // after the edit).
        if old_len > 0 {
            let mut gone = vec![replaced_old];
            for (c, &fresh) in front.chunks.iter().zip(&fresh_chunks) {
                if c.items.is_none() && !fresh {
                    let lo = if c.start >= region_end { (c.start as i64 - delta) as usize } else { c.start };
                    gone.push((lo, lo + c.text.len()));
                }
            }
            for (lo, hi) in gone {
                span_shift::blank_nodes(Arc::make_mut(&mut front.ast), ROOT_FILE, (lo as u32, hi as u32), None);
            }
            shift_ast_spans(front, edit.0, edit.1, delta);
        }
        if let Some(Err(d)) = parsed.iter().find(|p| p.is_err()) {
            let d = d.clone();
            front.chunks_blanked = old_len > 0;
            return errors(&mut [d], &map, &src, req);
        }
        let mut new_asts: FxMap<usize, Ast> = todo.iter().copied().zip(parsed.into_iter().map(|p| p.unwrap())).collect();
        // Splice every per-chunk list in chunk order: a re-parsed chunk
        // replaces its old items, body items, and inner attrs. Keeping
        // the old body items next to the new ones made collect see stale
        // nested fns, so the program had more fns than `fn_slot` (a warm
        // panic in the build re-emit loop). Arena nodes stay append-only
        // in `append_chunk`; only these enumerated lists are rebuilt.
        let old_block_count = front.ast.blocks.len();
        let mut old_items: Vec<Option<crate::ast::Item>> = std::mem::take(&mut Arc::make_mut(&mut front.ast).items).into_iter().map(Some).collect();
        let mut old_stmt_items: Vec<Option<crate::ast::Item>> =
            std::mem::take(&mut Arc::make_mut(&mut front.ast).stmt_items).into_iter().map(Some).collect();
        let mut old_inner_attrs: Vec<Option<crate::ast::Attr>> =
            std::mem::take(&mut Arc::make_mut(&mut front.ast).inner_attrs).into_iter().map(Some).collect();
        // Old body-item index to new index, for the blocks that already
        // exist. A replaced chunk's old entries map to the new entry at
        // the same offset when one exists (their blocks are orphans of
        // the old parse); the rest map to None and their statements drop.
        let mut stmt_remap: Vec<Option<u32>> = vec![None; old_stmt_items.len()];
        let mut items = Vec::with_capacity(old_items.len());
        let mut stmt_items = Vec::with_capacity(old_stmt_items.len());
        let mut inner_attrs = Vec::with_capacity(old_inner_attrs.len());
        for c in 0..front.chunks.len() {
            let start = items.len();
            let stmt_start = stmt_items.len();
            let inner_start = inner_attrs.len();
            match new_asts.remove(&c) {
                Some(ast) => {
                    let (its, sis, ias) = Arc::make_mut(&mut front.ast).append_chunk(ast, stmt_start as u32);
                    if let Some(old_range) = front.chunks[c].stmt_items.clone() {
                        for (k, old_idx) in old_range.enumerate() {
                            if k < sis.len() {
                                stmt_remap[old_idx] = Some((stmt_start + k) as u32);
                            }
                        }
                    }
                    items.extend(its);
                    stmt_items.extend(sis);
                    inner_attrs.extend(ias);
                }
                None => {
                    items.extend(front.chunks[c].items.clone().unwrap().map(|k| old_items[k].take().unwrap()));
                    for k in front.chunks[c].stmt_items.clone().unwrap() {
                        stmt_remap[k] = Some(stmt_items.len() as u32);
                        stmt_items.push(old_stmt_items[k].take().unwrap());
                    }
                    inner_attrs.extend(front.chunks[c].inner_attrs.clone().unwrap().map(|k| old_inner_attrs[k].take().unwrap()));
                }
            }
            front.chunks[c].items = Some(start..items.len());
            front.chunks[c].stmt_items = Some(stmt_start..stmt_items.len());
            front.chunks[c].inner_attrs = Some(inner_start..inner_attrs.len());
        }
        // Blocks from before the splice still hold old body-item
        // indexes; blocks the re-parsed chunks appended already hold
        // new ones (`append_chunk` shifted them to the splice base).
        for b in &mut Arc::make_mut(&mut front.ast).blocks[..old_block_count] {
            b.stmts.retain_mut(|st| match st {
                crate::ast::Stmt::Item(i) => match stmt_remap.get(*i as usize).copied().flatten() {
                    Some(n) => {
                        *i = n;
                        true
                    }
                    None => false,
                },
                _ => true,
            });
        }
        Arc::make_mut(&mut front.ast).items = items;
        Arc::make_mut(&mut front.ast).stmt_items = stmt_items;
        Arc::make_mut(&mut front.ast).inner_attrs = inner_attrs;
        match slot_update(front, caches, item_scans, env, changed_names, &fn_at, crate_ids, &scan_of, &mut t, None) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
            }
        }
    } else {
        // Reused chunks carry shifted token spans (see chunk assembly), so every chunk is ready.
        let seed = chunk_seed_allows(front);
        let parsed = par_map(&front.chunks, |c| {
            if c.start == 0 {
                parser::parse(&c.lexed, &front.interner, &front.known)
            } else {
                parser::parse_seeded(&c.lexed, &front.interner, &front.known, &seed)
            }
        });
        let ast = if parsed.iter().all(|p| p.is_ok()) {
            let mut start = 0;
            let mut stmt_start = 0;
            let mut inner_start = 0;
            for (c, p) in front.chunks.iter_mut().zip(&parsed) {
                let p = p.as_ref().unwrap();
                c.items = Some(start..start + p.items.len());
                start += p.items.len();
                c.stmt_items = Some(stmt_start..stmt_start + p.stmt_items.len());
                stmt_start += p.stmt_items.len();
                c.inner_attrs = Some(inner_start..inner_start + p.inner_attrs.len());
                inner_start += p.inner_attrs.len();
            }
            Ast::concat(parsed.into_iter().map(|p| p.unwrap()).collect())
        } else {
            // Re-parse serially for an exact error.
            let whole =
                match lexer::lex(&src, ROOT_FILE, 0, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode, req.session.profile, &req.session)) {
                    Ok((w, _deps)) => w,
                    Err(mut d) => {
                        front.env_hash = None;
                        return errors(std::slice::from_mut(&mut d), &map, &src, req);
                    }
                };
            match parser::parse(&whole, &front.interner, &front.known) {
                Ok(a) => a,
                Err(d) => {
                    front.env_hash = None;
                    return errors(&mut [d], &map, &src, req);
                }
            }
        };
        front.ast = Arc::new(ast);
        front.ast_gen = 0;
        front.fresh_exprs = front.ast.exprs.len();
        match slot_update(front, caches, item_scans, env, None, &fn_at, crate_ids, &scan_of, &mut t, None) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
            }
        }
    };

    // The chunk path's rule, for the visits line (fuzz coverage).
    visits.why = mode;
    // Every item has live nodes again (bodies mode never runs while some lack them).
    front.chunks_blanked = false;
    let fn_lines_all: Vec<u32> = (0..fn_count).map(|i| scan_of(front, i).1).collect();
    let body_hashes_all: Vec<u64> = (0..fn_count).map(|i| scan_of(front, i).0).collect();
    (map, changed, mention_only, const_fn_changed, fn_count, mode, fn_lines_all, body_hashes_all, None)
    };
    // A fn edit that moved Adt or static ids took the full path (`slot_update`).
    let mode = if std::mem::take(&mut front.ids_forced_full) { "full" } else { mode };
    let scan_of = |front: &Front, i: usize| {
        let _ = front;
        (body_hashes_all[i], fn_lines_all[i])
    };

    // Persist slot assignment when it grew (or was compacted), and
    // the unit byte target with it when a daemon session chose one the
    // manifest does not record yet: the next daemon seeds from this
    // file even if this compile later fails, because the assignment
    // itself is already in use by cached C. A one-shot session
    // writes back the recorded byte target unchanged, so its slot
    // stores never erase a daemon's grouping. A target first picked
    // by this build's grouping step is stored by the next request
    // that reaches this point (or re-derived: the picking formula
    // is a function of the same total C bytes).
    let store_unit_bytes = if caches.persistent { caches.unit_bytes as u32 } else { front.manifest_unit_bytes };
    if front.slot_of.len() != front.slot_manifest_stored || store_unit_bytes != front.manifest_unit_bytes {
        if let Some(cache) = disk_cache {
            cache.store_slot_manifest(&session_key, &front.slot_of, store_unit_bytes);
        }
        front.slot_manifest_stored = front.slot_of.len();
        front.manifest_unit_bytes = store_unit_bytes;
    }

    // The resolver path computes crate identity from the Cargo graph;
    // the single-file path keeps the session key's identity.
    let crate_ids = if let Some(ids) = front.resolved_crate_ids.take() { ids } else { crate_ids };
    // Generic reuse (driver/gen_reuse.rs, W-PERF): template checks and
    // instance discovery of a generic program are stored per stable def.
    // They hold while the trait system holds (collect checks
    // `gen_reuse::trait_key` before its body checks run); an entry made
    // under another item-level environment (item-scan hash, AST fn count,
    // and const fn bodies, whose edits move values) replays its recorded
    // reads first. Anything else drops them: a nested static (its index
    // can move), or a slot compaction (cached C carries slot numbers). A
    // const fn edit on a patch path drops them too (`const_fn_checked`). The source key of an AST fn is its body and head hash.
    // A body patch moves no static (body items keep their indexes), so
    // on that path nested statics keep their indices and the cache holds.
    // A full resolve keeps it too once a program's static ids are known:
    // after collect, they must equal the last program's (below).
    // Const fn bodies join the environment: a const fn edit moves const and
    // static values while no reader's source moves, so every entry and slot
    // checked before it must ask its reads (`Sig` folds a value), discovery
    // and template entries (`GenReuse::reads_hold`) as instance and closure
    // slots. Body hashes do not hold the fn's line, so a shift does not move it.
    let const_fns = {
        let mut h = crate::intern::FxHasher::default();
        for (i, &(item, sub)) in front.fn_loc.iter().enumerate().take(fn_count) {
            if fn_def_at(&front.ast, item, sub).qual.is_const {
                std::hash::Hash::hash(&(i, body_hashes_all.get(i)), &mut h);
            }
        }
        std::hash::Hasher::finish(&h)
    };
    let gen_env = front.env_hash.map(|env| {
        let mut h = crate::intern::FxHasher::default();
        std::hash::Hash::hash(&(env, fn_count, const_fns), &mut h);
        std::hash::Hasher::finish(&h)
    });
    // The item patch moves no static either: it refuses a fn with body
    // items (driver/patch.rs), so every other body keeps its items.
    let nested_statics = !matches!(visits.path, "patch" | "item") && front.ast.stmt_items.iter().any(|it| matches!(it.kind, ItemKind::Static(_)));
    let statics_may_move = nested_statics && front.prev_static_defs.is_none();
    // What a failed collect left undone joins this request. A const fn
    // edit (`Front::const_fn_pending`) makes this request one too, so every
    // passing body is a candidate and generic reuse goes. Else the
    // candidates it left unwalked (`Front::walk_pending`) join the walk
    // while they still pass and no other rule listed them; a changed body
    // lost its passing mark and rechecks.
    // A slot past the passing marks is new here: it never passed.
    let passed = |front: &Front, caches: &Caches, i: usize| front.fn_slot.get(i).is_some_and(|&s| caches.ok.get(s as usize) == Some(&true));
    // The derive delta's keyed shortcuts (its replays, the keyed dirty walk
    // below) hold only when a derive delta is all that moved since the
    // last walk: not with a failed collect's leftovers, unless they came
    // from refused derive deltas alone (`Front::pending_derive_only`).
    let derive_leftovers = std::mem::take(&mut front.pending_derive_only);
    if front.const_fn_pending || (!front.walk_pending.is_empty() && !derive_leftovers) {
        caches.derive_only = false;
    }
    if std::mem::take(&mut front.const_fn_pending) {
        const_fn_changed = true;
        front.walk_pending.clear();
        let mut listed = vec![false; fn_count];
        changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
        let cands: Vec<usize> = (0..fn_count).filter(|&i| passed(front, caches, i) && !listed[i]).collect();
        mention_only.extend_from_slice(&cands);
        changed.extend_from_slice(&cands);
        changed.sort_unstable();
    } else if !front.walk_pending.is_empty() {
        let mut pending = vec![false; caches.ok.len()];
        for s in std::mem::take(&mut front.walk_pending) {
            if let Some(p) = pending.get_mut(s as usize) {
                *p = true;
            }
        }
        let mut listed = vec![false; fn_count];
        changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
        let cands: Vec<usize> = (0..fn_count)
            .filter(|&i| front.fn_slot.get(i).is_some_and(|&s| pending.get(s as usize) == Some(&true)) && passed(front, caches, i) && !listed[i])
            .collect();
        mention_only.extend_from_slice(&cands);
        changed.extend_from_slice(&cands);
        changed.sort_unstable();
    }
    // The trait-system half of this joins after collect (`gen_ok`).
    // A const fn edit on a full resolve keeps generic reuse: the values it
    // can move reach the stored entries through their reads (a const or
    // static item's `Sig` folds its value) or their sources (a body const
    // folds into its owner fn's, collect `fold_body_const_values`).
    let const_fn_checked = const_fn_changed && !matches!(visits.path, "patch" | "item");
    let mut gen_ok_here =
        caches.persistent && gen_env.is_some() && (!const_fn_changed || const_fn_checked) && !statics_may_move && !front.slots_renumbered;
    visits.generic = match () {
        _ if gen_ok_here => "on",
        _ if !caches.persistent => "one_shot",
        _ if gen_env.is_none() => "no_env",
        _ if const_fn_changed => "const_fn",
        _ if statics_may_move => "statics_unknown",
        _ => "renumbered",
    };
    if !gen_ok_here {
        caches.gen_reuse.clear();
    }
    front.slots_renumbered = false;
    caches.gen_reuse.on = caches.persistent && gen_env.is_some();
    caches.gen_reuse.one_shot = !caches.persistent;
    caches.gen_reuse.env = gen_env.unwrap_or(0);
    // On a body patch, slot heads stand and only the changed fns' body
    // hashes moved (the slot update lists exactly those), so the last
    // request's fingerprints stand for every other fn.
    let ast_src_of = |front: &Front, i: usize| {
        let head = front.fn_slot.get(i).and_then(|&s| front.slot_head.get(s as usize)).copied().unwrap_or(0);
        let mut h = crate::intern::FxHasher::default();
        std::hash::Hash::hash(&(body_hashes_all[i], head), &mut h);
        std::hash::Hasher::finish(&h)
    };
    if visits.path == "patch" && caches.gen_reuse.ast_src.len() == fn_count {
        for &i in &changed {
            if let Some(slot) = caches.gen_reuse.ast_src.get_mut(i) {
                *slot = ast_src_of(front, i);
            }
        }
    } else {
        caches.gen_reuse.ast_src = (0..fn_count).map(|i| ast_src_of(front, i)).collect();
    }
    // The resolver tables enter here, before collect's own body
    // checks (mono's template checks) run, so every body checks
    // with the visibility tables attached (see `Program::resolved`).
    // Unchanged values do not write: a kept program may share the Ast.
    // A write is no body edit, so it drops the kept programs.
    if front.ast.shipped != std_ranges || front.ast.lang_methods != std_methods {
        super::patch::drop_kept(front, caches);
        let ast = Arc::make_mut(&mut front.ast);
        ast.shipped = std_ranges.clone();
        ast.lang_methods = std_methods;
    }
    // The kept program of the last request stands in for collect when
    // only provable body edits happened since (`patch::reuse_kept`). Its
    // laps (the signature delta's) count as collect laps.
    super::laps::start();
    caches.header_moves = None;
    let kept = if gen_ok_here {
        super::patch::reuse_kept(front, caches, resolved_tables.as_ref(), req.cmd == Cmd::Build)
    } else {
        Err("gen state")
    };
    // What a header delta on the kept program can move, when no derive
    // delta ran with it (the keyed walks below).
    let mut header_moves = caches.header_moves.take().filter(|_| kept.is_ok() && caches.derive_dirty.is_none());
    // A kept program that only body edits moved (no header or derive
    // delta): only `Checked` keys can differ from what its read sets held
    // against. An `impl Trait` body edit moves the environment hash, so
    // every instance would take the full walk, but `reuse_kept` proved its
    // hidden type stands (the keyed walk below).
    let body_only = kept.is_ok() && header_moves.is_none() && caches.derive_dirty.is_none();
    // What a derive delta on the kept program can move, when every edit of
    // this request is a derive list edit (the keyed dirty walk below).
    let derive_dirty = caches.derive_dirty.take().filter(|_| std::mem::take(&mut caches.derive_only) && kept.is_ok());
    // A const fn edit that only const and static values read: the kept
    // program stands when they all evaluate as before. Else (or with no
    // kept program) the request goes on as a const fn edit that changed
    // values: no generic reuse, and every unchanged passing body is a
    // read-set candidate.
    let mut kept = kept;
    if std::mem::take(&mut front.revalue_consts) {
        let hold = match &mut kept {
            Ok((p, _, _)) => collect::const_values_hold(p, &front.def_order.statics),
            Err(_) => false,
        };
        if !hold {
            kept = Err("gen state");
            const_fn_changed = true;
            gen_ok_here = false;
            visits.generic = "const_values";
            caches.gen_reuse.clear();
            // Added to the candidates already listed: a failed collect's
            // leftovers (`Front::const_fn_pending`) joined them above, and
            // dropping those rechecked a body under the new values but
            // kept its old C for the next build (hunt11 21:29 const chain).
            let mut listed = vec![false; fn_count];
            changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
            let cands: Vec<usize> = (0..fn_count).filter(|&i| caches.ok[front.fn_slot[i] as usize] && !listed[i]).collect();
            mention_only.extend_from_slice(&cands);
            changed.extend_from_slice(&cands);
            changed.sort_unstable();
        }
    }
    // A body edit of a fn that returns `impl Trait` (`Front::rpit_edit`):
    // with no kept program that stands, the hidden type may have moved,
    // and the users of the opaque type read it through the definer's
    // `Sig` fingerprint. As a full resolve's full mode does, every
    // unchanged passing body is a read-set candidate, and derived glue may
    // move.
    let rpit_edit = std::mem::take(&mut front.rpit_edit);
    // A program put back after a refused patch: the collect that answered
    // in between stored read sets against its own program (`Front::kept_put_back`).
    let put_back = std::mem::take(&mut front.kept_put_back) && kept.is_ok();
    if (rpit_edit && kept.is_err()) || put_back {
        let mut listed = vec![false; fn_count];
        changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
        let cands: Vec<usize> = (0..fn_count).filter(|&i| caches.ok[front.fn_slot[i] as usize] && !listed[i]).collect();
        mention_only.extend_from_slice(&cands);
        changed.extend_from_slice(&cands);
        changed.sort_unstable();
        caches.glue_stale = true;
    }
    // The kept program's generation (`Program::verified`): the slot read
    // sets marked with it held against it before this request's deltas.
    // The program loses it here, so one kept again before this request
    // walks its read sets (a template error) gives the next request no
    // base.
    let mut keyed_base = 0;
    let kept = match kept {
        Ok((mut p, spans, errs)) => {
            keyed_base = std::mem::take(&mut p.verified);
            visits.kept = "reuse";
            visits.prog_spans = spans;
            if errs.is_empty() {
                Some(Ok(p))
            } else {
                // Template errors are body errors: the program stands
                // for the next edit, which checks that template again.
                // After a header delta, the read sets it cannot have moved
                // stay verified against the program (the keyed walk of its
                // moved keys); the others lose the mark, so the next request
                // walks only those in full.
                if let Some(touched) = header_moves.as_ref().filter(|_| keyed_base != 0) {
                    let mode = usize::from(p.gx.walk_instances);
                    let k = keyed_dirty(&p, front, caches, &|k| touched.hit_pure(&p, k), keyed_base, &mut FxMap::default());
                    for (s, d) in k.iter().enumerate() {
                        if *d == Some(true)
                            && let Some(Some(r)) = caches.slot_reads.get_mut(s)
                        {
                            r.verified[mode] = 0;
                        }
                    }
                    p.verified = keyed_base;
                }
                super::patch::keep(front, p);
                Some(Err(errs))
            }
        }
        Err(why) => {
            // `reuse_kept` took this mode's program; it is back only when
            // the program stands for the next request (a refused header
            // delta left it as it was), and a clean collect replaces it.
            // Every program goes when the generic state moved.
            visits.kept = why;
            let old: Vec<_> = if why == "gen state" { front.kept.iter_mut().filter_map(Option::take).collect() } else { Vec::new() };
            if !old.is_empty() && caches.persistent {
                let _ = crate::pool::thread("lust-drop").spawn(move || drop(old));
            }
            None
        }
    };
    front.note_kept_use(visits.path, visits.kept);
    // Template check errors from the kept program are collect's errors
    // (`gen_reuse.template_errors` counts them).
    let collect = |front: &mut Front, caches: &mut Caches| {
        collect::collect_reuse(
            front.ast.clone(),
            front.interner.clone(),
            front.known.clone(),
            crate_ids,
            req.cmd == Cmd::Build,
            &mut front.def_order,
            resolved_tables.clone(),
            &mut caches.gen_reuse,
            &std_routes,
        )
    };
    // A refused header delta that found the edited signature's own errors
    // gives collect's answer (`Front::delta_errs`; the oracle compares it).
    let delta_errs = front.delta_errs.take();
    let delta_answered = delta_errs.is_some();
    // A collect from a kept type store (B1-PLAN.md) runs under its oracle.
    let pooled = kept.is_none() && delta_errs.is_none() && caches.gen_reuse.type_pool.is_some();
    let collected = match kept {
        Some(r) => r,
        None if delta_errs.is_some() => Err(delta_errs.unwrap_or_default()),
        None => match collect(front, caches) {
            // A static moved after all (statics rank by identity, so only a
            // removed one moves the ones after it): generic reuse goes and
            // collect runs again without it. An added static moves none.
            Ok(p) if nested_statics && gen_ok_here && !front.prev_static_defs.as_deref().is_some_and(|prev| statics_kept(prev, &p.static_defs)) => {
                drop(p);
                caches.gen_reuse.clear();
                gen_ok_here = false;
                visits.generic = "statics_moved";
                collect(front, caches)
            }
            c => c,
        },
    };
    if pooled && super::item_oracle::pool_on() {
        super::item_oracle::check_pool(front, crate_ids, req.cmd == Cmd::Build, resolved_tables.clone(), &std_routes, &collected);
    }
    if let Ok(p) = &collected {
        front.prev_static_defs = Some(p.static_defs.clone());
    }
    let mut program = match collected {
        Ok(p) => p,
        Err(mut ds) => {
            // A collect error drops the item state, so the next request
            // rebuilds it in full mode. Errors that all come from
            // template checks are body errors: the item state stands,
            // and the next edit (usually the fix) stays a body edit. So
            // does a body patch's: its items are the last full resolve's,
            // and only a body moved (a const fn body that fails const
            // evaluation, say); the next request collects again. So does
            // an item patch's: its slot update set the item state from
            // the item rescan (sigedit PLAN R9), and the next request
            // collects again.
            // The per-slot caches still match this request's slot update
            // (bodies it changed lost their passing mark there), so the
            // next slot update keeps them and walks every passing body
            // (`Front::walk_after_reject`) instead of clearing them.
            // But this request's dirty state never reached the bodies:
            // read-set walk candidates kept their passing mark for a walk
            // that never ran (a body that calls a fn whose bound changed),
            // a const fn edit moved values no body rechecked under, and
            // collect may have seen a new trait system. The next request
            // takes them over (`Front::walk_pending`,
            // `Front::const_fn_pending`, `GenReuse::forget_failed_gate`).
            // A kept program put back with derive list edits alone (its
            // refused derive delta was undone) covers them: the next
            // derive delta on it moves every key they moved.
            let mode = usize::from(req.cmd == Cmd::Build);
            front.pending_derive_only = !const_fn_changed && front.kept[mode].as_ref().is_some_and(|k| k.derive_edits_only());
            // Not after a header delta's own answer (`delta_answered`): its
            // program went back with the edit pending, and the next delta
            // moves the same keys again (its keyed walk covers them).
            if !delta_answered {
                front.walk_pending.extend(mention_only.iter().filter_map(|&i| front.fn_slot.get(i).copied()));
            }
            front.walk_pending.sort_unstable();
            front.walk_pending.dedup();
            front.const_fn_pending |= const_fn_changed;
            caches.gen_reuse.forget_failed_gate();
            if caches.gen_reuse.template_errors != ds.len() && !matches!(visits.path, "patch" | "item") {
                front.env_hash = None;
                front.walk_after_reject = true;
            }
            // This collect's static ids are unknown, so the generic reuse
            // entries it stored or replayed go. The rest were made under
            // the last program's static ids, which stay the reference.
            if nested_statics {
                let env = caches.gen_reuse.env;
                caches.gen_reuse.drop_env(env);
            }
            if super::item_oracle::on() {
                let (build, tables) = (req.cmd == Cmd::Build, resolved_tables.as_ref());
                let (lines, hashes) = (&fn_lines_all, &body_hashes_all);
                super::item_oracle::check(front, caches, Err(&ds), &[], fn_count, hashes, lines, visits.path, crate_ids, build, tables);
            }
            front.last_visits.clear();
            visits.render(&mut front.last_visits);
            log_visits(&front.last_visits);
            return errors(&mut ds, &map, &src, req);
        }
    };
    // Every body of a generic program rechecks when the trait system
    // moved too (collect dropped the cache then). Derive lists moved since
    // the last build regenerate the glue only: each slot's codegen records
    // the derive lists it reads into the slot's read set (below), so the
    // walk rechecks just those slots (gen_reuse.rs `build_derives_moved`).
    if req.cmd == Cmd::Build && caches.gen_reuse.build_derives_moved() {
        caches.glue_stale = true;
    }
    let gen_ok = gen_ok_here && !caches.gen_reuse.trait_changed;
    // A std or lang trait impl edit moves no trait-system key: bodies read
    // those impls (`ReadKey::LangImpls`). Derived and drop glue read them
    // with no read, so the next build regenerates the glue (once:
    // `glue_stale` holds until a build does).
    if std::mem::take(&mut caches.gen_reuse.lang_changed) {
        caches.glue_stale = true;
    }
    if gen_ok_here && !gen_ok {
        visits.generic = "trait_key";
    }
    // A program with no generics rechecks every body on a new trait
    // system too. Its plain bodies ask the impls of lang and std traits
    // with no recorded read (format glue's `has_display`/`require_fmt`,
    // `?` conversions, `for` loops, drop glue): only user trait impls
    // have `ImplSet` reads. A removed `impl Display for S` kept the
    // pass of a `main` that formats S (hunt11 21:29).
    if !program.gx.has_generics && caches.gen_reuse.trait_changed {
        let mut listed = vec![false; fn_count];
        changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
        mention_only.clear();
        for i in 0..fn_count {
            let s = front.fn_slot[i] as usize;
            caches.ok[s] = false;
            caches.has_out[s] = false;
            caches.slot_reads[s] = None;
            if !listed[i] {
                changed.push(i);
            }
        }
        changed.sort_unstable();
        caches.glue_stale = true;
    }
    // Persist the def order when collect grew it, like the slot
    // manifest above: the next daemon must number defs as this
    // one did or the disk objects' indices move under it.
    front.def_order_loaded = false;
    if def_order_size(&front.def_order) != front.def_order_stored {
        if let Some(cache) = disk_cache {
            cache.store_def_order(&session_key, &front.def_order, crate_ids.stable);
        }
        front.def_order_stored = def_order_size(&front.def_order);
    }
    // Read sets serve the next request's dirty walk; a one-shot process
    // has none, so its body checks skip recording and fingerprinting
    // (collect's own checks did too: `GenReuse::one_shot`).
    program.record_reads = caches.persistent;
    program.unwind = !session_key.profile.panic_abort;
    program.overflow_checks = session_key.profile.overflow_checks;
    program.debug_assertions = session_key.profile.debug_assertions;
    // Unwind tables need a C compiler with -fexceptions and a C++ driver, never tcc: a
    // release driver build uses them, one-shot or from a persistent session such as a
    // front image (LUST_UNWIND_TABLES=0 turns them off); --emit-c in a one-shot process
    // only with LUST_UNWIND_TABLES=1 (difftest EH=1, which builds that C itself). A tcc
    // build ignores the variable: it would link that C without the C++ unit, and
    // catch_unwind would return Ok after a panic (rel-opt).
    let tables_env = std::env::var("LUST_UNWIND_TABLES").ok();
    program.unwind_tables = program.unwind
        && if req.cc {
            tables_env.as_deref() != Some("0")
        } else {
            !caches.persistent && req.emit_c.is_some() && tables_env.as_deref() == Some("1")
        };
    // Route the spliced source std fns: resolve each registry row's
    // mangled name to the local fn the splice defined. A missing fn is
    // a broken std build (the loader found it standalone), so it is an
    // installation error, not a user diagnostic.
    if !std_ranges.is_empty() {
        program.shipped_ranges = std_ranges;
        // Collect routed the ones it found for mono; route all again.
        program.std_fns.clear();
        for def in std_routes {
            let mangled = front.interner.intern(def.mangled);
            match program.fn_names.get(&mangled) {
                Some(&f) => {
                    let path: Vec<Sym> = def.path.iter().map(|s| front.interner.intern(s)).collect();
                    program.std_fns.push((path, f));
                }
                None => {
                    front.env_hash = None;
                    return Response {
                        stderr: format!("error: lust std load failed: spliced std fn `{}` is missing after collect\n", def.path.join("::")),
                        code: 3,
                        ..Default::default()
                    };
                }
            }
        }
    }
    // The program stays unchanged from here on (until a patch takes it
    // back), so deep Adt fingerprints can be kept across reads.
    program.fp_memo.on(program.adts.len());
    if program.fns.len() < fn_count {
        // The scanner and the parser disagree (only possible with unusual syntax). Start over.
        front.env_hash = None;
        return Response { stderr: "error: internal: function count mismatch; run again\n".into(), code: 3, ..Default::default() };
    }
    // Mono instance slots (docs/ARCH.md section 4.2; W-TRAITS-CORE
    // through W-DRIVER): collect appends materialized instances
    // after the AST fns. They get append-only slots keyed by their
    // instance disk identity, exactly like AST fns in slot_update;
    // templates and trait-method stubs are emptied like dead slots
    // so only plain fns and instances are checked and generated.
    // Instance slots keep their check state across requests (generic
    // reuse): `slot_hash` holds the source fingerprint of the last
    // check, and `ok` false marks one stale.
    front.fn_slot.truncate(fn_count);
    front.inst_live = program.fns.len().saturating_sub(fn_count);
    if program.gx.has_generics {
        for i in fn_count..program.fns.len() {
            let disk = program.disk_id(LocalDefId(i as u32));
            if let Err(c) = def::insert_path(&mut front.slot_paths, disk, &format!("instance#{}", disk.hash.0)) {
                front.env_hash = None;
                return Response { stderr: format!("error: {c}\n"), code: 3, ..Default::default() };
            }
            let slot = match front.slot_of.get(&disk) {
                Some(&slot) => slot,
                None => {
                    let slot = front.slot_of.len() as u32;
                    front.slot_of.insert(disk, slot);
                    slot
                }
            };
            front.fn_slot.push(slot);
        }
        let n_slots = front.slot_of.len();
        caches.ok.resize(n_slots, false);
        caches.has_out.resize(n_slots, false);
        caches.out.resize_with(n_slots, FnOut::default);
        caches.slot_reads.resize_with(n_slots, || None);
            caches.slot_ir.resize_with(n_slots, || None);
        front.slot_hash.resize(n_slots, 0);
        front.inst_slot.resize(n_slots, false);
        front.slot_env.resize(n_slots, 0);
        let mut present = vec![false; n_slots];
        for i in fn_count..program.fns.len() {
            let s = front.fn_slot[i] as usize;
            front.inst_slot[s] = true;
            present[s] = true;
        }
        for s in 0..n_slots {
            if !front.inst_slot[s] {
                continue;
            }
            if !gen_ok {
                // Checked under another trait system.
                caches.ok[s] = false;
            }
            // An instance slot with no instance in a build is dead: its
            // C must leave the units. A check makes no generic fn
            // instances at all, so there an absent slot keeps its
            // state for the next build.
            if !present[s] && req.cmd == Cmd::Build {
                wipe_slot(caches, s);
                caches.ok[s] = false;
            }
        }
        for i in 0..program.fns.len() {
            if !matches!(
                program.gx.fn_class.get(i),
                Some(crate::check::generics::FnClass::Plain | crate::check::generics::FnClass::Instance | crate::check::generics::FnClass::Closure) | None
            ) {
                let s = front.fn_slot[i] as usize;
                caches.out[s] = FnOut::default();
                caches.has_out[s] = true;
                caches.ok[s] = true;
                caches.slot_reads[s] = None;
            }
        }
    } else {
        // No generics: every instance slot is dead. The marks stay
        // with the slot numbers, so the slot update never treats one
        // as a dead AST fn (passing, no C) that a later instance of the
        // same key could reuse.
        for s in 0..front.inst_slot.len().min(caches.ok.len()) {
            if front.inst_slot[s] && caches.ok[s] {
                wipe_slot(caches, s);
                caches.ok[s] = false;
            }
        }
    }
    t.lap("collect");
    t.note_parts(super::laps::take());
    if visits.kept != "reuse" {
        visits.collect = front.ast.items.len() + front.ast.stmt_items.len() + program.fns.len();
    }
    visits.discovery = caches.gen_reuse.discovery_checked + caches.gen_reuse.discovery_reused;
    visits.pool = program.tys.pool_counts();
    // A full-mode edit or a const fn edit can move what derived glue
    // was generated from. Record that now, for whatever build comes
    // next: this request may be check-only, and the build request
    // after it sees an unchanged file in bodies mode. The build that
    // refreshes the glue clears the flag (see the glue step below).
    // A type item inside a fn body (R18) never edits in bodies mode
    // (its item scan folds it in, `ast_hash::item_scan`), but a
    // signatures-mode edit can move its fields, which its glue reads.
    if mode == "full" || const_fn_changed || (mode == "signatures" && def::has_body_type_items(&front.ast)) {
        caches.glue_stale = true;
    }

    // A signature edit that an `-> impl Trait` fn's body names (that fn
    // is in the work set) may move its hidden type, and callers read the
    // hidden type through its `Sig` without naming the edited item: an
    // unchanged `g() -> impl Debug { f() }` is no longer `Send` once `f`
    // returns an `Rc` (sigedit: Sol's RPIT chain). As for an RPIT body
    // edit, every unchanged passing body is a read-set candidate. The
    // return type decides, not a revealed hidden type: a definer whose
    // body now fails has none, and its callers must still check again.
    let rpit = |i: usize| {
        let mut found = Vec::new();
        if let Some(t) = program.fn_def(LocalDefId(i as u32)).ret {
            crate::check::generics::nested_impl_traits(&program.ast, t, &mut found);
        }
        !found.is_empty()
    };
    if mode == "signatures" && changed.iter().any(|&i| i < fn_count && rpit(i)) {
        let mut listed = vec![false; fn_count];
        changed.iter().filter(|&&i| i < fn_count).for_each(|&i| listed[i] = true);
        let cands: Vec<usize> = (0..fn_count).filter(|&i| caches.ok[front.fn_slot[i] as usize] && !listed[i]).collect();
        mention_only.extend_from_slice(&cands);
        changed.extend_from_slice(&cands);
        changed.sort_unstable();
    }
    // Read-set dirty walk (section 8.3 step 5): a candidate whose
    // recorded reads all still match this program keeps its last
    // passing result (check state and C). Candidates come from
    // signature-only edits (bodies that mention a changed name) and
    // from full-mode edits (every unchanged passing body; deep `Sig`
    // fingerprints carry type and impl edits into the reads that used
    // them). Candidates with no stored reads, or with any dirty read
    // (a changed binding answer, a moved method candidate, a failed
    // lookup that now resolves, a changed layout), stay in the work
    // set and lose their stored C, exactly as before this walk existed.
    let mut reads_reused = 0usize;
    let mut reads_invalidated = 0usize;
    // The node answers of this walk and of the generic reuse walk below, by
    // key index: they read the same program, and most instance bodies read
    // keys the plain bodies read too.
    let mut walk_answers = crate::driver::graph::KeyAnswers::default();
    // The keyed dirty walk (sigedit P3.2): after a derive delta only the
    // read keys it can move (`Program::derive_key_moves`) may have moved;
    // the delta found the slots that read one with a new fingerprint
    // (driver/kept_derive.rs). The other candidates reuse their results
    // here; the dirty ones go on to the walk below.
    if let Some(is_dirty) = derive_dirty.as_ref().filter(|_| mode == "full" && !mention_only.is_empty()) {
        let mut reused = vec![false; mention_only.iter().max().map_or(0, |&m| m + 1)];
        mention_only.retain(|&i| {
            let s = front.fn_slot[i] as usize;
            let clean = caches.slot_reads.get(s).is_some_and(Option::is_some) && !is_dirty.get(s).copied().unwrap_or(true);
            reused[i] = clean;
            !clean
        });
        reads_reused = reused.iter().filter(|&&r| r).count();
        changed.retain(|&i| reused.get(i) != Some(&true));
        t.lap("reads keyed walk");
    }
    // The keyed walk after a header delta (Sol review 2 item 1): a read
    // set of the delta's base program can only have moved in the keys the
    // delta moved (`keyed_dirty`). The candidates and the instance bodies
    // below with such a set take its answer; the others (a set of another
    // program, after a failed collect, say) go on to the full walks. The
    // oracle proves each keyed clean set with the full walk.
    // This request's node answers for the program, shared by the keyed
    // walk and the oracle's proofs below.
    let mut answers = FxMap::default();
    let wants = keyed_base != 0 && (!mention_only.is_empty() || program.gx.has_generics);
    let keyed: Option<Vec<Option<bool>>> = match header_moves.as_mut() {
        Some(touched) if wants => {
            super::laps::start();
            let touched: &crate::driver::kept_delta::Touched = touched;
            let k = keyed_dirty(&program, front, caches, &|k| touched.hit_pure(&program, k), keyed_base, &mut answers);
            t.lap("reads keyed index");
            t.note_parts(super::laps::take());
            Some(k)
        }
        None if wants && body_only && (rpit_edit || put_back) => {
            let checked = &|k: &crate::driver::graph::ReadKey| matches!(k, crate::driver::graph::ReadKey::Checked(_));
            let k = keyed_dirty(&program, front, caches, checked, keyed_base, &mut answers);
            t.lap("reads keyed index");
            Some(k)
        }
        _ => None,
    };
    let keyed_clean = |caches: &Caches, s: usize, memo: &mut FxMap<_, _>, i: usize| {
        let clean = keyed.as_ref().is_some_and(|k| k.get(s) == Some(&Some(false)));
        if clean && super::item_oracle::on() && caches.slot_reads[s].as_ref().is_some_and(|r| program.reads_dirty_memo(r, &caches.read_keys, memo) != 0) {
            super::item_oracle::fail("keyed clean body has dirty reads", visits.path, &i.to_string());
        }
        clean
    };
    if keyed.is_some() && !mention_only.is_empty() {
        let memo = &mut answers;
        let mut reused = vec![false; mention_only.iter().max().map_or(0, |&m| m + 1)];
        mention_only.retain(|&i| {
            let clean = keyed_clean(caches, front.fn_slot[i] as usize, memo, i);
            reused[i] = clean;
            !clean
        });
        let n = reused.iter().filter(|&&r| r).count();
        reads_reused += n;
        visits.keyed += n;
        changed.retain(|&i| reused.get(i) != Some(&true));
        t.lap("reads keyed walk");
    }
    if !mention_only.is_empty() {
        let slot_at = |i: usize| front.fn_slot[i] as usize;
        // First the dirty count of each candidate's stored reads (None:
        // no stored reads), with the read sets borrowed in place; then
        // the results land back in the caches.
        let sets: Vec<_> = mention_only.iter().map(|&i| caches.slot_reads.get(slot_at(i)).and_then(Option::as_ref)).collect();
        let dirty = reads_dirty_par(&program, &sets, &caches.read_keys, &mut walk_answers);
        // A mask, not a list: full mode makes every passing body a
        // candidate, and `changed` holds them all.
        let mut reused = vec![false; mention_only.iter().max().map_or(0, |&m| m + 1)];
        for (&i, d) in mention_only.iter().zip(dirty) {
            let s = slot_at(i);
            match d {
                Some(0) => {
                    reused[i] = true;
                    reads_reused += 1;
                }
                Some(d) => {
                    reads_invalidated += d;
                    caches.has_out[s] = false;
                    caches.slot_reads[s] = None;
                }
                None => caches.has_out[s] = false,
            }
        }
        if reads_reused > 0 {
            changed.retain(|&i| reused.get(i) != Some(&true));
        }
        t.lap("reads dirty walk");
    }
    // Every body still in the work set checks again, so its C (made under
    // the old reads) is stale until codegen replaces it; a check request
    // never gets there. The rules above clear it case by case; this keeps
    // a body listed by any other rule from reaching the next build with
    // C that holds old const values (hunt11 21:29 const chain).
    for &i in &changed {
        if let Some(&s) = front.fn_slot.get(i) {
            caches.has_out[s as usize] = false;
        }
    }

    // Slot-moved C re-emit (section 4.2): a reused fn whose own slot
    // or a used slot moved since its C was emitted (a compaction
    // renumber) re-emits C from its cached IR, with no recheck. The
    // rebuilt body must reproduce the cached IR fingerprint, and its
    // file text must stand (spans); anything else falls back to a
    // recheck through the ordinary work set.
    let slot = |i: usize| front.fn_slot[i] as usize;
    let mut reemit: Vec<(usize, ir::Body)> = Vec::new();
    let mut reemit_failed: Vec<usize> = Vec::new();
    let mut in_changed = vec![false; program.fns.len()];
    changed.iter().filter(|&&i| i < program.fns.len()).for_each(|&i| in_changed[i] = true);
    if req.cmd == Cmd::Build && !program.gx.has_generics {
        let mut file_hashes: FxMap<FileId, u64> = FxMap::default();
        for i in 0..program.fns.len() {
            if in_changed[i] {
                continue;
            }
            let s = slot(i);
            if !caches.has_out[s] {
                continue;
            }
            let Some(Some(cached)) = caches.slot_ir.get(s) else {
                // No cached IR (the program had generics when this C was
                // made): after a renumber the C may name moved slots, so
                // it is checked again.
                if front.slots_renumbered {
                    reemit_failed.push(i);
                }
                continue;
            };
            let moved = cached.slot_at_gen != s as u32
                || cached.used_at_gen.iter().any(|(disk, at_gen)| front.slot_of.get(disk) != Some(at_gen));
            if !moved {
                continue;
            }
            let file = program.fn_def(LocalDefId(i as u32)).name_span.file;
            let fh = *file_hashes.entry(file).or_insert_with(|| file_text_hash(&map, file));
            let rebuilt = if fh == cached.file_hash {
                super::ir_cache::rebuild(&program, cached, LocalDefId(i as u32))
            } else {
                None
            };
            match rebuilt {
                Some(body) if super::ir_cache::ir_fingerprint(&program, &body, &map, scan_of(front, i).1) == cached.ir_fp => {
                    reemit.push((i, body))
                }
                _ => reemit_failed.push(i),
            }
        }
        if !reemit.is_empty() || !reemit_failed.is_empty() {
            t.lap("ir re-emit rebuild");
        }
    }
    let reemitted = reemit.len();

    // A build under another codegen key (release C on or off, the release backend's
    // switches, debug info, unwind tables) makes every slot's C again, as a one-shot build
    // does: its slot cache holds C of the other form (a front image saved by a tcc build,
    // then a release driver build). A check makes no C and keeps the key.
    let release = super::release_c::on(caches.persistent, req.cc);
    if req.cmd == Cmd::Build {
        let key = super::release_c::codegen_key(release, req.debug, program.unwind_tables);
        if caches.codegen_key != key {
            caches.codegen_key = key;
            caches.has_out.iter_mut().for_each(|h| *h = false);
            caches.out.iter_mut().for_each(|o| *o = FnOut::default());
            caches.glue = GlueSet::default();
            caches.objects = None;
        }
    }
    // Front end for the functions that need it. A build also needs IR for functions with no C yet.
    let mut work = changed.clone();
    work.extend(reemit_failed.iter().copied());
    if req.cmd == Cmd::Build {
        work.extend((0..program.fns.len()).filter(|&i| !caches.has_out[slot(i)] && !in_changed[i]));
    }
    // The instance Adt ids this build generates C under, and whether one
    // names another instance than in the C made since the last full
    // regeneration (ids are session places: only a moved base or a reset
    // order does that).
    let inst_ids = if program.gx.has_generics && req.cmd == Cmd::Build { inst_adt_ids(&program) } else { Vec::new() };
    let ids_moved = inst_ids.iter().any(|(id, key)| caches.inst_ids.get(id).is_some_and(|k| k != key));
    if program.gx.has_generics {
        // Generic reuse: a plain fn rechecks when the front end or the
        // read-set walk put it in `changed`; an instance or closure body
        // fn when its source changed or, checked under another item-level
        // environment, its reads no longer hold; any of them when its
        // last check failed or a build has no C for it. C names Adts by
        // id, so a build whose instance ids moved regenerates every body.
        // Without reuse, the whole concrete set rechecks, every compile.
        let build = req.cmd == Cmd::Build;
        let regenerate_all = !gen_ok || (build && ids_moved);
        if regenerate_all {
            caches.inst_ids.clear();
        }
        if build && ids_moved {
            // Moved ids rename types and glue (`A<id>`, `drop_A<id>`):
            // the glue set and every unit object, the glue unit's
            // included, rebuild from the regenerated C. Comparing glue
            // text cannot see this: `W<u8>` and `W<u16>` share it.
            caches.glue = GlueSet::default();
            caches.objects = None;
        }
        let mut body_changed = vec![false; fn_count];
        for &i in &changed {
            if i < fn_count {
                body_changed[i] = true;
            }
        }
        let concrete = |i: usize| {
            matches!(
                program.gx.fn_class.get(i),
                Some(crate::check::generics::FnClass::Plain | crate::check::generics::FnClass::Instance | crate::check::generics::FnClass::Closure)
                    | None
            )
        };
        let reuse = &caches.gen_reuse;
        let env = gen_env.unwrap_or(0);
        let consts_moved = const_fn_changed || front.walked_const_fns != const_fns;
        let memo = &mut answers;
        // Slots some fn of this program holds. A body whose stored C
        // names any other slot rebuilds it: that callee's identity moved
        // to a new slot (a nested fn's body item index, when its parent
        // is not found) while this body's source stayed, as in
        // `slot_update` for AST fns.
        let mut held = vec![false; front.slot_of.len()];
        for &s in &front.fn_slot {
            if let Some(h) = held.get_mut(s as usize) {
                *h = true;
            }
        }
        // A body's C names only slots held when it was made, and every build remakes
        // the bodies whose C names a slot no fn holds. So unless a slot held at the
        // last build is lost (or slots were renumbered), no body calls a dead slot, and
        // the walk skips reading every body's used slots (each a block of its own).
        let lost = caches.held_slots.is_empty()
            || front.slots_renumbered
            || caches.held_slots.len() > held.len()
            || caches.held_slots.iter().zip(&held).any(|(&was, &is)| was && !is);
        // Each concrete fn's verdict; an instance or closure body fn whose
        // stored reads decide waits for one parallel walk over all of them
        // (`reads_dirty_par`).
        let mut recheck_of = vec![false; program.fns.len()];
        let mut by_reads: Vec<usize> = Vec::new();
        // The source fingerprint of each instance and closure body fn
        // (`src_of`: a few map lookups each, over every instance of the
        // program), in parallel; the verdicts below stay in fn order.
        let srcs: Vec<Option<u64>> = if regenerate_all {
            Vec::new()
        } else {
            let chunks: Vec<std::ops::Range<usize>> = (fn_count..program.fns.len()).step_by(4096).map(|a| a..(a + 4096).min(program.fns.len())).collect();
            par_map(&chunks, |r| r.clone().map(|i| if concrete(i) { reuse.src_of(&program, LocalDefId(i as u32)) } else { None }).collect::<Vec<_>>())
                .into_iter()
                .flatten()
                .collect()
        };
        for i in (0..program.fns.len()).filter(|&i| concrete(i)) {
            let s = front.fn_slot[i] as usize;
            let calls_dead = build && lost && caches.out[s].used.iter().any(|&u| !held.get(u as usize).copied().unwrap_or(false));
            let mut recheck = regenerate_all || !caches.ok[s] || (build && !caches.has_out[s]) || calls_dead;
            if !recheck && i < fn_count {
                recheck = body_changed[i];
            } else if !recheck {
                // An instance or closure body fn: its source (with what
                // it replays from its template or parent), then, if it
                // was checked under another item-level environment, its
                // reads (see gen_reuse.rs).
                // After a derive delta the keyed walk knows the dirty slots
                // (the oracle proves each clean one).
                let mut clean = |r: &crate::driver::graph::Reads, d: &Vec<bool>| {
                    let clean = !d.get(s).copied().unwrap_or(true);
                    if clean && super::item_oracle::on() && program.reads_dirty_memo(r, &caches.read_keys, memo) != 0 {
                        super::item_oracle::fail("clean instance body has dirty reads", visits.path, &i.to_string());
                    }
                    clean
                };
                recheck = srcs[i - fn_count] != Some(front.slot_hash[s]);
                // Const fn bodies are in `env` (`gen_env`): after a const fn
                // edit every slot checked before it asks its reads, and a check
                // makes no instances, so the next build asks theirs. Neither the
                // derive nor the keyed walk follows a moved value: while the
                // const fns differ from the last build's walk, the full read
                // check decides.
                if !recheck && front.slot_env[s] != env {
                    match (&caches.slot_reads[s], &derive_dirty) {
                        (None, _) => recheck = true,
                        (Some(_), _) if consts_moved => {
                            by_reads.push(i);
                            continue;
                        }
                        (Some(r), Some(d)) => recheck = !clean(r, d),
                        (Some(_), None) if keyed.as_ref().is_some_and(|k| matches!(k.get(s), Some(Some(_)))) => {
                            recheck = !keyed_clean(caches, s, memo, i);
                            visits.keyed += 1;
                        }
                        (Some(_), None) => {
                            by_reads.push(i);
                            continue;
                        }
                    }
                }
                if !recheck {
                    front.slot_env[s] = env;
                }
            }
            recheck_of[i] = recheck;
        }
        let sets: Vec<_> = by_reads.iter().map(|&i| caches.slot_reads[front.fn_slot[i] as usize].as_ref()).collect();
        for (&i, d) in by_reads.iter().zip(reads_dirty_par(&program, &sets, &caches.read_keys, &mut walk_answers)) {
            recheck_of[i] = d != Some(0);
            if !recheck_of[i] {
                front.slot_env[front.fn_slot[i] as usize] = env;
            }
        }
        work = (0..program.fns.len()).filter(|&i| recheck_of[i]).collect();
        if super::genreuse_oracle::on() {
            for i in fn_count..program.fns.len() {
                if !recheck_of[i]
                    && let Some(Some(r)) = caches.slot_reads.get(slot(i))
                {
                    super::genreuse_oracle::kept_reads("an instance or closure body", &program, LocalDefId(i as u32), r, &caches.read_keys, memo);
                }
            }
        }
        if build {
            caches.held_slots = held;
            front.walked_const_fns = const_fns;
        }
        // A recheck leaves the slot's C stale until codegen replaces
        // it; a check request, or a build that stops on errors, never
        // gets there.
        for &i in &work {
            caches.has_out[front.fn_slot[i] as usize] = false;
        }
    }
    t.lap("generic reuse walk");
    // This program's generation (`Program::verified`): every stored read
    // set this request does not check again holds against it now (the
    // walks above, or no candidate), and the checks below store theirs
    // with it, as this mode's mark. A set this request checks again keeps
    // its old marks until then (a skipped std body keeps them for good);
    // the other mode's mark stands while the set does. The program takes
    // the mark when it is kept. An error answer that leaves the put-back
    // program in place (`patch::keep_err`) gives these sets their old
    // marks back (`old_marks`): they held against that program before
    // this request and did not change, so the revert after a reject takes
    // the keyed walk.
    let verified = next_verified();
    let mode_at = usize::from(program.gx.walk_instances);
    let mut old_marks: Vec<(usize, u64)> = Vec::new();
    {
        let mut in_work = vec![false; program.fns.len()];
        work.iter().for_each(|&i| in_work[i] = true);
        for i in (0..program.fns.len()).filter(|&i| !in_work[i]) {
            if let Some(Some(r)) = caches.slot_reads.get_mut(slot(i)) {
                old_marks.push((slot(i), r.verified[mode_at]));
                r.verified[mode_at] = verified;
            }
        }
    }
    // A one-shot check needs no IR after borrowck: dropping each body on
    // its worker lets the allocator reuse the memory for the next body,
    // instead of touching fresh pages for every function.
    let keep_bodies = req.cmd == Cmd::Build || caches.persistent;
    // `lust check` skips std platform bodies (`Program::check_skips`).
    // A skipped slot keeps its last marks; one that needed a check lost
    // its C above, so the next build checks it.
    work.retain(|&i| !program.check_skips(LocalDefId(i as u32)));
    if super::item_oracle::on() {
        let (build, tables) = (req.cmd == Cmd::Build, resolved_tables.as_ref());
        let (lines, hashes) = (&fn_lines_all, &body_hashes_all);
        super::item_oracle::check(front, caches, Ok(&program), &work, fn_count, hashes, lines, visits.path, crate_ids, build, tables);
        t.lap("item oracle");
    }
    let results = par_map(&work, |&i| {
        let f = LocalDefId(i as u32);
        // Lowering and borrowck read derive lists too (Copy operands,
        // moves): their notes join the body's reads (check/derive_delta.rs).
        let ((body, errs), noted) = check::derive_delta::scoped(program.record_reads, || {
            let (checked, mut errs) = check::check_fn(&program, f);
            if !errs.is_empty() {
                return (None, errs);
            }
            let body = lower::lower(&program, f, checked);
            errs.extend(borrowck::borrowck(&program, &body));
            (Some(body), errs)
        });
        let body = body.filter(|_| keep_bodies).map(|mut b| {
            check::derive_delta::record(&program, &mut b.reads, &noted);
            b
        });
        (body, errs)
    });
    let mut diags: Vec<Diag> = Vec::new();
    for (k, &i) in work.iter().enumerate() {
        caches.ok[slot(i)] = results[k].1.is_empty();
        // An instance slot remembers the source and the environment it
        // was checked under.
        if i >= fn_count
            && let Some(src) = caches.gen_reuse.src_of(&program, LocalDefId(i as u32))
        {
            front.slot_hash[slot(i)] = src;
            if let Some(e) = front.slot_env.get_mut(slot(i)) {
                *e = gen_env.unwrap_or(0);
            }
        }
        // Store the read set with the result (section 8.2 rule 2): the
        // next signature-only edit replays it in the dirty walk above.
        // Only passing functions get one; a failing function always
        // rechecks (its `ok` is false), so it needs no read set. The
        // stored set gains a `Sig` read of the function itself: body
        // checking reads its own signature (parameter types bind the
        // locals, the return type coerces the tail) through the compat
        // `FnInfo` path, which records nothing, so this entry is the only
        // record of that read. `slot_update` already keeps a fn whose
        // own signature item changed out of the reuse candidates; the
        // read keeps the walk itself honest about the same edge.
        if caches.persistent
            && results[k].1.is_empty()
            && let Some(body) = &results[k].0
            && caches.slot_reads.get(slot(i)).is_some()
        {
            let mut stored = body.reads.clone();
            let _ = program.sig_of(&mut stored, program.def_id(LocalDefId(i as u32)));
            stored.freeze(&mut caches.read_keys);
            stored.verified[mode_at] = verified;
            caches.slot_reads[slot(i)] = Some(stored);
        }
        diags.extend(results[k].1.iter().cloned());
    }
    // rustc stops before monomorphization once a pre-mono check fails, so an
    // instance checked over an erroneous caller (an error-typed closure argument)
    // must not add cascade errors ahead of the real ones.
    if work.iter().enumerate().any(|(k, &i)| !results[k].1.is_empty() && !post_mono(&program, LocalDefId(i as u32))) {
        diags = work
            .iter()
            .enumerate()
            .filter(|&(_, &i)| !post_mono(&program, LocalDefId(i as u32)))
            .flat_map(|(k, _)| results[k].1.iter().cloned())
            .collect();
    }
    // A lust file is a bin crate, so check needs `main` too, as `rustc --emit=metadata`
    // does. `lust test` sets `harness`: it adds a generated `main` after this check.
    // A Cargo lib target (`--lib`) is a lib crate: rustc needs no `main` there.
    if !req.harness && req.session.krate.target_kind != "lib" && program.main.is_none() {
        diags.push(Diag::new("L0130", diag::Span::default(), "no `main` function", "Add `fn main() { ... }`."));
    }
    t.lap(if mode == "full" { "check+borrowck (par)" } else { "check changed fns (par)" });
    // A one-shot process (`leak_at_exit`) exits right after this call. Freeing the IR and
    // program arenas, mostly built on worker threads, costs about 10 ms on a 31k-line crate,
    // so leak them on every return below and let the OS reclaim the memory at exit. A
    // non-persistent session inside the daemon (the patch oracle's) must free them.
    let leak_at_exit = caches.leak_at_exit;
    if !diags.is_empty() {
        // The visits line for tests and logs only: an error answer must
        // stay the cold one, so stderr gets no stats.
        front.last_visits.clear();
        Visits { checked: work.len(), ..visits }.render(&mut front.last_visits);
        log_visits(&front.last_visits);
        let resp = errors(&mut diags, &map, &src, req);
        if leak_at_exit {
            std::mem::forget(results);
            std::mem::forget(program);
        } else {
            drop(results);
            program.verified = verified;
            if !super::patch::keep_err(front, program) {
                for (s, mark) in old_marks {
                    if let Some(Some(r)) = caches.slot_reads.get_mut(s) {
                        r.verified[mode_at] = mark;
                    }
                }
            }
        }
        return resp;
    }
    let mut resp = Response::default();
    if req.cmd == Cmd::Check {
        // The answer, before the timing and stats lines, for a no-op
        // check of the same request to reuse.
        if let Some(fp) = check_fp {
            front.last_check = Some((fp, resp.clone()));
        }
        if stats_on() {
            Stats {
                mode,
                fns: program.fns.len(),
                rechecked: work.len(),
                reused: reads_reused,
                invalidated: reads_invalidated,
                instances: front.fn_slot.len(),
                templates: generic_work(&caches.gen_reuse).0,
                discovered: generic_work(&caches.gen_reuse).1,
                ..Default::default()
            }
            .render(&mut resp.stderr);
        }
        front.last_visits.clear();
        Visits { checked: work.len(), ..visits }.render(&mut front.last_visits);
        if stats_on() {
            resp.stderr.push_str(&front.last_visits);
        }
        log_visits(&front.last_visits);
        if req.timings {
            let _ = writeln!(
                resp.stderr,
                "lust check {path}: ok ({} functions, {mode}: {} rechecked, {} reused by reads)",
                program.fns.len(),
                work.len(),
                reads_reused
            );
            t.render(&mut resp.stderr);
        }
        if leak_at_exit {
            std::mem::forget(results);
            std::mem::forget(program);
        } else {
            drop(results);
            program.verified = verified;
            super::patch::keep(front, program);
        }
        return resp;
    }

    // Codegen for the work set, plus any slot-moved re-emits rebuilt
    // from cached IR above.
    let mut bodies: Vec<(usize, ir::Body)> = work.iter().copied().zip(results).filter_map(|(i, r)| r.0.map(|b| (i, b))).collect();
    bodies.extend(reemit);
    // Each fn's base line: cgen stores its line numbers relative to it
    // and the main unit adds each slot's base back, so a reused body's
    // C stays right when its source text moves. An instance's base is
    // its source fn's line (`GenReuse::source`): the template's, a
    // closure's host fn's, or a trait default method's own first line.
    // Each fn's source file too (W-PANIC): a panic in a module file names that file. An
    // instance takes its source fn's file, as it takes its line. Both on the pool.
    let fn_ids: Vec<u32> = (0..program.fns.len() as u32).collect();
    let (line_bases, fn_files): (Vec<u32>, Vec<u32>) = par_map(&fn_ids, |&i| match caches.gen_reuse.source(&program, LocalDefId(i)) {
        Some(s) if (s.0 as usize) < fn_count => (scan_of(front, s.0 as usize).1, map.call_site(program.fn_def(s).name_span).file.0),
        Some(s) => {
            let at = map.call_site(program.fn_def(s).name_span);
            (map.line_col(at).0, at.file.0)
        }
        None => (0, ROOT_FILE.0),
    })
    .into_iter()
    .unzip();
    let line_base_of = |_: &Front, i: usize| -> u32 { line_bases.get(i).copied().unwrap_or(0) };
    // Release C (driver/release_c.rs): content-addressed names, set as cgen's naming
    // context around every step that prints C.
    let rnames = release.then(|| super::release_c::names(&program, &front.fn_slot, front.slot_of.len().max(caches.out.len()), &inst_adt_ids(&program)));
    let rn = rnames.as_ref();
    // A release C build to the release driver streams its cc step (`cc::Stream`): each unit the
    // assembly makes compiles from the time its text exists. Not with --emit-c nor LLVM units.
    // The stream starts on a thread of its own while codegen runs (its compiler check and warm
    // profile spawn a process and read files), joined before the assembly: the image save forks
    // after the assembly and must find no other thread.
    let stream_start = (release && req.cc && req.emit_c.is_none() && !cgen::names::with(rn, || cgen::ll::on(&program))).then(|| {
        let triple = if req.session.target_triple.is_empty() {
            crate::protocol::host_triple().to_string()
        } else {
            req.session.target_triple.clone()
        };
        let (debug, cache, work) = (req.debug, crate::driver::cache::Cache::open(&req.file), caches.obj_dir.join("cc"));
        std::thread::spawn(move || crate::cc::Stream::start(&triple, debug, cache, work))
    });
    // Codegen reads derive lists (Copy layouts, comparison forms, default
    // variants): its notes join the slot's read set below, as the check's
    // do (check/derive_delta.rs), so a derive edit regenerates just the
    // slots that read the list.
    // One codegen phase: `c_layout` keeps its answers per thread, and the new
    // FnOuts share their extern declarations.
    let layout_tag = cgen::layout_phase();
    cgen::clear_extern_pool();
    let (outs, cg_noted): (Vec<_>, Vec<_>) = par_map(&bodies, |(i, b)| {
        check::derive_delta::scoped(program.record_reads, || {
            cgen::in_layout_phase(layout_tag, || {
                cgen::names::with(rn, || cgen::gen_fn(&program, b, &map, line_base_of(front, *i), &front.fn_slot))
            })
        })
    })
    .into_iter()
    .unzip();
    if let Some(e) = outs.iter().find_map(|o| o.error.clone()) {
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    let n_slots = caches.out.len();
    // Slots with new C in this build. Their groups are marked dirty
    // after grouping below (grouping needs the new C sizes first).
    let mut dirty_slots: Vec<usize> = Vec::new();
    // A slot a compile wiped (a removed fn, a dead instance) still
    // has its old C in its unit's object: reassemble that unit so
    // the dead C (and any symbol only it named) leaves the link.
    dirty_slots.extend(std::mem::take(&mut caches.wiped_slots).into_iter().map(|s| s as usize));
    let mut file_hashes: FxMap<FileId, u64> = FxMap::default();
    // Cached IR serves only the slot-moved re-emit, which runs only in a
    // program with no generics: a generic program caches none (on tsgo it
    // was 1.5 GB of a daemon session, made serially per generated body).
    let keep_ir = !program.gx.has_generics;
    // The stable id of each fn whose slot the new C prints (`FnOut::used`),
    // by slot: the pairs below are the next renumber's re-emit trigger.
    let mut wanted = vec![false; if keep_ir { front.slot_of.len() } else { 0 }];
    outs.iter().filter(|_| keep_ir).flat_map(|o| &o.used).for_each(|&u| wanted[u as usize] = true);
    let disk_at: FxMap<u32, DiskDefId> = (front.fn_slot.iter().enumerate())
        .filter(|&(_, &u)| wanted.get(u as usize).copied().unwrap_or(false))
        .map(|(l, &u)| (u, program.disk_id(LocalDefId(l as u32))))
        .collect();
    for ((i, _), noted) in bodies.iter().zip(&cg_noted) {
        if !noted.is_empty()
            && let Some(Some(r)) = caches.slot_reads.get_mut(slot(*i))
        {
            r.thaw(&caches.read_keys);
            check::derive_delta::record(&program, r, noted);
            r.freeze(&mut caches.read_keys);
        }
    }
    for ((i, body), out) in bodies.iter().zip(outs) {
        let s = slot(*i);
        // The IR fingerprint a slot-moved re-emit checks its rebuilt
        // body against (see `ir_cache::CachedBody`).
        let cached = keep_ir.then(|| {
            let base_line = line_base_of(front, *i);
            let fp = super::ir_cache::ir_fingerprint(&program, body, &map, base_line);
            let used_pairs: Vec<(DiskDefId, u32)> = out.used.iter().filter_map(|&u| Some((*disk_at.get(&u)?, u))).collect();
            let file = program.fn_def(LocalDefId(*i as u32)).name_span.file;
            let fh = *file_hashes.entry(file).or_insert_with(|| file_text_hash(&map, file));
            super::ir_cache::cache_body(&program, body, fh, s as u32, used_pairs, fp)
        });
        caches.out[s] = out;
        caches.has_out[s] = true;
        dirty_slots.push(s);
        if let Some(slot_ir) = caches.slot_ir.get_mut(s) {
            *slot_ir = cached;
        }
    }
    // LUST_CHECK_GENREUSE=1 (genreuse_oracle.rs): every concrete body a release C build keeps
    // is checked, lowered and generated again without reuse (nothing stored), and its C must
    // equal the kept C. Release C names are content-addressed; dev C names a vtable by a
    // session number, which a body made again may not take.
    if super::genreuse_oracle::on() && req.cmd == Cmd::Build && release {
        let mut made = vec![false; program.fns.len()];
        bodies.iter().for_each(|(i, _)| made[*i] = true);
        let kept: Vec<usize> = (0..program.fns.len())
            .filter(|&i| !made[i] && caches.has_out.get(slot(i)) == Some(&true))
            .filter(|&i| {
                use crate::check::generics::FnClass as C;
                matches!(program.gx.fn_class.get(i), Some(C::Plain | C::Instance | C::Closure) | None)
            })
            .collect();
        let fresh = par_map(&kept, |&i| {
            let f = LocalDefId(i as u32);
            let ((checked, errs), _) = check::derive_delta::scoped(program.record_reads, || check::check_fn(&program, f));
            if !errs.is_empty() {
                return Err(errs[0].message.clone());
            }
            let body = lower::lower(&program, f, checked);
            let out = cgen::in_layout_phase(layout_tag, || {
                cgen::names::with(rn, || cgen::gen_fn(&program, &body, &map, line_base_of(front, i), &front.fn_slot))
            });
            Ok([out.code_text().into_owned(), out.ll, out.ll_c])
        });
        super::genreuse_oracle::compare_bodies(&program, visits.path, &kept, fresh, |i| {
            let o = &caches.out[slot(i)];
            [o.code_text().into_owned(), o.ll.clone(), o.ll_c.clone()]
        });
    }
    // The phase is over: the pool's tables and its references would otherwise stay until the
    // next phase, and a front image save would write them where no later process reaches them
    // (60 MB of a cold tsgo image).
    cgen::clear_extern_pool();
    // Group slots into function units by C bytes (see
    // `Caches::groups`): regroup all on a fresh base (or when the
    // frozen groups no longer cover the slots exactly, after a
    // renumber); otherwise keep the frozen groups and group only
    // the new slots at the end. The byte target is picked once,
    // from the total C size: a one-shot build wants about two units
    // per core (enough units for the bounded tcc workers to stay
    // balanced, few enough that per-unit header cost stays small);
    // a daemon keeps units smaller, about four per core, so a warm
    // edit recompiles little code.
    let covered = caches.groups.last().map_or(0, |g| g.end);
    if caches.groups.is_empty() || covered > n_slots || caches.objects != Some(req.debug) || !caches.persistent {
        let sizes: Vec<usize> = caches.out.iter().map(FnOut::code_len).collect();
        if caches.unit_bytes == 0 {
            let cores = crate::pool::threads().max(1);
            let total: usize = sizes.iter().sum();
            caches.unit_bytes = if caches.persistent {
                (total / (cores * 4)).clamp(48 * 1024, 384 * 1024)
            } else {
                (total / (cores * 2)).clamp(64 * 1024, 768 * 1024)
            };
        }
        caches.groups = cgen::group_fns_by_bytes(&sizes, caches.unit_bytes);
    } else if covered < n_slots {
        let sizes: Vec<usize> = caches.out[covered..].iter().map(FnOut::code_len).collect();
        let target = if caches.unit_bytes == 0 { 128 * 1024 } else { caches.unit_bytes };
        caches.groups.extend(cgen::group_fns_by_bytes(&sizes, target).into_iter().map(|r| (r.start + covered)..(r.end + covered)));
    }
    let groups = caches.groups.clone();
    let mut group_of = vec![usize::MAX; n_slots];
    for (g, range) in groups.iter().enumerate() {
        for s in range.clone() {
            group_of[s] = g;
        }
    }
    let mut dirty_groups = vec![false; groups.len()];
    for s in dirty_slots {
        if let Some(&g) = group_of.get(s)
            && let Some(d) = dirty_groups.get_mut(g)
        {
            *d = true;
        }
    }
    // Every live slot's C of a generic program is now under these ids
    // (moved ids regenerated all of it above).
    caches.inst_ids.extend(inst_ids);
    // Derived glue (Debug, Clone, Eq, Drop) is keyed by Adt id but
    // generated from field and variant types, and the glue unit also
    // holds the statics. Regenerate every live glue definition and
    // compare text when a compile since the last build saw a
    // full-mode or const fn edit (`glue_stale`, set above), or this
    // build will reassemble a fresh base anyway (`objects` mismatch:
    // first build, a carried-over non-fn change, an error reset). A
    // changed definition forces a fresh base so fn units that carry
    // static copies reassemble too. The statics compare against the
    // fingerprint last built into the glue unit, so a value edit
    // consumed by an earlier check request still rebuilds it here.
    // Release C has a statics unit of its own, made every build, and no glue unit: it skips the
    // fingerprint (10 ms for tsgo), which then stays the glue unit's last one.
    let statics_changed = !release && {
        let statics_fp = crate::driver::graph::statics_fingerprint(&program);
        std::mem::replace(&mut caches.statics_fp, statics_fp) != statics_fp
    };
    // Glue an earlier refresh did not reach (no live body used it then)
    // is stale in the set; `add` regenerates it when a body reaches it
    // again, with the same fresh-base rule.
    // Glue that calls a written `fmt` or `drop` method names the
    // method instance's slot. A bodies-mode build can move that
    // instance to a new slot (or point the Adt at another instance);
    // the old glue then calls an empty slot (a run-time segfault,
    // W-STD-C daemon probes). Refresh the glue when those slots move.
    let glue_slots_fp = crate::driver::graph::glue_method_slots_fp(&program, &front.fn_slot);
    // Glue whose text prints a slot no fn holds now (its callee's identity
    // moved to a new slot) refreshes the same way.
    let mut held = vec![false; front.slot_of.len()];
    front.fn_slot.iter().for_each(|&s| held[s as usize] = true);
    let glue_slots_changed =
        caches.glue_slots_fp != glue_slots_fp || caches.glue.prints_slot(|s| !held.get(s as usize).copied().unwrap_or(false));
    caches.glue_slots_fp = glue_slots_fp;
    let (shared_changed, regenerated) = if caches.glue_stale || glue_slots_changed || caches.objects != Some(req.debug) {
        caches.glue_stale = false;
        cgen::names::with(rn, || caches.glue.refresh(&program, &front.fn_slot, caches.out.iter().flat_map(|o| o.glue.iter())))
    } else {
        cgen::names::with(rn, || caches.glue.add(&program, &front.fn_slot, bodies.iter().flat_map(|(i, _)| caches.out[slot(*i)].glue.iter())))
    };
    if regenerated {
        caches.objects = None;
    }
    let glue_changed = shared_changed || regenerated || statics_changed;
    t.lap("codegen (par)");
    // Nothing reads the IR after codegen. A one-shot build leaks it at exit
    // (`leak_at_exit`), but on a large program it is the largest block
    // alive at the peak (ts-rust's bins: about 2.4 GB of 9.4 GB, through
    // tcc and the link), so a large build frees it now, in chunks on the
    // pool (one thread took 0.3 s on tsgo).
    let n_bodies = bodies.len();
    let bodies = if leak_at_exit && n_bodies >= 10_000 {
        let per = n_bodies.div_ceil(crate::pool::threads().max(1) * 4);
        let mut chunks: Vec<std::sync::Mutex<Vec<(usize, ir::Body)>>> = Vec::new();
        let mut rest = bodies.into_iter();
        loop {
            let chunk: Vec<(usize, ir::Body)> = rest.by_ref().take(per).collect();
            if chunk.is_empty() {
                break;
            }
            chunks.push(std::sync::Mutex::new(chunk));
        }
        par_map(&chunks, |c| drop(std::mem::take(&mut *c.lock().unwrap_or_else(|e| e.into_inner()))));
        t.lap("free IR");
        Vec::new()
    } else {
        bodies
    };

    // Units: 0 = main (always rebuilt), 1 = glue, 2 = runtime, 3 = function table, 4 = location
    // tables, 5.. = function groups. A cold build links them all statically. The daemon links
    // everything but main into libbase.so once, then each edit compiles only "overlay" copies of
    // the changed units and links a small executable that loads libbase.so and swaps the new
    // functions into `lust_fns`. The location unit overlays like glue: only a build whose slot
    // lines or files changed recompiles it.
    const FIRST_FN_UNIT: usize = 5;
    const LOC_UNIT: usize = 4;
    const MAX_OVERLAYS: usize = 32;
    // B1: the prefix of a release C glue shard's record name (`Caches::unit_records`).
    const SHARD_RECORD: &str = "glue shard ";
    let fn_units: Vec<usize> = (0..groups.len()).map(|g| g + FIRST_FN_UNIT).collect();
    let dirty_fn_units: Vec<usize> = (0..groups.len()).filter(|&g| dirty_groups[g]).map(|g| g + FIRST_FN_UNIT).collect();
    let main_slot = front.fn_slot[program.main.unwrap().0 as usize];
    // Instance slots take their template's line: cgen stores an
    // instance's panic lines relative to it (see `line_base_of`).
    let mut slot_lines = vec![0u32; n_slots];
    let mut slot_files = vec![ROOT_FILE.0; n_slots];
    for i in 0..front.fn_slot.len().min(program.fns.len()) {
        slot_lines[slot(i)] = line_base_of(front, i);
        slot_files[slot(i)] = fn_files[i];
    }
    let library = crate::resolve::adapters::library_root();
    let file_paths: Vec<String> =
        (0..map.file_count()).map(|f| location_path(map.path(FileId(f as u32)), &library, front.display_root.as_deref(), &front.client)).collect();
    let file_refs: Vec<&str> = file_paths.iter().map(String::as_str).collect();
    let files = cgen::SlotFiles { paths: &file_refs, of_slot: &slot_files };
    // The location unit rebuilds only when its tables change (see
    // `Caches::loc_fp`): most warm edits keep every slot's line.
    let loc_fp = {
        use std::hash::Hash as _;
        let mut h = crate::intern::FxHasher::default();
        slot_lines.hash(&mut h);
        slot_files.hash(&mut h);
        file_paths.hash(&mut h);
        std::hash::Hasher::finish(&h)
    };
    let loc_changed = caches.loc_fp != loc_fp;
    caches.loc_fp = loc_fp;
    // A fresh base: no base yet under this debug setting, or a one-shot
    // (static) build. Growth no longer forces one (section 4.2): when
    // slots outgrow the table capacity or a new fn unit appears, only
    // the table unit (whose C is the capacity plus the unit list)
    // rebuilds and the base
    // relinks over the existing unit objects. Unrelated units keep
    // their objects, in the session and in the disk unit cache.
    let fresh_base = caches.objects != Some(req.debug) || !caches.persistent;
    let cap_grown = n_slots > caches.table_cap;
    if fresh_base || cap_grown {
        caches.table_cap = n_slots * 2 + 64;
    }
    if fresh_base {
        caches.base_units = groups.len();
    }
    let table_dirty = cap_grown || groups.len() != caches.base_units;
    let rebuild_base = fresh_base || table_dirty || caches.overlays.len() + dirty_fn_units.len() > MAX_OVERLAYS;
    let dir = caches.obj_dir.clone();
    let base_obj = |u: usize| dir.join(format!("u{u}.o"));
    let overlay_obj = |u: usize| dir.join(format!("o{u}.o"));
    // (unit, overlay?) pairs to compile now.
    let mut todo: Vec<(usize, bool)> = Vec::new();
    if rebuild_base {
        // Everything not yet in the base goes in: all units on a fresh base, else the overlays.
        if fresh_base {
            todo.extend([(1, false), (2, false), (3, false), (LOC_UNIT, false)]);
            todo.extend(fn_units.iter().map(|&u| (u, false)));
        } else {
            let mut units: Vec<usize> = caches.overlays.iter().copied().chain(dirty_fn_units.iter().copied()).collect();
            // A unit new since the last base has no object yet, dirty or
            // not: one that holds only template or stub slots gets no
            // fresh C, but the base links every unit.
            units.extend(fn_units.iter().copied().filter(|&u| u >= FIRST_FN_UNIT + caches.base_units));
            units.sort_unstable();
            units.dedup();
            todo.extend(units.into_iter().map(|u| (u, false)));
            if glue_changed && !todo.contains(&(1, false)) {
                todo.push((1, false));
            }
            if table_dirty && !todo.contains(&(3, false)) {
                todo.push((3, false));
            }
            if loc_changed && !todo.contains(&(LOC_UNIT, false)) {
                todo.push((LOC_UNIT, false));
            }
            // The relinked base now registers every current unit.
            caches.base_units = groups.len();
        }
        caches.overlays.clear();
    } else {
        caches.overlays.extend(dirty_fn_units.iter().copied());
        todo.extend(dirty_fn_units.iter().map(|&u| (u, true)));
        if glue_changed {
            caches.overlays.insert(1);
            todo.push((1, true));
        }
        if loc_changed {
            caches.overlays.insert(LOC_UNIT);
            todo.push((LOC_UNIT, true));
        }
    }
    let registered: Vec<usize> = caches.overlays.iter().copied().filter(|&u| u >= FIRST_FN_UNIT).collect();
    todo.push((0, false));
    // Hybrid glue: glue reached by 3 or more units stays in the shared glue unit, the rest is
    // static per unit. The set is frozen until the next fresh base (see cgen::GlueSet). The
    // glue unit's C is built below, only when unit 1 is in `todo`.
    // Release C sets its own shared set below, so it skips this count.
    if rnames.is_none() && (fresh_base || caches.glue.shared.is_none()) {
        caches.glue.compute_shared(&caches.out, &groups, 3);
    }
    // Release C: every glue key is shared (fn units hold its prototype, `glue_shards`
    // its definition: a set that follows the grouping would move with it), and the fn
    // units are `release_c::groups`. B1's Glue reads and every unit's switches read the
    // shared set, so it is set first.
    // With LUST_B1_OBSERVE=1 or LUST_ASM_PARTS=1, the parts of release C assembly (ms from
    // here to when this thread has each result): groups, glue shards, B1 before with the C
    // units and inline sets, C refs, fn units, B1 after, the rest.
    let t_asm = Instant::now();
    let mut asm_ms = [0f64; 7];
    if rnames.is_some() {
        caches.glue.shared = Some(caches.glue.protos.keys().cloned().collect());
    }
    // Release C's fn units, cut beside the statics unit, the glue shard cut and B1's
    // fingerprints (below); `rgroups` after the assembly.
    let rg_cell: std::sync::OnceLock<Vec<(String, Vec<usize>)>> = std::sync::OnceLock::new();
    let cut_fn_units = |names: &cgen::names::Names| {
        let mut file = vec![String::new(); caches.out.len()];
        let mut line = vec![0u32; caches.out.len()];
        for i in 0..front.fn_slot.len().min(program.fns.len()) {
            let s = slot(i);
            if let (Some(f), Some(l)) = (file.get_mut(s), line.get_mut(s)) {
                *f = fn_files.get(i).and_then(|&f| file_paths.get(f as usize)).cloned().unwrap_or_default();
                *l = line_base_of(front, i);
            }
        }
        super::release_c::groups(&caches.out, names, &file, &line)
    };
    let gen_unit = |u: usize, overlay: bool| match u {
        0 => cgen::main_unit(main_slot, &registered, cgen::unwind_init(&program, |f| front.fn_slot[f.0 as usize])),
        1 => cgen::glue_unit(&program, &caches.glue),
        2 => cgen::runtime_unit(),
        3 => cgen::table_unit(caches.table_cap, &fn_units),
        LOC_UNIT => cgen::loc_unit(&files, &slot_lines),
        g => {
            let register = if overlay { format!("lust_overlay_u{g}") } else { format!("lust_register_u{g}") };
            cgen::fn_unit(&program, &caches.out, &groups[g - FIRST_FN_UNIT].clone().collect::<Vec<_>>(), &caches.glue, &register, Some(main_slot))
        }
    };
    // Release C: whether fn bodies are LLVM IR (cgen/ll.rs), and B1's switches.
    let llvm_on = cgen::names::with(rn, || cgen::ll::on(&program));
    // B1 (`cgen::record`): each C fn unit records the pieces it is made of and what it
    // read, and the next build sets the record against its program
    // (`Caches::unit_records`). A session that keeps its caches (a daemon, a front
    // image) skips the assembly of a unit whose reads all kept their fingerprints and
    // whose object the unit memo holds (`cc::memo_misses`): cc takes its fingerprint and
    // no text (LUST_B1=0 turns it off). Not with --emit-c (it writes every unit) nor for
    // LLVM units (never recorded). LUST_CHECK_UNIT_FP=1 is the oracle: every unit
    // assembles, a unit clean by its reads must have the same pieces, and cc's memo the
    // same key for its fingerprint. LUST_B1_OBSERVE=1 prints the counts.
    let b1_observe = std::env::var_os("LUST_B1_OBSERVE").is_some_and(|v| v == "1");
    let b1_check = !llvm_on && std::env::var_os("LUST_CHECK_UNIT_FP").is_some_and(|v| v == "1");
    let b1_skip = !llvm_on
        && !b1_check
        && caches.persistent
        && req.cc
        && req.emit_c.is_none()
        && std::env::var_os("LUST_B1").is_none_or(|v| v != "0");
    let b1_record = b1_observe || b1_check || b1_skip;
    // B1's memo pre-check (`cc::memo_misses`) reads the unit memo (10 MB for tsgo), stats each
    // unit's object and, for the memo's tag, asks the compiler its version: 60-90 ms on a boat
    // box with the page cache dropped, more on a CI job's cold disk, and the fn units waited
    // for it. It starts here on a thread of its own, beside both cuts and B1's fingerprints,
    // for every unit the last build recorded (which of them are clean is known only then), by
    // its record name (fn units and glue shards get their unit numbers from the cuts); the
    // statics record's units by `statics_unit_name`.
    let mut b1_memo = Joined(match rnames {
        Some(_) if b1_skip && !caches.unit_records.is_empty() => {
            let bare: Vec<crate::cc::UnitIn> = caches
                .unit_records
                .iter()
                .flat_map(|(reg, r)| {
                    let units: Vec<(String, u128)> = if reg == STATICS_RECORD {
                        (0..=caches.statics_parts).map(|k| (statics_unit_name(k), statics_unit_fp(r.fp, k))).collect()
                    } else {
                        vec![(reg.clone(), r.fp)]
                    };
                    units.into_iter().map(|(name, fp)| crate::cc::UnitIn { name, fp: Some(fp), text: None })
                })
                .collect();
            let triple = if req.session.target_triple.is_empty() { crate::protocol::host_triple().to_string() } else { req.session.target_triple.clone() };
            let (file, debug, work) = (req.file.clone(), req.debug, dir.join("cc"));
            Some(std::thread::spawn(move || -> std::collections::HashSet<String> {
                match crate::cc::spec_for(&triple) {
                    Ok(spec) => crate::cc::memo_misses(&bare, &spec, debug, crate::driver::cache::Cache::open(&file).as_ref(), &work).into_iter().collect(),
                    Err(_) => bare.into_iter().map(|u| u.name).collect(),
                }
            }))
        }
        _ => None,
    });
    // The cc stream, started during codegen (above).
    let stream = stream_start.and_then(|h| h.join().ok()).flatten();
    // Release C glue shards come after the fn units (`link_fn_units` counts both). Their cut
    // and their texts are made beside the statics unit (below).
    let mut n_shards = 0usize;
    let mut rshards: Vec<String> = Vec::new();
    // B1 (below): the release C fn units cc takes with a fingerprint, by unit name, and whether
    // without text (a skipped assembly).
    let mut b1_units: FxMap<String, (u128, bool)> = FxMap::default();
    let mut b1_line: Option<String> = None;
    // Release C statics in parts (`cgen::names::statics_parts`): unit 1 is their index, and the
    // parts come after the glue shards.
    let mut n_statics = 0usize;
    let mut units: Vec<(PathBuf, String)> = match rn {
        None => par_map(&todo, |&(u, overlay)| (if overlay { overlay_obj(u) } else { base_obj(u) }, gen_unit(u, overlay))),
        Some(names) => {
            let statics_out: std::sync::Mutex<Vec<String>> = Default::default();
            // The parts' first unit number, sent when both cuts are done (below). The statics
            // unit's thread waits for it only once its parts are made.
            let (first_tx, first_rx) = std::sync::mpsc::channel::<usize>();
            let first_rx = std::sync::Mutex::new(first_rx);
            // Cross-unit inlining for the LLVM backend (cgen/ll.rs `ll_inline_set`): per fn
            // unit, the small fns of other units it gets a copy of (C fns have none).
            let slot_of: std::collections::HashMap<&str, usize> =
                if llvm_on { names.fns.iter().enumerate().filter_map(|(s, id)| id.as_deref().map(|id| (id, s))).collect() } else { Default::default() };
            // One layout phase (cgen `in_layout_phase`): the program is frozen, so each
            // worker keeps its `c_layout` answers across the units it assembles.
            let asm_tag = cgen::layout_phase();
            // The LLVM backend: C that calls an LLVM fn through its C ABI wrapper gets the
            // wrapper inline (`cgen::ll::Adapters`); an LLVM unit's own wrappers stay external.
            let adapters = if llvm_on { cgen::ll::Adapters::new(&caches.out) } else { None };
            let adapt = |text: String, own: &std::collections::HashSet<u64>| match adapters.as_ref().and_then(|a| a.adapt(&text, |id| own.contains(&id))) {
                Some(t) => t,
                None => text,
            };
            type B1Rec = (usize, Option<((u64, u64), Vec<cgen::record::Read>)>);
            let b1_records: std::sync::Mutex<Vec<B1Rec>> = Default::default();
            // With LUST_B1_OBSERVE=1, where B1's own time goes (ms): the statics' declarations,
            // the last build's reads into shards, the clean test, the memo pre-check, the new
            // reads, the new records.
            let mut b1_ms = [0f64; 6];
            let t_b1 = Instant::now();
            let b1_statics = b1_record.then(|| cgen::names::with(rn, || cgen::static_decl_map(&program))).unwrap_or_default();
            b1_ms[0] = t_b1.elapsed().as_secs_f64() * 1e3;
            // With LUST_B1_OBSERVE=1, the workers' time per read kind (Fn, SlotOf, Glue, Type,
            // Static, Main, Pick) and the count of each.
            let kind_ns: [std::sync::atomic::AtomicU64; 14] = Default::default();
            // The last build's distinct reads fingerprint in parts, several per thread.
            let b1_shards = crate::pool::threads().max(1) * 4;
            // With LUST_ASM_PARTS=1 (or B1 observed), each C unit's time (units 0 to 4).
            let c_unit_ms: [std::sync::atomic::AtomicU64; 5] = Default::default();
            // B1 for the release statics in parts (C units only): one record for the whole pass
            // (`cgen::names::statics_parts`), its index (unit 1) and every part, kept here when the
            // pass is made.
            let statics_b1 = b1_record && !llvm_on && super::release_c::statics_bytes() > 0;
            let statics_rec: std::sync::Mutex<cgen::names::StaticsRecord> = Default::default();
            // The switches every unit reads: every LUST_* knob but paths (the sources' ready file
            // too), B1's own, the cc stream's (`cc::Stream` changes no unit's text) and the front
            // image's (LUST_FRONT_*: image mechanics, never codegen, and new ones must stay so; the
            // image's compaction rebuild runs with other ones, and its records must hold for the
            // next build), and `cgen::unit_switches`. Fn units and glue shards add the copies
            // profile (`b1_switches`).
            let b1_base = b1_record.then(|| {
                let mut vars: Vec<(String, String)> = std::env::vars()
                    .filter(|(k, _)| {
                        k.starts_with("LUST_")
                            && !k.starts_with("LUST_FRONT_")
                            && !["DIR", "STATE", "SOCKET", "_FD", "_PID", "ARENA", "HOME", "_IDS", "B1", "UNIT_FP", "CC_STREAM", "SOURCES_READY"].iter().any(|x| k.contains(x))
                    })
                    .collect();
                vars.sort();
                let vars: Vec<String> = vars.into_iter().map(|(k, v)| format!("{k}={v}")).collect();
                format!("{}\n{}", vars.join("\n"), cgen::names::with(rn, || cgen::unit_switches(&program, &caches.glue)))
            });
            // The statics pass's identity: its record name, those switches and the compiler build.
            let statics_id =
                crate::driver::cache::hash128(&[STATICS_RECORD.as_bytes(), b1_base.as_deref().unwrap_or("").as_bytes(), env!("LUST_BUILD_HASH").as_bytes()], 18);
            // A read of the statics record now (`cgen::read_fp`; the record reads no copies set).
            let statics_read_fp =
                |r: &cgen::record::Read| cgen::in_layout_phase(asm_tag, || cgen::names::with(rn, || cgen::read_fp(&program, &caches.out, &caches.glue, &b1_statics, None, r)));
            // The last build's record of the pass, when it has this identity: its fingerprint and its
            // reads with theirs, owned (the statics thread runs beside the jobs that change B1's
            // records).
            let statics_old: Option<(u128, Vec<(cgen::record::Read, (u64, u64))>)> = statics_b1
                .then(|| caches.unit_records.get(STATICS_RECORD).filter(|r| r.id == statics_id))
                .flatten()
                .map(|r| (r.fp, r.reads.iter().map(|&(i, f)| (caches.unit_reads.get(i).clone(), f)).collect()));
            // Its fingerprint, which stands for every unit of the pass, when its reads kept theirs:
            // the statics' content (`content`, now) first, which ends the test when it moved, then
            // the rest on all cores.
            let statics_clean = |content: (u64, u64)| -> Option<u128> {
                let (fp, reads) = statics_old.as_ref()?;
                if !reads.iter().any(|(r, f)| *r == cgen::record::Read::Statics && *f == content) {
                    return None;
                }
                let rest: Vec<&(cgen::record::Read, (u64, u64))> = reads.iter().filter(|(r, _)| *r != cgen::record::Read::Statics).collect();
                let chunks: Vec<&[&(cgen::record::Read, (u64, u64))]> = rest.chunks(64).collect();
                par_map(&chunks, |c| c.iter().all(|(r, f)| statics_read_fp(r) == *f)).into_iter().all(|same| same).then_some(*fp)
            };
            // One unit's C, added to the cc stream. Only fn units read the copies set (`copy_hot`).
            let assemble = |u: usize, inl: &[Vec<usize>], c_refs: Option<&cgen::ll::CRefs>, copy_hot: Option<&cgen::CopyHot>| {
                let t = Instant::now();
                let (c, helpers) = cgen::in_layout_phase(asm_tag, || cgen::names::with(rn, || match u {
                    0 => (cgen::main_unit(main_slot, &[], cgen::unwind_init(&program, |f| front.fn_slot[f.0 as usize])), String::new()),
                    1 => match super::release_c::statics_bytes() {
                        0 => (adapt(cgen::names::statics_unit(&program, &caches.glue), &Default::default()), String::new()),
                        target => {
                            let (index, parts, rec) = cgen::names::statics_parts(&program, &caches.glue, target, statics_b1);
                            *statics_rec.lock().unwrap_or_else(|e| e.into_inner()) = rec;
                            let parts: Vec<String> = parts.into_iter().map(|t| adapt(t, &Default::default())).collect();
                            if let Some(s) = &stream
                                && let Ok(first) = first_rx.lock().unwrap_or_else(|e| e.into_inner()).recv()
                            {
                                par_map(&(0..parts.len()).collect::<Vec<_>>(), |&j| s.add(&format!("u{}", first + j), &parts[j]));
                            }
                            *statics_out.lock().unwrap_or_else(|e| e.into_inner()) = parts;
                            (adapt(index, &Default::default()), String::new())
                        }
                    },
                    2 => (cgen::runtime_unit(), String::new()),
                    3 => {
                        let rg = rg_cell.get().expect("the fn units are cut before unit 3");
                        (super::release_c::table_unit(&rg.iter().filter(|(_, s)| s.contains(&(main_slot as usize))).map(|(r, _)| r.clone()).collect::<Vec<_>>()), String::new())
                    }
                    LOC_UNIT => {
                        let live: Vec<u32> = (0..caches.out.len()).filter(|&s| caches.out[s].has_code()).map(|s| s as u32).collect();
                        (cgen::names::loc_unit(&live, &files, &slot_lines, super::release_c::elf_target(&req.session.target_triple)), String::new())
                    }
                    g => {
                        let (reg, slots) = &rg_cell.get().expect("the fn units are cut before they assemble")[g - FIRST_FN_UNIT];
                        if b1_record {
                            cgen::record::open();
                        }
                        let (c, h) = cgen::fn_unit_parts(&program, &caches.out, slots, &inl[g - FIRST_FN_UNIT], &caches.glue, reg, Some(main_slot), c_refs, copy_hot);
                        if b1_record {
                            let rec = cgen::record::close(&c);
                            b1_records.lock().unwrap_or_else(|e| e.into_inner()).push((g - FIRST_FN_UNIT, rec));
                        }
                        if adapters.is_none() {
                            return (c, h);
                        }
                        // An LLVM unit's C defines its own fns' wrappers (external).
                        let own = slots.iter().filter_map(|&s| cgen::names::fn_tag_opt(s as u32)).filter_map(|id| u64::from_str_radix(&id, 16).ok()).collect();
                        (adapt(c, &own), adapt(h, &own))
                    }
                }));
                if let Some(ms) = c_unit_ms.get(u) {
                    ms.store(t.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
                }
                if let Some(s) = &stream {
                    s.add(&format!("u{u}"), &c);
                }
                (base_obj(u), c, helpers)
            };
            // The LLVM backend: an LLVM fn's C is its C ABI wrapper and trampoline, which only
            // C calls (`fl_<id>` is what IR and helpers call), so a unit keeps them only when a
            // text names them (`cgen::ll::CRefs`): the C units and glue shards, and every fn's
            // helpers' C. `main`'s is always kept (the termination entry calls it).
            // The C units (the statics unit is the slow one) and the inline sets, together.
            // With a profile, the copies are of the fns it saw hot (`LUST_LL_COPY_MIN=<count>`,
            // default 100000; 0: every callee the rule allows). tsgo, warm merges 4-12 against
            // release C: +11.5% at 1000, +3.7% at 100000, run speed the same.
            let copy_min: u64 = std::env::var("LUST_LL_COPY_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(100_000);
            let hot = (llvm_on && copy_min > 0).then(|| crate::cc::pgo::hot_ids(&dir.join("cc"), copy_min).ok().flatten()).flatten();
            // The statics unit is one long job (~150-300 ms for tsgo). With C units only (no copy
            // sets, and no C refs read from its text) it assembles on a thread of its own from the
            // start, before the copies set is read and beside both cuts and every other part of the
            // assembly below, not before the fn units: on a build with few changes it ended the
            // assembly.
            let late_statics = !llvm_on;
            // With C units only, main, runtime and locations assemble beside the cuts (they need
            // neither), the table unit after the fn units' cut (it names their units), and there
            // is no inline set to make; with LLVM units, the C units and the inline sets are one
            // pass after the cuts.
            let early: Vec<usize> = if late_statics { vec![0, 2, LOC_UNIT] } else { vec![0, 1, 2, 3, LOC_UNIT] };
            let n_early = if late_statics { 0 } else { early.len() };
            let assembled: Result<Vec<(PathBuf, String)>, String> = std::thread::scope(|sc| {
                // Moved in: should a cut panic, the sender drops as this unwinds, and the statics
                // thread's wait ends (with no number) before the scope waits for that thread.
                let first_tx = first_tx;
                // B1: a statics pass still clean by its record is not made here (the unit memo may
                // still have lost an object of it: below); the pass, the fingerprint of its record
                // when clean, and the statics' content now.
                let statics = late_statics.then(|| {
                    sc.spawn(|| {
                        let content = statics_b1.then(|| statics_read_fp(&cgen::record::Read::Statics));
                        let clean = content.and_then(statics_clean);
                        ((clean.is_none() || !b1_skip).then(|| assemble(1, &[], None, None)), clean, content)
                    })
                });
                // With it, the jobs that need neither the copies set nor B1's reads: the two cuts
                // and, with C units only, main, runtime and locations (the table unit names fn units,
                // so it waits for their cut).
                let cut = sc.spawn(|| {
                    cgen::in_layout_phase(asm_tag, || cgen::names::with(rn, || cgen::names::glue_shard_keys(&caches.glue, &caches.out, super::release_c::shard_bytes())))
                });
                let fn_cut = sc.spawn(|| rg_cell.get_or_init(|| cut_fn_units(names)));
                let early_c = late_statics.then(|| sc.spawn(|| par_map(&early, |&u| assemble(u, &[], None, None))));
                // Release C copies from a pinned profile (`LUST_PGO_COPIES=<profdata>`, read by the
                // instrumented build and the use build alike, so both copy the same callees and a
                // caller's profile record matches its use): the fns it ran `LUST_PGO_COPY_MIN`
                // times or more (default 1000) get copies of the callees it ran as often.
                // `LUST_PGO_COPIES=*`: every fn counts as hot, a test of the copy rules on any
                // program. A fn with an unwind cleanup frame gets copies when it ran
                // `cgen::FRAME_COPY_MIN` times.
                let copy_hot = match std::env::var_os("LUST_PGO_COPIES").filter(|_| !llvm_on) {
                    Some(path) => {
                        let (hot, frames) = if path == "*" {
                            let all: std::collections::HashSet<u64> = names.fns.iter().flatten().filter_map(|id| u64::from_str_radix(id, 16).ok()).collect();
                            (all.clone(), all)
                        } else {
                            let min: u64 = std::env::var("LUST_PGO_COPY_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(1000);
                            let ids = |min: u64, memo: &str| crate::cc::pgo::hot_ids_of(std::path::Path::new(&path), &dir.join("cc"), min, memo);
                            ids(min, "pgo-copies.memo").and_then(|hot| Ok((hot, ids(min.max(cgen::FRAME_COPY_MIN), "pgo-copies-frames.memo")?)))?
                        };
                        let big = cgen::in_layout_phase(cgen::layout_phase(), || cgen::names::with(rn, || cgen::big_adts(&program)));
                        Some(cgen::CopyHot { hot, frames, big })
                    }
                    None => None,
                };
                // A unit's identity: its registration name, fns and main slot, the switches every
                // unit reads (`b1_base`), the copies profile's hot set (the copy choice reads it),
                // and the compiler build.
                let b1_switches = b1_base.as_ref().map(|base| {
                    // Both id sets; the big ADTs are in each pick's read (`cgen::read_fp`).
                    let copies = copy_hot.as_ref().map(|h| {
                        let bytes = |s: &std::collections::HashSet<u64>| {
                            let mut ids: Vec<u64> = s.iter().copied().collect();
                            ids.sort_unstable();
                            ids.iter().flat_map(|i| i.to_le_bytes()).collect::<Vec<u8>>()
                        };
                        crate::driver::cache::hash128(&[&bytes(&h.hot), &bytes(&h.frames)], 14)
                    });
                    format!("{base}\ncopies={copies:?}\n{}", env!("LUST_BUILD_HASH"))
                });
                // One read's fingerprint now (`cgen::read_fp`), in the assembly's layout phase.
                let read_fp = |r: &cgen::record::Read| {
                    let t = b1_observe.then(Instant::now);
                    let f = cgen::in_layout_phase(asm_tag, || cgen::names::with(rn, || cgen::read_fp(&program, &caches.out, &caches.glue, &b1_statics, copy_hot.as_ref(), r)));
                    if let Some(t) = t {
                        use cgen::record::Read as R;
                        let k = match r {
                            R::Fn(_) => 0,
                            R::SlotOf(_) => 1,
                            R::Glue(..) => 2,
                            R::Type(..) | R::TypeFwd(..) => 3,
                            R::Static(_) | R::Statics => 4,
                            R::Main => 5,
                            R::Pick(..) | R::PickHot(_) => 6,
                        };
                        kind_ns[k].fetch_add(t.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
                        kind_ns[7 + k].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                    f
                };
                // The last build's records name their reads by index in the session's table: the
                // passes below fingerprint each distinct one once (many units read one type).
                let t_old = Instant::now();
                // (The statics' content is the statics thread's own read.)
                let old_ids: Vec<u32> = if !b1_record || caches.unit_records.is_empty() {
                    Vec::new()
                } else {
                    let mut used = vec![false; caches.unit_reads.len()];
                    caches.unit_records.values().flat_map(|u| &u.reads).for_each(|&(i, _)| used[i as usize] = true);
                    let content = caches.unit_reads.find(&cgen::record::Read::Statics);
                    (0..caches.unit_reads.len() as u32).filter(|&i| used[i as usize] && Some(i) != content).collect()
                };
                // B1's fingerprints of the last build's reads, in two passes of their own (`par_map`
                // hands out a pass's jobs in batches, so behind thousands of cheap jobs a few workers
                // took them all), each in parts: the reads the glue shards' records hold (a shard
                // clean by them is not made), and the rest. A read's fingerprint is of the program
                // now, not of a cut.
                let (shard_ids_of_reads, rest_ids): (Vec<u32>, Vec<u32>) = {
                    let mut by_shard = vec![false; caches.unit_reads.len()];
                    caches.unit_records.iter().filter(|(reg, _)| reg.starts_with(SHARD_RECORD)).flat_map(|(_, u)| &u.reads).for_each(|&(i, _)| by_shard[i as usize] = true);
                    old_ids.iter().copied().partition(|&i| by_shard[i as usize])
                };
                b1_ms[1] = t_old.elapsed().as_secs_f64() * 1e3;
                let in_parts = |ids: &[u32]| -> Vec<std::ops::Range<usize>> {
                    let step = ids.len().div_ceil(b1_shards).max(1);
                    (0..ids.len()).step_by(step).map(|a| a..(a + step).min(ids.len())).collect()
                };
                let (first_parts, rest_parts) = (in_parts(&shard_ids_of_reads), in_parts(&rest_ids));
                let (reads, records) = (&caches.unit_reads, &caches.unit_records);
                let fingerprints = |ids: &[u32], parts: &[std::ops::Range<usize>]| -> Vec<Vec<(u32, (u64, u64))>> {
                    par_map(&(0..parts.len()).collect::<Vec<_>>(), |&t| ids[parts[t].clone()].iter().map(|&i| (i, read_fp(reads.get(i)))).collect())
                };
                // Beside the statics unit, the cuts and the C units above, each a job of its own that
                // reads no other's result (on a build with few changes each in turn ended the
                // assembly): B1's two passes. Then, beside B1's second pass, the glue shards: one still
                // clean by its last record whose object the unit memo holds is not made (B1). (B1's
                // records change after these, so these jobs have a scope of their own.)
                let (rg, shard_ids, shard_reg, early_made, now, shard_clean, shard_made, lost) = std::thread::scope(|inner| {
                    // The pool runs one pass at a time (another gets threads of its own), so the
                    // second pass starts when the first ends.
                    let (first_done, first_end) = std::sync::mpsc::channel::<()>();
                    let shard_fps = inner.spawn(move || {
                        let f = fingerprints(&shard_ids_of_reads, &first_parts);
                        drop(first_done);
                        f
                    });
                    let rest = inner.spawn(move || {
                        let _ = first_end.recv();
                        fingerprints(&rest_ids, &rest_parts)
                    });
                    let rg = fn_cut.join().unwrap_or_else(|e| std::panic::resume_unwind(e));
                    asm_ms[0] = t_asm.elapsed().as_secs_f64() * 1e3;
                    let table = late_statics.then(|| assemble(3, &[], None, None));
                    let shard_keys = cut.join().unwrap_or_else(|e| std::panic::resume_unwind(e));
                    n_shards = shard_keys.len();
                    let _ = first_tx.send(FIRST_FN_UNIT + rg.len() + n_shards);
                    asm_ms[1] = t_asm.elapsed().as_secs_f64() * 1e3;
                    // B1 for the glue shards: a shard is its keys (their prototypes, in order) under
                    // B1's switches; its record goes by a name of that identity (its unit number moves
                    // with the fn units'). `unit_id` and `rg[g].0` of the fn units, for shard `j` at
                    // `rg.len() + j`.
                    let shard_ids: Vec<(u64, u64)> = shard_keys
                        .iter()
                        .map(|keys| {
                            let mut parts: Vec<&[u8]> = vec![SHARD_RECORD.as_bytes(), b1_switches.as_deref().unwrap_or("").as_bytes()];
                            parts.extend(keys.iter().map(|k| caches.glue.protos[*k].as_bytes()));
                            crate::driver::cache::hash128(&parts, 17)
                        })
                        .collect();
                    let shard_reg: Vec<String> = shard_ids.iter().map(|(a, b)| format!("{SHARD_RECORD}{a:016x}{b:016x}")).collect();
                    let mut now: Vec<Option<(u64, u64)>> = vec![None; if old_ids.is_empty() { 0 } else { reads.len() }];
                    shard_fps.join().unwrap_or_else(|e| std::panic::resume_unwind(e)).into_iter().flatten().for_each(|(i, f)| now[i as usize] = Some(f));
                    let shard_clean: Vec<Option<u128>> =
                        if now.is_empty() { vec![None; n_shards] } else { (0..n_shards).map(|j| b1_clean_by(records, &now, &shard_reg[j], shard_ids[j])).collect() };
                    // The memo pre-check's answer (`b1_memo`); none when its thread panicked, and then
                    // every clean unit is made.
                    let lost = if b1_skip && !records.is_empty() { b1_memo.take() } else { None };
                    let skip: Vec<bool> = (0..n_shards).map(|j| shard_clean[j].is_some() && lost.as_ref().is_some_and(|l| !l.contains(&shard_reg[j]))).collect();
                    let (texts, recs): (Vec<String>, Vec<cgen::names::ShardRecord>) =
                        cgen::names::with(rn, || cgen::names::glue_shard_texts(&program, &caches.glue, &shard_keys, &skip, b1_record)).into_iter().unzip();
                    rshards = texts;
                    if let Some(a) = &adapters {
                        let new = par_map(&rshards, |t| a.adapt(t, |_| false));
                        for (t, n) in rshards.iter_mut().zip(new) {
                            if let Some(n) = n {
                                *t = n;
                            }
                        }
                    }
                    // A shard not made has no text: the stream does not take it.
                    if let Some(s) = &stream {
                        let first = FIRST_FN_UNIT + rg.len();
                        par_map(&(0..n_shards).collect::<Vec<_>>(), |&j| s.add(&format!("u{}", first + j), &rshards[j]));
                    }
                    // In unit order: main, runtime, the table unit, locations.
                    let early_made = match (early_c, table) {
                        (Some(h), Some(table)) => {
                            let mut m = h.join().unwrap_or_else(|e| std::panic::resume_unwind(e));
                            m.insert(2, table);
                            m
                        }
                        _ => Vec::new(),
                    };
                    rest.join().unwrap_or_else(|e| std::panic::resume_unwind(e)).into_iter().flatten().for_each(|(i, f)| now[i as usize] = Some(f));
                    (rg, shard_ids, shard_reg, early_made, now, shard_clean, recs.into_iter().zip(skip).collect::<Vec<_>>(), lost)
                });
                let unit_id = |g: usize| {
                    let (reg, slots) = &rg[g];
                    crate::driver::cache::hash128(&[reg.as_bytes(), format!("{slots:?} {main_slot}").as_bytes(), b1_switches.as_deref().unwrap_or("").as_bytes()], 13)
                };
                // The statics pass's B1 entries come after the shards' (at `rg.len() + n_shards`).
                let reg_of = |g: usize| match g.checked_sub(rg.len()) {
                    None => rg[g].0.as_str(),
                    Some(j) if j < n_shards => shard_reg[j].as_str(),
                    Some(_) => STATICS_RECORD,
                };
                let id_of = |g: usize| match g.checked_sub(rg.len()) {
                    None => unit_id(g),
                    Some(j) if j < n_shards => shard_ids[j],
                    Some(_) => statics_id,
                };
                let mut made = Vec::with_capacity(5 + rg.len());
                made.extend(early_made);
                let mut inl: Vec<Vec<usize>> = Vec::with_capacity(rg.len());
                if late_statics {
                    inl.resize(rg.len(), Vec::new());
                } else {
                    let first: Vec<usize> = early[..n_early].iter().copied().chain(0..rg.len()).collect();
                    for (k, r) in par_map(&(0..first.len()).collect::<Vec<_>>(), |&k| {
                        if k < n_early {
                            Ok(assemble(first[k], &[], None, None))
                        } else {
                            Err(cgen::ll::ll_inline_set(&caches.out, &rg[first[k]].1, &slot_of, hot.as_ref()))
                        }
                    })
                    .into_iter()
                    .enumerate()
                    {
                        match r {
                            Ok(m) => made.push(m),
                            Err(set) => {
                                debug_assert!(k >= n_early);
                                inl.push(set)
                            }
                        }
                    }
                }
                let table = &caches.unit_reads;
                // B1: each unit still clean by its last record keeps its old fingerprint; skipped
                // are the clean units the unit memo can serve (their fingerprint in it, their object
                // in the cache), and the rest assemble after all. The fn units, then the shards.
                let t_clean = Instant::now();
                let mut b1_clean: Vec<Option<u128>> = if now.is_empty() {
                    vec![None; rg.len()]
                } else {
                    par_map(&(0..rg.len()).collect::<Vec<_>>(), |&g| b1_clean_by(&caches.unit_records, &now, &rg[g].0, unit_id(g)))
                };
                b1_clean.extend(shard_clean);
                // A read's fingerprint now, when a last build's record holds it.
                let fp_now = |r: &cgen::record::Read| table.find(r).and_then(|i| now.get(i as usize).copied().flatten());
                b1_ms[2] = t_clean.elapsed().as_secs_f64() * 1e3;
                let mut b1_skipped = vec![false; rg.len()];
                if let Some(lost) = &lost {
                    for (g, skip) in b1_skipped.iter_mut().enumerate() {
                        *skip = b1_clean[g].is_some() && !lost.contains(&rg[g].0);
                    }
                }
                b1_skipped.extend(shard_made.iter().map(|&(_, skipped)| skipped));
                b1_ms[3] = t_clean.elapsed().as_secs_f64() * 1e3 - b1_ms[2];
                asm_ms[2] = t_asm.elapsed().as_secs_f64() * 1e3;
                let c_refs = cgen::names::with(rn, || cgen::ll::on(&program)).then(|| {
                    // The C units, glue shards and statics parts are made this build; each fn's C was read when
                    // its FnOut was made (`FnOut::ll_c_refs`; a C body's `text` is read here).
                    let statics_now = statics_out.lock().unwrap_or_else(|e| e.into_inner());
                    let texts: Vec<&str> =
                        made.iter().map(|(_, c, _)| c.as_str()).chain(rshards.iter().map(String::as_str)).chain(statics_now.iter().map(String::as_str)).collect();
                    let mut r = cgen::ll::CRefs::default();
                    for p in par_map(&texts, |t| {
                        let mut r = cgen::ll::CRefs::default();
                        r.scan(t);
                        r
                    }) {
                        r.extend(&p);
                    }
                    for f in caches.out.iter() {
                        if f.ll.is_empty() {
                            r.scan(&f.code_text());
                        } else {
                            r.extend(&f.ll_c_refs);
                        }
                    }
                    if let Some(id) = cgen::names::with(rn, || cgen::names::fn_tag_opt(main_slot)).and_then(|id| u64::from_str_radix(&id, 16).ok()) {
                        r.wrappers.insert(id);
                    }
                    r
                });
                asm_ms[3] = t_asm.elapsed().as_secs_f64() * 1e3;
                let fn_jobs: Vec<usize> = (0..rg.len()).map(|g| g + FIRST_FN_UNIT).collect();
                made.extend(par_map(&fn_jobs, |&u| match b1_skipped[u - FIRST_FN_UNIT] {
                    true => (base_obj(u), String::new(), String::new()),
                    false => assemble(u, &inl, c_refs.as_ref(), copy_hot.as_ref()),
                }));
                // The units keep their order: the statics unit is unit 1. A statics pass clean by its
                // record is not made when the unit memo holds every object of it (the index and the
                // parts cc then takes by fingerprint, `statics_unit_fp`); else it is made now. Its
                // B1 entries follow the shards' (`b1_clean`, `b1_skipped`).
                let mut statics_content = None;
                if let Some(h) = statics {
                    let (made_now, clean, content) = h.join().unwrap_or_else(|e| std::panic::resume_unwind(e));
                    let all_held = lost.as_ref().is_some_and(|l| (0..=caches.statics_parts).all(|k| !l.contains(&statics_unit_name(k))));
                    let skipped = made_now.is_none() && all_held;
                    let unit = match made_now {
                        Some(m) => m,
                        None if skipped => {
                            *statics_out.lock().unwrap_or_else(|e| e.into_inner()) = vec![String::new(); caches.statics_parts];
                            (base_obj(1), String::new(), String::new())
                        }
                        None => assemble(1, &[], None, None),
                    };
                    made.insert(1, unit);
                    b1_clean.push(clean);
                    b1_skipped.push(skipped);
                    statics_content = content;
                }
                asm_ms[4] = t_asm.elapsed().as_secs_f64() * 1e3;
                if b1_record {
                    use cgen::record::{Read, UnitRecord};
                    let mut recs = std::mem::take(&mut *b1_records.lock().unwrap_or_else(|e| e.into_inner()));
                    recs.sort_unstable_by_key(|(g, _)| *g);
                    // The glue shards made now, after the fn units (`reg_of`, `id_of`), then the statics
                    // pass when it was made with a record.
                    recs.extend(shard_made.into_iter().enumerate().filter(|(_, (_, skipped))| !skipped).map(|(j, (rec, _))| (rg.len() + j, rec)));
                    let g_statics = rg.len() + n_shards;
                    if statics_b1 && !b1_skipped.get(g_statics).copied().unwrap_or(true) {
                        recs.push((g_statics, statics_rec.lock().unwrap_or_else(|e| e.into_inner()).take()));
                    }
                    // The reads of the units assembled now that no old record holds.
                    let t_more = Instant::now();
                    // (Each step that looks a read up runs on every thread: a glue shard's record holds
                    // about a thousand reads, each a type tree to hash.)
                    let at: Vec<usize> = (0..recs.len()).collect();
                    // (The statics' content is the statics thread's read: on all cores itself, so not
                    // from a pool job here.)
                    let missing: Vec<Read> = {
                        let per: Vec<Vec<&Read>> = par_map(&at, |&k| recs[k].1.iter().flat_map(|(_, reads)| reads).filter(|r| fp_now(r).is_none()).collect());
                        let mut m: FxMap<&Read, ()> = FxMap::default();
                        per.into_iter().flatten().filter(|r| **r != Read::Statics).for_each(|r| {
                            m.insert(r, ());
                        });
                        m.into_keys().cloned().collect()
                    };
                    let fps = par_map(&missing, |r| read_fp(r));
                    let mut more: FxMap<Read, (u64, u64)> = missing.into_iter().zip(fps).collect();
                    if recs.iter().any(|(g, _)| *g == g_statics) {
                        more.insert(Read::Statics, statics_content.unwrap_or_else(|| statics_read_fp(&Read::Statics)));
                    }
                    let read_fps: Vec<Vec<(u64, u64)>> = par_map(&at, |&k| {
                        recs[k].1.iter().flat_map(|(_, reads)| reads).map(|r| fp_now(r).or_else(|| more.get(r).copied()).unwrap_or((u64::MAX, u64::MAX))).collect()
                    });
                    b1_ms[4] = t_more.elapsed().as_secs_f64() * 1e3;
                    // B1's own wall time: the last build's reads fingerprint while the C units assemble.
                    let fp_ms = b1_ms[0] + b1_ms[1] + b1_ms[2] + b1_ms[3] + b1_ms[4];
                    let n_reads = now.iter().filter(|f| f.is_some()).count() + more.len();
                    let (mut same, mut new, mut unrecorded, mut unsound, mut missed) = (0, 0, 0, 0, 0);
                    // With LUST_B1_OBSERVE=1: in the missed units, the reads whose fingerprint moved,
                    // by kind (Fn, SlotOf, Glue, Type, Static, Main, Pick).
                    let mut moved = [0usize; 7];
                    let mut unsound_names: Vec<String> = Vec::new();
                    type Fresh = std::sync::Mutex<Option<((u64, u64), Vec<(Read, (u64, u64))>)>>;
                    let mut fresh: Vec<(usize, Fresh)> = Vec::new();
                    for ((g, rec), read_fps) in recs.into_iter().zip(read_fps) {
                        let Some((pieces, reads)) = rec else {
                            unrecorded += 1;
                            continue;
                        };
                        let reg = reg_of(g);
                        match caches.unit_records.get(reg) {
                            Some(old) => {
                                let same_pieces = old.pieces == pieces;
                                same += same_pieces as usize;
                                if b1_clean[g].is_some() && !same_pieces {
                                    unsound += 1;
                                    if unsound_names.len() < 3 {
                                        unsound_names.push(reg.to_string());
                                    }
                                }
                                missed += (same_pieces && b1_clean[g].is_none()) as usize;
                                if b1_observe && same_pieces && b1_clean[g].is_none() && old.id == id_of(g) {
                                    for &(i, f) in &old.reads {
                                        let r = table.get(i);
                                        if now.get(i as usize).copied().flatten() != Some(f) {
                                            moved[match r {
                                                Read::Fn(_) => 0,
                                                Read::SlotOf(_) => 1,
                                                Read::Glue(..) => 2,
                                                Read::Type(..) | Read::TypeFwd(..) => 3,
                                                Read::Static(_) | Read::Statics => 4,
                                                Read::Main => 5,
                                                Read::Pick(..) | Read::PickHot(_) => 6,
                                            }] += 1;
                                        }
                                    }
                                }
                            }
                            None => new += 1,
                        }
                        let reads = reads.into_iter().zip(read_fps).collect();
                        fresh.push((g, std::sync::Mutex::new(Some((pieces, reads)))));
                    }
                    // The new records' reads join the session's table (each found on every thread, the
                    // new ones added in turn), then each record takes its fingerprint, on every thread.
                    drop(now);
                    let fresh: Vec<(usize, (u64, u64), Vec<(Read, (u64, u64))>)> = fresh
                        .into_iter()
                        .map(|(g, m)| {
                            let (pieces, reads) = m.into_inner().unwrap_or_else(|e| e.into_inner()).unwrap_or_default();
                            (g, pieces, reads)
                        })
                        .collect();
                    let found: Vec<Vec<Option<u32>>> = {
                        let table = &caches.unit_reads;
                        par_map(&fresh, |(_, _, reads)| reads.iter().map(|(r, _)| table.find(r)).collect())
                    };
                    let fresh: Vec<(usize, (u64, u64), Vec<(u32, (u64, u64))>)> = fresh
                        .into_iter()
                        .zip(found)
                        .map(|((g, pieces, reads), found)| {
                            (g, pieces, reads.into_iter().zip(found).map(|((r, f), i)| (i.unwrap_or_else(|| caches.unit_reads.index(r)), f)).collect())
                        })
                        .collect();
                    let table = &caches.unit_reads;
                    let fresh: Vec<(usize, UnitRecord)> =
                        par_map(&fresh, |(g, pieces, reads)| (*g, UnitRecord::new(id_of(*g), *pieces, reads.clone(), table)));
                    if b1_check && unsound > 0 {
                        panic!("LUST_CHECK_UNIT_FP: {unsound} C fn units, glue shards or statics passes are clean by their recorded reads, but their text changed: {}", unsound_names.join(", "));
                    }
                    // The next build's records: a skipped unit keeps its own, an assembled one takes
                    // its new one. cc takes each recorded unit's fingerprint; the oracle gives a unit
                    // clean by its reads its old one with its new text, so cc's memo fails a key
                    // that moved.
                    // The statics pass's units are unit 1 and its parts after the shards, each with its
                    // fingerprint from the record's (`statics_unit_fp`).
                    let first_statics = FIRST_FN_UNIT + g_statics;
                    let put = |b1_units: &mut FxMap<String, (u128, bool)>, g: usize, fp: u128, n_parts: usize, bare: bool| {
                        if g != g_statics {
                            b1_units.insert(format!("u{}", g + FIRST_FN_UNIT), (fp, bare));
                            return;
                        }
                        b1_units.insert("u1".to_string(), (statics_unit_fp(fp, 0), bare));
                        for j in 0..n_parts {
                            b1_units.insert(format!("u{}", first_statics + j), (statics_unit_fp(fp, j + 1), bare));
                        }
                    };
                    let mut old = std::mem::take(&mut caches.unit_records);
                    let mut next: FxMap<String, UnitRecord> = FxMap::default();
                    for (g, &skipped) in b1_skipped.iter().enumerate() {
                        if skipped && let Some(r) = old.remove(reg_of(g)) {
                            put(&mut b1_units, g, r.fp, caches.statics_parts, true);
                            next.insert(reg_of(g).to_string(), r);
                        }
                    }
                    let parts_now = statics_out.lock().unwrap_or_else(|e| e.into_inner()).len();
                    for (g, r) in fresh {
                        if b1_check || b1_skip {
                            let fp = if b1_check { b1_clean[g].unwrap_or(r.fp) } else { r.fp };
                            put(&mut b1_units, g, fp, parts_now, false);
                        }
                        if g == g_statics {
                            caches.statics_parts = parts_now;
                        }
                        next.insert(reg_of(g).to_string(), r);
                    }
                    caches.unit_records = next;
                    // A read no record names stays in the table until the table holds twice the
                    // live ones; then it starts again from the live records (a record's
                    // fingerprint follows its reads, not their indexes).
                    let live: usize = {
                        let mut used = vec![false; caches.unit_reads.len()];
                        caches.unit_records.values().flat_map(|u| &u.reads).for_each(|&(i, _)| used[i as usize] = true);
                        used.iter().filter(|&&u| u).count()
                    };
                    if caches.unit_reads.len() > 2 * live + 100_000 {
                        let old_table = std::mem::take(&mut caches.unit_reads);
                        for r in caches.unit_records.values_mut() {
                            for (i, _) in r.reads.iter_mut() {
                                *i = caches.unit_reads.index(old_table.get(*i).clone());
                            }
                        }
                    }
                    b1_ms[5] = t_more.elapsed().as_secs_f64() * 1e3 - b1_ms[4];
                    let statics_state = match (b1_skipped.get(g_statics), b1_clean.get(g_statics)) {
                        _ if !statics_b1 => "unrecorded",
                        (Some(true), _) => "not made",
                        (Some(false), Some(Some(_))) => "clean by its reads, made",
                        _ => "made",
                    };
                    let line = format!(
                        "{} C fn units, {n_shards} glue shards and the statics pass ({statics_state}), {same} the same pieces as the last build, {new} new, {unrecorded} unrecorded; by reads {} clean, {unsound} of them with changed pieces (unsound{}), {missed} unchanged units the reads miss; {} not assembled; {n_reads} reads; B1 {fp_ms:.0} ms",
                        rg.len(),
                        b1_clean.iter().filter(|c| c.is_some()).count(),
                        if unsound_names.is_empty() { String::new() } else { format!(": {}", unsound_names.join(", ")) },
                        b1_skipped.iter().filter(|&&s| s).count()
                    );
                    if b1_observe {
                        let k: Vec<u64> = kind_ns.iter().map(|a| a.load(std::sync::atomic::Ordering::Relaxed)).collect();
                        eprintln!(
                            "b1-observe: {line}; worker time (count) Fn {:.0} ms ({}), SlotOf {:.0} ({}), Glue {:.0} ({}), Type {:.0} ({}), Static {:.0} ({}), Main {:.0} ({}), Pick {:.0} ({}); wall ms statics {:.0}, buckets {:.0}, clean {:.0}, memo {:.0}, new reads {:.0}, records {:.0}; moved reads in missed units {moved:?}",
                            k[0] as f64 / 1e6, k[7], k[1] as f64 / 1e6, k[8], k[2] as f64 / 1e6, k[9], k[3] as f64 / 1e6, k[10], k[4] as f64 / 1e6, k[11], k[5] as f64 / 1e6, k[12],
                            k[6] as f64 / 1e6, k[13],
                            b1_ms[0], b1_ms[1], b1_ms[2], b1_ms[3], b1_ms[4], b1_ms[5]
                        );
                    }
                    b1_line = Some(line);
                }
                asm_ms[5] = t_asm.elapsed().as_secs_f64() * 1e3;
                let mut units: Vec<(PathBuf, String)> = Vec::with_capacity(made.len());
                // The LLVM backend (cgen/ll.rs): a fn unit whose fns have LLVM IR gets two
                // companions after the glue shards, its IR `u<N>.ll` and its helpers' C `u<N>.hc`,
                // which cc.rs compiles with `u<N>` into one object.
                let mut companions: Vec<(PathBuf, String)> = Vec::new();
                for (o, c, helpers) in made {
                    if !helpers.is_empty() {
                        companions.push((o.with_extension("hc"), helpers));
                    }
                    units.push((o, c));
                }
                let first = FIRST_FN_UNIT + rg.len();
                units.extend(rshards.drain(..).enumerate().map(|(j, c)| (base_obj(first + j), c)));
                let statics = std::mem::take(&mut *statics_out.lock().unwrap_or_else(|e| e.into_inner()));
                n_statics = statics.len();
                units.extend(statics.into_iter().enumerate().map(|(j, c)| (base_obj(first + n_shards + j), c)));
                let triple = if req.session.target_triple.is_empty() { crate::protocol::host_triple() } else { &req.session.target_triple };
                let lls = par_map(&(0..rg.len()).collect::<Vec<_>>(), |&g| cgen::ll::ll_unit(&caches.out, &rg[g].1, &inl[g], triple));
                for (g, text) in lls.into_iter().enumerate() {
                    if !text.is_empty() {
                        units.push((dir.join(format!("u{}.ll", g + FIRST_FN_UNIT)), text));
                    }
                }
                units.extend(companions);
                asm_ms[6] = t_asm.elapsed().as_secs_f64() * 1e3;
                if b1_observe || std::env::var_os("LUST_ASM_PARTS").is_some_and(|v| v == "1") {
                    let d: Vec<String> = (0..7).map(|i| format!("{:.0}", asm_ms[i] - if i > 0 { asm_ms[i - 1] } else { 0.0 })).collect();
                    let c: Vec<u64> = c_unit_ms.iter().map(|a| a.load(std::sync::atomic::Ordering::Relaxed) / 1000).collect();
                    eprintln!(
                        "b1-observe asm parts ms: groups {}, glue shard cut {}, B1 before + glue shards + C units + inline sets {} (main {}, statics {}, runtime {}, table {}, locations {}), C refs {}, fn units {}, B1 after {}, the rest {}",
                        d[0], d[1], d[2], c[0], c[1], c[2], c[3], c[4], d[3], d[4], d[5], d[6]
                    );
                }
                Ok(units)
            });
            match assembled {
                Ok(units) => units,
                Err(e) => return Response { stderr: format!("error: LUST_PGO_COPIES: {e}\n"), code: 3, ..Default::default() },
            }
        }
    };
    let rgroups = rg_cell.into_inner();
    // The LLVM backend (cgen/ll.rs) wrote `.ll` companions: only cc.rs builds them.
    let llvm = rgroups.is_some() && cgen::names::with(rn, || cgen::ll::on(&program));
    // The units the link takes after 1..4: release C has its own fn units, glue shards and
    // statics parts.
    let link_fn_units: Vec<usize> = match &rgroups {
        Some(rg) => (0..rg.len() + n_shards + n_statics).map(|g| g + FIRST_FN_UNIT).collect(),
        None => fn_units.clone(),
    };
    if let Some(p) = &req.emit_c {
        // Emitted C must be self-contained: write every base unit, not only the units
        // rebuilt for this (possibly warm, incremental) build.
        if rgroups.is_some() {
            for (o, c) in &units {
                // An LLVM companion (`u<N>.ll`, `u<N>.hc`) keeps its extension.
                if o.extension().is_some_and(|e| e == "ll" || e == "hc") {
                    let u = o.file_name().and_then(|s| s.to_str()).unwrap_or("ux.ll");
                    let _ = std::fs::write(format!("{}.{u}", p.display()), c);
                    continue;
                }
                let u = o.file_stem().and_then(|s| s.to_str()).and_then(|s| s.strip_prefix('u')).unwrap_or("x");
                let _ = std::fs::write(format!("{}.u{u}.c", p.display()), c);
            }
        } else {
            for u in [0, 1, 2, 3, LOC_UNIT].into_iter().chain(fn_units.iter().copied()) {
                // The standalone main unit registers no overlays; `lust_base_init` covers all units.
                let c = if u == 0 { cgen::main_unit(main_slot, &[], cgen::unwind_init(&program, |f| front.fn_slot[f.0 as usize])) } else { gen_unit(u, false) };
                let _ = std::fs::write(format!("{}.u{u}.c", p.display()), c);
            }
        }
        // Unwind tables: the C++ half of a panic (throw and catch), for the C++ compiler.
        if program.unwind_tables {
            let _ = std::fs::write(format!("{}.eh.cc", p.display()), include_str!("../runtime/unwind.cc"));
        }
        // A foreign emit-c build has no link step here: the emitted C
        // is the product, unless the cc release driver below links it.
        // So is an LLVM backend build's (tcc cannot take its `.ll` units).
        if (foreign || llvm) && !req.cc {
            return Response { code: 0, ..Default::default() };
        }
    }
    if llvm && !req.cc {
        return Response {
            stderr: "error: LUST_RELEASE_BACKEND=llvm builds through the release driver (`lust build --release --target <triple>`) or with --emit-c\n".into(),
            code: 2,
            ..Default::default()
        };
    }
    t.lap("assemble C units (par)");
    // The release driver (src/cc.rs): the same self-contained unit set
    // goes to the external C compiler for the session target, and the
    // tcc path below never runs. A cold session builds every unit; a
    // persistent one (a front image, src/image.rs) keeps its groups
    // frozen, so a clean unit's C is the same as last time and its object
    // comes from the cache. Overlays do not exist here: every build emits
    // the base form of each unit.
    if req.cc {
        // The release driver returns before the visits line at the end: its log line is here
        // (front-check's path coverage).
        front.last_visits.clear();
        Visits { checked: work.len(), ..visits }.render(&mut front.last_visits);
        log_visits(&front.last_visits);
        let triple = if req.session.target_triple.is_empty() { crate::protocol::host_triple() } else { &req.session.target_triple };
        // Base-form units this build already made (all of them on a fresh
        // base) are taken, not made again. Release C made all of its units above.
        let mut made: FxMap<usize, String> = FxMap::default();
        if rgroups.is_none() {
            for (&(u, overlay), (_, c)) in todo.iter().zip(std::mem::take(&mut units)) {
                if !overlay && u != 0 {
                    made.insert(u, c);
                }
            }
        }
        let prepared = crate::cc::spec_for(triple).and_then(|spec| {
            // Release C (`LUST_RELEASE_C=1`) already holds the content-addressed units.
            let mut all: Vec<(String, String)> = if rgroups.is_some() {
                // An LLVM companion keeps its `.ll` name (cc.rs pairs it with its C unit). The
                // texts move: nothing reads `units` after cc, and a copy of tsgo's is ~1 GB.
                std::mem::take(&mut units)
                    .into_iter()
                    .map(|(o, c)| {
                        let name = if o.extension().is_some_and(|e| e == "ll" || e == "hc") { o.file_name() } else { o.file_stem() };
                        (name.map_or(String::new(), |s| s.to_string_lossy().into_owned()), c)
                    })
                    .collect()
            } else {
                let order: Vec<usize> = [0, 1, 2, 3, LOC_UNIT].into_iter().chain(fn_units.iter().copied()).collect();
                let fresh = par_map(&order, |&u| match u {
                    0 => Some(cgen::main_unit(main_slot, &[], cgen::unwind_init(&program, |f| front.fn_slot[f.0 as usize]))),
                    u if made.contains_key(&u) => None,
                    u => Some(gen_unit(u, false)),
                });
                order.iter().zip(fresh).map(|(&u, c)| (format!("u{u}"), c.or_else(|| made.remove(&u)).unwrap_or_default())).collect()
            };
            // Unwind tables: the C++ half of a panic (throw and catch), for the C++ driver.
            if program.unwind_tables {
                all.push(("eh.cc".to_string(), include_str!("../runtime/unwind.cc").to_string()));
            }
            // musl: mimalloc replaces musl's malloc (LUST_RELEASE_ALLOC=system keeps it;
            // LUST_RELEASE_ALLOC=mimalloc links it for other targets too, to measure a glibc
            // build with the shipped allocator).
            let alloc = std::env::var("LUST_RELEASE_ALLOC");
            if (triple.ends_with("-musl") && alloc.as_deref() != Ok("system") || alloc.as_deref() == Ok("mimalloc"))
                && let Some(mi) = crate::cc::mimalloc_unit()
            {
                all.push(("mimalloc".to_string(), mi));
            }
            // musl: vector mem* replace musl's and zig's loops (LUST_RELEASE_MEM=libc keeps them).
            if triple.ends_with("-musl") && std::env::var("LUST_RELEASE_MEM").as_deref() != Ok("libc") {
                all.push(("memfast".to_string(), crate::cc::memfast_unit()));
            }
            if let Some(parent) = req.out.parent() {
                std::fs::create_dir_all(parent).map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
            }
            Ok((all, spec, crate::driver::cache::Cache::open(&req.file)))
        });
        let (all, spec, cache) = match prepared {
            Ok(x) => x,
            Err(e) => return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() },
        };
        let (out, debug, cc_dir) = (req.out.clone(), req.debug, dir.join("cc"));
        // B1: a unit with a record goes with its fingerprint, a skipped one without its text.
        let all: Vec<crate::cc::UnitIn> = all
            .into_iter()
            .map(|(name, text)| match b1_units.get(&name) {
                Some(&(fp, bare)) => crate::cc::UnitIn { name, fp: Some(fp), text: (!bare).then_some(text) },
                None => crate::cc::UnitIn::text(name, text),
            })
            .collect();
        if req.timings
            && let Some(l) = &b1_line
        {
            let _ = writeln!(resp.stderr, "b1: {l}");
        }
        let job = move || {
            let built = crate::cc::build_with(&all, &spec, &out, debug, cache.as_ref(), &cc_dir, stream).map_err(|e| e.to_string());
            // A build that leaks at exit leaks the unit texts too (they moved out of `units`).
            if leak_at_exit {
                std::mem::forget(all);
            }
            built
        };
        if DEFER_CC.with(std::cell::Cell::get) && !leak_at_exit {
            // Parked for the caller (`DeferredCc`): the session is final before it, as after
            // a build that links.
            caches.objects = Some(req.debug);
            caches.overlays.clear();
            caches.base_units = groups.len();
            drop((bodies, units));
            program.verified = verified;
            super::patch::keep(front, program);
            let head = format!("lust build {path}: ok (cc {triple}: ");
            PARKED.with(|p| *p.borrow_mut() = Some(Parked::Job(DeferredCc { job: Box::new(job), t, head, timings: req.timings })));
            return resp;
        }
        let built = job();
        t.lap("cc compile + link");
        match built {
            Ok(summary) => {
                // The emitted set is this session's base: the next build
                // keeps these groups and emits only what changed.
                caches.objects = Some(req.debug);
                caches.overlays.clear();
                caches.base_units = groups.len();
                if req.timings {
                    let _ = writeln!(resp.stderr, "lust build {path}: ok (cc {triple}: {summary})");
                    t.render(&mut resp.stderr);
                }
                if leak_at_exit {
                    std::mem::forget(bodies);
                    std::mem::forget(units);
                    std::mem::forget(program);
                } else {
                    drop((bodies, units));
                    program.verified = verified;
                    super::patch::keep(front, program);
                }
                return resp;
            }
            Err(e) => return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() },
        }
    }
    // `lust run` of a small program (one function unit, fresh base): compile in memory and run
    // it there, with no object files, link, or exec. The runtime comes from a cached object.
    // libtcc compiles serially, so bigger programs keep the parallel file-based path below.
    // Any setup failure falls back to that path (user code has not run yet). A debug run also
    // keeps the file path, so a debugger sees a real binary. One-shot sessions only: the run
    // forks, no other thread may live at the fork (tcc.rs), and a daemon runs guard compiles
    // on other threads. The daemon wire carries no run arguments (`protocol::read_request`);
    // this check keeps that a pin, not a hope.
    if let Some(run_args) = &req.run_args
        && !caches.persistent
        && fresh_base
        && groups.len() == 1
        && !req.debug
        && let Ok(runtime_obj) = crate::tcc::cached_runtime_object(&cgen::runtime_unit(), req.debug)
    {
        let mem_units: Vec<(PathBuf, String)> = units.iter().filter(|(o, _)| *o != base_obj(2)).cloned().collect();
        let mut argv = vec![req.out.to_string_lossy().into_owned()];
        argv.extend(run_args.iter().cloned());
        if let Ok(code) = crate::tcc::run_in_memory(&mem_units, &runtime_obj, &argv, req.debug) {
            t.lap("tcc compile + run (memory)");
            resp.code = code;
            resp.ran = true;
            if req.timings {
                let kb = mem_units.iter().map(|u| u.1.len()).sum::<usize>() / 1024;
                let _ = writeln!(resp.stderr, "lust run {path}: exit {code} ({} functions, {kb} KB of C, in memory)", program.fns.len());
                t.render(&mut resp.stderr);
            }
            if leak_at_exit {
                std::mem::forget(bodies);
                std::mem::forget(units);
                std::mem::forget(program);
            } else {
                drop((bodies, units));
                program.verified = verified;
                super::patch::keep(front, program);
            }
            return resp;
        }
    }
    // Disk unit objects key on each unit's full C text (see cache.rs):
    // tcc's output is a function of the C, the debug flag, and the
    // compiler, so a hit can never serve an object whose C differs. The
    // C is already built here for every unit in `todo`, so the key costs
    // one hash per unit.
    let mut unit_hits = 0usize;
    if let Err(e) = std::fs::create_dir_all(&dir) {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    let keys: Vec<Option<String>> = match &disk_cache {
        Some(cache) => par_map(&units, |(_, c)| Some(cache.unit_key(c, req.debug))),
        None => vec![None; units.len()],
    };
    // The units move into the miss list, and their C is freed before the
    // link: on a large program (ts-rust's bins, about 1 GB of C) copies of
    // it held the peak memory.
    let (c_bytes, n_units) = (units.iter().map(|u| u.1.len()).sum::<usize>(), units.len());
    let mut miss_units: Vec<(PathBuf, String)> = Vec::new();
    let mut miss_keys: Vec<Option<String>> = Vec::new();
    for ((obj, c), key) in units.into_iter().zip(keys) {
        if let (Some(cache), Some(k)) = (&disk_cache, &key)
            && cache.unit_object(k, &obj)
        {
            unit_hits += 1;
        } else {
            miss_units.push((obj, c));
            miss_keys.push(key);
        }
    }
    if let Err(e) = crate::tcc::compile_units(&miss_units, req.debug) {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    if let Some(cache) = disk_cache {
        for ((obj, _), key) in miss_units.iter().zip(&miss_keys) {
            if let Some(k) = key {
                cache.store_unit_object(k, obj);
            }
        }
        cache.evict_objects();
    }
    let units_compiled = miss_units.len();
    drop(miss_units);
    caches.objects = Some(req.debug);
    t.lap("tcc compile");
    let all_base: Vec<PathBuf> = [1, 2, 3, LOC_UNIT].into_iter().chain(link_fn_units.iter().copied()).map(base_obj).collect();
    let linked = if !caches.persistent {
        let mut objs = vec![base_obj(0)];
        objs.extend(all_base);
        crate::tcc::link(&objs, &req.out, req.debug)
    } else {
        // The base library lives in a persistent dir under a content name
        // (see `resolve_base_dir`): the executable loads it by absolute
        // rpath at run time, so it must survive this daemon and its
        // per-daemon temp dir (`dir`, deleted on daemon exit). A content
        // name also means two sessions or daemons can never overwrite
        // each other's base under a running executable.
        let base_dir = resolve_base_dir(caches, &req.file);
        if !caches.base_swept {
            sweep_bases(&base_dir, 0);
            caches.base_swept = true;
        }
        let base = if rebuild_base {
            caches.base_gen += 1;
            let tmp = base_dir.join(format!("libbase-tmp-{}-{}-{}.{BASE_EXT}", std::process::id(), caches.base_gen, base_tmp_seq()));
            let obj_dir = caches.obj_dir.to_string_lossy().into_owned();
            // The object dir in the hash makes the name unique to this
            // session instance, and the pid names the owning process:
            // see `base_owner_pid`.
            let name_of = |content: &[u8]| {
                let (a, b) = crate::driver::cache::hash128(&[content, obj_dir.as_bytes()], 41);
                format!("base-{}-{a:016x}{b:016x}", std::process::id())
            };
            let built = std::fs::create_dir_all(&base_dir)
                .map_err(|e| format!("cannot create {}: {e}", base_dir.display()))
                .and_then(|_| {
                    // On macOS the library holds its own install name, so the
                    // name comes before the link: from the objects, which fix
                    // the library's bytes.
                    if cfg!(target_os = "macos") {
                        let mut objs = Vec::new();
                        for o in &all_base {
                            objs.extend(std::fs::read(o).map_err(|e| format!("cannot read {}: {e}", o.display()))?);
                        }
                        let name = name_of(&objs);
                        crate::tcc::link_shared(&all_base, &tmp, &format!("lib{name}.{BASE_EXT}"), req.debug)?;
                        return Ok(name);
                    }
                    crate::tcc::link_shared(&all_base, &tmp, "", req.debug)?;
                    let bytes = std::fs::read(&tmp).map_err(|e| format!("cannot read {}: {e}", tmp.display()))?;
                    Ok(name_of(&bytes))
                })
                .and_then(|name| {
                    caches.base_name = name;
                    let soname = format!("lib{}.{BASE_EXT}", caches.base_name);
                    install_base(&tmp, &base_dir.join(&soname))?;
                    if !caches.base_files.contains(&soname) {
                        caches.base_files.push_back(soname);
                    }
                    Ok(())
                });
            if built.is_err() {
                let _ = std::fs::remove_file(&tmp);
            }
            t.lap("link libbase.so");
            built
        } else if !caches.base_name.is_empty() && !base_dir.join(format!("lib{}.{BASE_EXT}", caches.base_name)).exists() {
            // The base file vanished under a live session. The bases dir
            // is in `.lust-cache`, state outside tools may delete as a
            // cache (the edit fuzzer rewrites the crate tree every edit).
            // The base objects still live in the session object dir, so
            // relink the same base under the same name.
            let dest = base_dir.join(format!("lib{}.{BASE_EXT}", caches.base_name));
            let tmp = base_dir.join(format!("libbase-tmp-{}-relink-{}.{BASE_EXT}", std::process::id(), base_tmp_seq()));
            let built = std::fs::create_dir_all(&base_dir)
                .map_err(|e| format!("cannot create {}: {e}", base_dir.display()))
                .and_then(|_| crate::tcc::link_shared(&all_base, &tmp, &format!("lib{}.{BASE_EXT}", caches.base_name), req.debug))
                .and_then(|_| install_base(&tmp, &dest));
            if built.is_err() {
                let _ = std::fs::remove_file(&tmp);
            }
            t.lap("link libbase.so");
            built
        } else {
            Ok(())
        };
        let name = caches.base_name.clone();
        let mut objs = vec![base_obj(0)];
        objs.extend(caches.overlays.iter().map(|&u| overlay_obj(u)));
        base.and_then(|_| crate::tcc::link_with_base(&objs, &base_dir, &name, &req.out, req.debug))
    };
    if let Err(e) = linked {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    // Reference-counted cleanup: record this build as a user of the current base (in memory
    // and in the base dir manifest, for after this daemon exits), then delete old bases past
    // a small grace count while no known output file still references them. A binary the user
    // kept keeps its base; one that was overwritten or deleted does not. A running program
    // keeps its mapped copy after unlink.
    if caches.persistent && !caches.base_name.is_empty() {
        let soname = format!("lib{}.{BASE_EXT}", caches.base_name);
        if let Some(base_dir) = caches.base_dir.clone() {
            record_base_user(&base_dir, &soname, &req.out);
        }
        caches.base_users.push((soname, req.out.clone()));
    }
    const KEEP_BASES: usize = 4;
    let excess: Vec<String> = caches.base_files.iter().take(caches.base_files.len().saturating_sub(KEEP_BASES)).cloned().collect();
    for soname in excess {
        if !base_still_used(&caches.base_users, &soname) {
            caches.base_files.retain(|x| x != &soname);
            caches.base_users.retain(|(u, _)| u != &soname);
            if let Some(base_dir) = &caches.base_dir {
                let _ = std::fs::remove_file(base_dir.join(&soname));
            }
        }
    }
    t.lap("link");
    if stats_on() {
        Stats {
            mode,
            fns: program.fns.len(),
            rechecked: work.len(),
            reused: reads_reused,
            invalidated: reads_invalidated,
            c_bytes,
            dirty_units: dirty_fn_units.len(),
            units_compiled,
            unit_cache_hits: unit_hits,
            table_rebuilt: todo.iter().any(|&(u, _)| u == 3),
            instances: front.fn_slot.len(),
            reemitted,
            templates: generic_work(&caches.gen_reuse).0,
            discovered: generic_work(&caches.gen_reuse).1,
        }
        .render(&mut resp.stderr);
    }
    front.last_visits.clear();
    Visits { checked: work.len(), ..visits }.render(&mut front.last_visits);
    if stats_on() {
        resp.stderr.push_str(&front.last_visits);
    }
    log_visits(&front.last_visits);
    if req.timings {
        let kb = c_bytes / 1024;
        let _ = writeln!(
            resp.stderr,
            "lust build {path}: ok ({} functions, {mode}: {} fn(s) generated, {} units compiled, {} overlays, {kb} KB of C)",
            program.fns.len(),
            n_bodies,
            n_units,
            caches.overlays.len(),
        );
        t.render(&mut resp.stderr);
    }
    if leak_at_exit {
        std::mem::forget(bodies);
        std::mem::forget(program);
    } else {
        drop(bodies);
        program.verified = verified;
        super::patch::keep(front, program);
    }
    resp
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Known;

    /// A binary names lust's own library files by their path under `library/`, wherever lust
    /// is installed, and a workspace file relative to the workspace root.
    #[test]
    fn location_paths_do_not_hold_the_install_path() {
        let client = expand::ClientView { env: None, shown_root: None };
        let at = |lust: &str, p: &str| location_path(&format!("{lust}{p}"), &Path::new(lust).join("library"), Some(Path::new("/ws")), &client);
        for lust in ["/opt/lust", "/home/u/tools/lust-0.2"] {
            assert_eq!(at(lust, "/library/deps/bumpalo/src/lib.rs"), "library/deps/bumpalo/src/lib.rs");
            assert_eq!(at(lust, "/library/std/src/platform.rs"), "library/std/src/platform.rs");
        }
        assert_eq!(location_path("/ws/crates/a/src/lib.rs", Path::new("/opt/lust/library"), Some(Path::new("/ws")), &client), "crates/a/src/lib.rs");
        assert_eq!(location_path("/elsewhere/x.rs", Path::new("/opt/lust/library"), Some(Path::new("/ws")), &client), "/elsewhere/x.rs");
    }

    /// The output of a binary just built. libtcc writes it without O_CLOEXEC, so a child
    /// another test thread spawns meanwhile can hold it open for writing (ETXTBSY): retry
    /// then, as `patch.rs`'s tests do.
    fn run_bin(bin: &Path) -> std::process::Output {
        for _ in 0..100 {
            match std::process::Command::new(bin).output() {
                Ok(o) => return o,
                Err(e) if e.kind() == std::io::ErrorKind::ExecutableFileBusy => std::thread::sleep(std::time::Duration::from_millis(20)),
                Err(e) => panic!("{}: {e}", bin.display()),
            }
        }
        panic!("{}: still busy", bin.display())
    }

    /// The base sweep never deletes a live owner's base (it may be a live
    /// session's current base, found by fuzz seed 7 multi when a guard
    /// session's first-build sweep deleted the warm session's base), but
    /// deletes a dead owner's, and an exiting owner's when told.
    #[test]
    fn sweep_bases_keeps_live_owners() {
        let dir = std::env::temp_dir().join(format!("lust-basesweep-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mine = format!("libbase-{}-aaaa.so", std::process::id());
        let dead = "libbase-4000000003-bbbb.so";
        for f in [&mine, &dead.to_string()] {
            std::fs::write(dir.join(f), b"x").unwrap();
        }
        let gone = dir.join("gone.bin");
        std::fs::write(dir.join("manifest"), format!("{mine}\t{}\n{dead}\t{}\n", gone.display(), gone.display())).unwrap();
        sweep_bases(&dir, 0);
        assert!(dir.join(&mine).exists(), "live owner's base kept");
        assert!(!dir.join(dead).exists(), "dead owner's unreferenced base swept");
        sweep_bases(&dir, std::process::id());
        assert!(!dir.join(&mine).exists(), "exiting owner's unreferenced base swept");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The boundary scan records exactly the clean line starts: not inside a
    /// string (escapes included), a block comment, or brackets, and after a
    /// line comment ends. Fed whole or in two parts, the answer is the same.
    #[test]
    fn boundary_scan_clean_line_starts() {
        let text = "fn a() {\n  let s = \"}\\n{\";\n}\n// x {\nfn b() {}\n/* {\n */\nstruct C;\nlet c = '{';\n";
        let after = |line: &str| text.find(line).unwrap() + line.len();
        let want = vec![after("}\n"), after("// x {\n"), after("fn b() {}\n"), after(" */\n"), after("struct C;\n"), text.len()];
        let mut got = Vec::new();
        BoundaryScan::new().feed(text.as_bytes(), 0, Some(&mut got));
        assert_eq!(got, want);
        let mut split = Vec::new();
        let mut scan = BoundaryScan::new();
        scan.feed(&text.as_bytes()[..20], 0, Some(&mut split));
        scan.feed(&text.as_bytes()[20..], 20, Some(&mut split));
        assert_eq!(split, want);
        assert!(scan.clean());
    }

    /// A chunk cut never falls between an attribute (a doc comment counts,
    /// the lexer emits it as `#[doc = ..]`) and its item: the header of an
    /// item preceded by attributes names the first attribute line, and no
    /// header names the item line itself. A chunk ending after attributes
    /// is a parse error, which used to send the whole file down the serial
    /// re-parse path.
    #[test]
    fn item_headers_keep_attrs_with_their_item() {
        let src = "\
fn a() {}
/// Doc for B.
struct B;
/// Doc for C.
#[derive(Debug)]
struct C;
#[derive(Debug)]
// A plain comment between the attribute and its item.
struct D;
/** Doc for E,
on two lines. */
struct E;
//// Not a doc comment.
struct F;
";
        let at = |line: &str| src.find(line).unwrap();
        let got: Vec<usize> = item_headers(src).into_iter().map(|(at, _)| at).collect();
        assert_eq!(
            got,
            vec![at("fn a()"), at("/// Doc for B."), at("/// Doc for C."), at("#[derive(Debug)]\n//"), at("/** Doc for E,"), at("struct F;")]
        );
    }

    /// A later chunk seeded with the file's inner allows builds the
    /// same fn attributes as a whole parse, so chunking cannot move an
    /// `allow` lint answer.
    #[test]
    fn seeded_chunk_keeps_crate_allows() {
        let whole = "#![allow(arithmetic_overflow)]\nfn a() {}\nfn b() -> u8 { 1 }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(whole, ROOT_FILE, 0, &interner).unwrap();
        let seed = parser::leading_allows(&lexed, &interner, &known);
        assert_eq!(seed.len(), 1);
        let chunk2 = lexer::lex("fn b() -> u8 { 1 }\n", ROOT_FILE, 0, &interner).unwrap();
        let seeded = parser::parse_seeded(&chunk2, &interner, &known, &seed).unwrap();
        let ItemKind::Fn(def) = &seeded.items[0].kind else { panic!("fn item") };
        assert!(def.attrs.iter().any(|a| crate::check::allow_attr(a, &interner, "arithmetic_overflow")));
        let unseeded = parser::parse(&chunk2, &interner, &known).unwrap();
        let ItemKind::Fn(def) = &unseeded.items[0].kind else { panic!("fn item") };
        assert!(!def.attrs.iter().any(|a| crate::check::allow_attr(a, &interner, "arithmetic_overflow")));
    }

    /// The driver's slot keys and `collect`'s stored def ids are computed in two
    /// places from the same source. They must agree for every function, methods
    /// in repeated impl blocks included, or slots and defs would name different
    /// functions. The reverse map (`local_def`) must round-trip too.
    #[test]
    fn slot_keys_match_collect_def_ids() {
        let src = "\
struct Foo { x: i64 }
fn helper() -> i64 { 1 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn main() { println!(\"{}\", helper()); }
impl Foo { fn set(&mut self, v: i64) { self.x = v; } }
";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast.clone()), interner.clone(), known.clone(), ids).unwrap();
        let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
        let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
        assert_eq!(keys.len(), program.fns.len());
        assert_eq!(program.krate, def::LOCAL_CRATE);
        for (i, k) in keys.iter().enumerate() {
            let local = LocalDefId(i as u32);
            assert_eq!(k.disk, program.disk_id(local), "fn {i}");
            assert_eq!(program.def_id(local).krate, program.krate, "fn {i}");
            assert_eq!(program.local_def(k.disk.hash), Some(local), "fn {i}");
        }
        assert_eq!(program.main.map(|m| program.def_id(m)), keys.get(2).map(|k| crate::def::DefId { krate: ids.local, hash: k.disk.hash }));
    }

    /// A nested fn's identity is its parent fn's plus its name and an
    /// ordinal among same-name fns of that parent (section 1.7). The
    /// driver's keys equal collect's def ids at any depth, same-name
    /// fns in one body differ, and an item added to another body (or
    /// above, in the same file) keeps every other nested fn's key.
    #[test]
    fn nested_fn_keys_follow_the_parent() {
        let a = "\
fn f() -> i32 {
    fn g() -> i32 { 1 }
    g()
}
struct S;
impl S { fn m(&self) -> i32 { fn g() -> i32 { 5 } g() } }
fn k() -> i32 {
    { fn g() -> i32 { 2 } }
    fn m() -> i32 {
        fn g() -> i32 { 3 }
        g()
    }
    { fn g() -> i32 { 4 } g() + m() }
}
fn main() { println!(\"{}\", f() + k() + S.m()); }
";
        let b = a.replace("    fn g() -> i32 { 1 }\n", "    fn h() {}\n    fn g() -> i32 { 1 }\n");
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        let keys_of = |src: &str| {
            let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let program = collect::collect(std::sync::Arc::new(ast.clone()), interner.clone(), known.clone(), ids).unwrap();
            let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
            let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
            assert_eq!(keys.len(), program.fns.len());
            for (i, k) in keys.iter().enumerate() {
                assert_eq!(k.disk, program.disk_id(LocalDefId(i as u32)), "fn {i} ({})", k.path);
            }
            keys.into_iter().map(|k| (k.path, k.disk)).collect::<Vec<_>>()
        };
        let (ka, kb) = (keys_of(a), keys_of(&b));
        let paths: Vec<&str> = ka.iter().map(|(p, _)| p.as_str()).collect();
        for want in [
            "fn:f#0::fn:g#0",
            "impl:S#0::method:m#0::fn:g#0",
            "fn:k#0::fn:g#0",
            "fn:k#0::fn:m#0::fn:g#0",
            "fn:k#0::fn:g#1",
            "fn:k#0::fn:m#0",
        ] {
            assert!(paths.contains(&want), "missing {want} in {paths:?}");
        }
        let mut sorted = ka.iter().map(|(_, d)| *d).collect::<Vec<_>>();
        sorted.sort_by_key(|d| d.hash.0);
        sorted.dedup();
        assert_eq!(sorted.len(), ka.len(), "nested keys are unique");
        // `f` gained `h`: every key of `a` stays.
        for (p, d) in &ka {
            assert!(kb.iter().any(|(q, e)| q == p && e == d), "{p} moved");
        }
    }

    /// A fn nested in a trait default method body takes the method's
    /// path (trait path plus method name) as its parent, in the driver's
    /// keys and in collect's def ids alike, and keeps it when another
    /// body gains an item. It once had the body item index fallback and
    /// no scanned slot (a DefPathHash collision with an instance slot).
    #[test]
    fn trait_default_nested_fn_keys_follow_the_method() {
        let a = "\
fn f0() -> i64 { fn z() -> i64 { 7 } z() }
trait Tr {
    fn t(&self) -> i64;
    fn d(&self) -> i64 { fn h(x: &i64) -> bool { *x > 1 } fn m(x: i64) -> i64 { fn m(y: i64) -> i64 { y } m(x) * 10 } self.t() }
}
trait Tr2 { fn d(&self) -> i64 { fn h(_x: &i64) -> bool { true } 0 } }
impl Tr for i64 { fn t(&self) -> i64 { *self } }
fn main() { println!(\"{}\", f0() + 5i64.d()); }
";
        let b = a.replace("fn z() -> i64 { 7 }", "fn y() {} fn z() -> i64 { 7 }");
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        let keys_of = |src: &str| {
            let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let program = collect::collect(std::sync::Arc::new(ast.clone()), interner.clone(), known.clone(), ids).unwrap();
            let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
            // The token scan counts every AST fn (instances come after them).
            assert_eq!(crate::scan::scan(&lexed).fns.len(), keys.len());
            for (i, k) in keys.iter().enumerate() {
                assert_eq!(k.disk, program.disk_id(LocalDefId(i as u32)), "fn {i} ({})", k.path);
            }
            keys.into_iter().map(|k| (k.path, k.disk)).collect::<Vec<_>>()
        };
        let (ka, kb) = (keys_of(a), keys_of(&b));
        let paths: Vec<&str> = ka.iter().map(|(p, _)| p.as_str()).collect();
        for want in ["trait:Tr#0::method:d#0::fn:h#0", "trait:Tr#0::method:d#0::fn:m#0", "trait:Tr#0::method:d#0::fn:m#0::fn:m#0", "trait:Tr2#0::method:d#0::fn:h#0"] {
            assert!(paths.contains(&want), "missing {want} in {paths:?}");
        }
        for (p, d) in &ka {
            assert!(kb.iter().any(|(q, e)| q == p && e == d), "{p} moved");
        }
    }

    /// Adt and static indices are stable under reordering and
    /// addition: a fresh order numbers by def hash (not item
    /// order), and a session order keeps every old index when a
    /// new def arrives whose hash sorts before the old ones. The
    /// driver's predicted indices match collect's assignment.
    #[test]
    fn adt_and_static_indices_are_stable() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        // Collects one source and returns its Adt and static indices
        // by name (Program borrows the Ast, so it stays inside).
        let collect_src = |src: &str, order: &mut collect::DefOrder| {
            let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let (adts, statics) = predicted_def_ids(&ast, &interner, ids.stable, order, &[]);
            let program = collect::collect_with_order(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids, true, order).unwrap();
            for (hash, &id) in &adts {
                // A synthetic std Adt carries its builtin def, not a
                // local-crate one (check/collect.rs).
                let def = if let Some((_, _, d, _)) = crate::check::generics::std_adts().into_iter().find(|s| s.2.hash == *hash) {
                    d
                } else {
                    crate::def::DefId { krate: ids.local, hash: *hash }
                };
                assert_eq!(program.adt_by_def(def).map(|a| a.0), Some(id), "predicted Adt index");
            }
            for (hash, &idx) in &statics {
                let def = crate::def::DefId { krate: ids.local, hash: *hash };
                assert_eq!(program.static_by_def(def), Some(idx), "predicted static index");
            }
            let by_name = |names: &[&str]| -> Vec<u32> { names.iter().map(|n| program.type_names.get(&interner.intern(n)).map_or(u32::MAX, |a| a.0)).collect() };
            let statics_by_name =
                |names: &[&str]| -> Vec<u32> { names.iter().map(|n| program.static_names.get(&interner.intern(n)).copied().unwrap_or(u32::MAX)).collect() };
            (by_name(&["Alpha", "Mid", "Zed"]), statics_by_name(&["SA", "SM", "SZ"]))
        };

        // Item order does not decide indices in a fresh session.
        let (a, _) = collect_src("struct Zed { x: i64 }\nstruct Alpha { x: i64 }\nfn main() {}\n", &mut collect::DefOrder::default());
        let (b, _) = collect_src("struct Alpha { x: i64 }\nstruct Zed { x: i64 }\nfn main() {}\n", &mut collect::DefOrder::default());
        assert_eq!(a[0], b[0], "Alpha index is order-independent");
        assert_eq!(a[2], b[2], "Zed index is order-independent");

        // One session: adding defs (in any item position) and
        // reordering files keeps every old index.
        let mut order = collect::DefOrder::default();
        let (a1, s1) = collect_src(
            "struct Zed { x: i64 }\nstruct Mid { x: i64 }\nstatic SZ: i64 = 1;\nstatic SM: i64 = 2;\nfn main() {}\n",
            &mut order,
        );
        let (a2, s2) = collect_src(
            "struct Alpha { x: i64 }\nstruct Mid { x: i64 }\nstruct Zed { x: i64 }\nstatic SA: i64 = 3;\nstatic SM: i64 = 2;\nstatic SZ: i64 = 1;\nfn main() {}\n",
            &mut order,
        );
        assert_eq!(a1[1], a2[1], "Mid keeps its index");
        assert_eq!(a1[2], a2[2], "Zed keeps its index");
        assert_eq!(s1[1], s2[1], "SM keeps its index");
        assert_eq!(s1[2], s2[2], "SZ keeps its index");

        // A removed def leaves a hole: every other def keeps its index.
        let (a3, s3) = collect_src("struct Alpha { x: i64 }\nstruct Zed { x: i64 }\nstatic SA: i64 = 3;\nstatic SZ: i64 = 1;\nfn main() {}\n", &mut order);
        assert_eq!(a3[0], a2[0], "Alpha keeps its index after Mid goes");
        assert_eq!(a3[2], a2[2], "Zed keeps its index after Mid goes");
        assert_eq!(s3[0], s2[0], "SA keeps its index after SM goes");
        assert_eq!(s3[2], s2[2], "SZ keeps its index after SM goes");
    }

    /// Instance Adt ids are session places (`collect::InstOrder`): a new
    /// instance made first in discovery and a new struct (one more
    /// template Adt) keep every other instance's id, so cached C that
    /// names `A<id>` keeps its meaning.
    #[test]
    fn instance_adt_ids_are_stable() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        let inst_ids = |src: &str, order: &mut collect::DefOrder| -> FxMap<u64, u32> {
            let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let program = collect::collect_with_order(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids, true, order).unwrap();
            inst_adt_ids(&program).into_iter().map(|(id, key)| (key, id)).collect()
        };
        let base = "struct W<T> { a: T }\nfn f() -> u8 { W { a: 1u8 }.a }\nfn g() -> u16 { W { a: 2u16 }.a }\n\
                    fn main() { println!(\"{} {}\", f(), g()); }\n";
        let first = base.replace("fn f() -> u8 {", "fn f() -> u8 { let _z = W { a: 3u32 };");
        let grown = format!("struct Fresh {{ v: u8 }}\n{first}");
        let mut order = collect::DefOrder::default();
        let a = inst_ids(base, &mut order);
        let b = inst_ids(&first, &mut order);
        let c = inst_ids(&grown, &mut order);
        assert_eq!((a.len(), b.len(), c.len()), (2, 3, 3));
        for (k, id) in &a {
            assert_eq!(b.get(k), Some(id), "a new instance first keeps the others' ids");
            assert_eq!(c.get(k), Some(id), "a new struct keeps every instance id");
        }
    }

    /// A disk-loaded def order is stale only when it names none of
    /// the current defs; any overlap (the same crate, edited) keeps
    /// it, and empty sides never count as stale.
    #[test]
    fn loaded_def_order_stale_only_without_overlap() {
        use crate::def::DefPathHash as H;
        let ids = |hs: &[u64]| -> FxMap<H, u32> { hs.iter().enumerate().map(|(i, h)| (H(*h), i as u32)).collect() };
        let mut order = collect::DefOrder::default();
        assert!(!def_order_stale(&order, &ids(&[1]), &ids(&[])), "empty order");
        order.adts = vec![H(10), H(20)];
        order.statics = vec![H(30)];
        assert!(def_order_stale(&order, &ids(&[1, 2]), &ids(&[3])), "no overlap");
        assert!(!def_order_stale(&order, &ids(&[20, 2]), &ids(&[3])), "Adt overlap");
        assert!(!def_order_stale(&order, &ids(&[1]), &ids(&[30])), "static overlap");
        assert!(!def_order_stale(&order, &ids(&[]), &ids(&[])), "empty parse");
    }

    fn req_for(key: crate::protocol::SessionKey) -> Request {
        Request {
            cmd: Cmd::Check,
            file: key.krate.root.clone(),
            session: key,
            out: PathBuf::from("/tmp/out"),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false, cc: false, overlay: Default::default(),
            client: Default::default(),
        }
    }

    /// Routing guard: a request for another crate selection never compiles in
    /// this session (code 3 before any file read), and a non-host target is a
    /// clear code 2, not a host build under a foreign name.
    #[test]
    fn compile_refuses_a_misrouted_request() {
        let dir = PathBuf::from("/tmp/lust-route-test");
        let a = crate::protocol::SessionKey::synthetic(std::path::Path::new("/tmp/nope/a.rs"), false);
        let mut b = crate::protocol::SessionKey::synthetic(std::path::Path::new("/tmp/nope/a.rs"), false);
        b.features = vec!["alpha".into()];
        let mut s = Session::new(dir.clone(), false, a.clone());
        let r = compile(&req_for(b), &mut s);
        assert_eq!(r.code, 3);
        assert!(r.stderr.contains("wrong session"), "{}", r.stderr);
        let mut foreign = a;
        foreign.target_triple = "wasm32-wasip1".into();
        let req = req_for(foreign.clone());
        let mut s = Session::new(dir, false, foreign);
        let r = compile(&req, &mut s);
        assert_eq!(r.code, 2);
        assert!(r.stderr.contains("unsupported target"), "{}", r.stderr);
    }

    /// Resolver routing follows the current text: after a `static` item
    /// routes one compile through the worklist, deleting it must route
    /// the next compile through the chunk path again, exactly as a fresh
    /// session would, and the answers must match. Sticky routing made a
    /// warm session answer through the other front end for the same
    /// bytes (fuzz realish seed 107, iter 585).
    #[test]
    fn resolver_routing_unsticks_when_trigger_goes() {
        let dir = std::env::temp_dir().join(format!("lust-unstick-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("route.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let req = req_for(key.clone());
        let mut s = Session::new(dir.join("obj"), false, key.clone());
        std::fs::write(&file, "static S: i64 = 1;\nfn main() { println!(\"{}\", S); }\n").unwrap();
        let r = compile(&req, &mut s);
        assert_eq!(r.code, 0, "primer: {}", r.stderr);
        assert!(s.front.resolved_crate, "the static item routes through the resolver");
        std::fs::write(&file, "fn main() { println!(\"{}\", xformat!(\"{}\", 1)); }\n").unwrap();
        let warm = compile(&req, &mut s);
        assert!(!s.front.resolved_crate, "routing falls back when the trigger is gone");
        let mut fresh = Session::new(dir.join("obj2"), false, key);
        let cold = compile(&req, &mut fresh);
        assert_eq!(warm.code, 1);
        assert_eq!(warm.code, cold.code);
        assert_eq!(warm.stderr, cold.stderr);
        assert!(warm.stderr.contains("L0802"), "{}", warm.stderr);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A chunk re-parse replaces that chunk's body items: check a file
    /// with a fn nested in `main`, then change another fn's signature
    /// and build. The old splice kept the stale nested fn in
    /// `stmt_items` next to its fresh copy, so collect made one fn
    /// more than `fn_slot` and the build re-emit loop panicked (found
    /// by fx-seed658). A body-only edit of the outer fn takes the
    /// bodies fall-back and must stay exact too.
    #[test]
    fn chunk_reparse_replaces_body_items() {
        let dir = std::env::temp_dir().join(format!("lust-nest-splice-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("nest.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let check = req_for(key.clone());
        let build = Request { cmd: Cmd::Build, out: dir.join("nest.bin"), ..req_for(key.clone()) };
        let mut s = Session::new(dir.join("obj"), true, key.clone());
        std::fs::write(
            &file,
            "fn f0(x: i64) -> i64 {\n    x\n}\n\nfn main() {\n    let p = 1;\n    fn zed() -> i64 { 3 }\n    println!(\"{} {}\", p + f0(1), zed());\n}\n",
        )
        .unwrap();
        let r = compile(&check, &mut s);
        assert_eq!(r.code, 0, "primer: {}", r.stderr);
        assert_eq!(s.front.ast.stmt_items.len(), 1, "one nested fn after the primer");
        std::fs::write(
            &file,
            "fn f0(x: i64, _z: i64) -> i64 {\n    x\n}\n\nfn main() {\n    let p = 1;\n    fn zed() -> i64 { 3 }\n    println!(\"{} {}\", p + f0(1, 2), zed());\n}\n",
        )
        .unwrap();
        let warm = compile(&build, &mut s);
        assert_eq!(warm.code, 0, "signature edit: {}", warm.stderr);
        assert_eq!(s.front.ast.stmt_items.len(), 1, "the re-parsed chunk replaced its body items");
        assert_eq!(s.front.fn_slot.len(), 3, "one slot per fn, nested fn included once");
        let out = run_bin(&dir.join("nest.bin"));
        assert_eq!(String::from_utf8_lossy(&out.stdout), "2 3\n");
        std::fs::write(
            &file,
            "fn f0(x: i64, _z: i64) -> i64 {\n    x\n}\n\nfn main() {\n    let p = 10;\n    fn zed() -> i64 { 3 }\n    println!(\"{} {}\", p + f0(1, 2), zed());\n}\n",
        )
        .unwrap();
        let warm = compile(&build, &mut s);
        assert_eq!(warm.code, 0, "body edit: {}", warm.stderr);
        assert_eq!(s.front.ast.stmt_items.len(), 1, "still one nested fn after the body edit");
        let out = run_bin(&dir.join("nest.bin"));
        assert_eq!(String::from_utf8_lossy(&out.stdout), "11 3\n");
        let cold_build = Request { out: dir.join("nest-cold.bin"), ..build };
        let cold = compile(&cold_build, &mut Session::new(dir.join("obj2"), false, key));
        assert_eq!((warm.code, &warm.stderr), (cold.code, &cold.stderr), "warm and cold answers match");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// `lust check` checks no std platform body (`Program::check_skips`),
    /// and a build in the same session still checks and runs them: the
    /// build after a check prints what a cold build prints.
    #[test]
    fn check_skips_std_platform_bodies() {
        let dir = std::env::temp_dir().join(format!("lust-platskip-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("plat.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let check = req_for(key.clone());
        let build = Request { cmd: Cmd::Build, out: dir.join("plat.bin"), ..req_for(key.clone()) };
        std::fs::write(&file, "use std::io::Write;\n\nfn main() {\n    writeln!(std::io::stdout(), \"hi {}\", 1).unwrap();\n}\n").unwrap();
        let mut s = Session::new(dir.join("obj"), true, key.clone());
        let r = compile(&check, &mut s);
        assert_eq!(r.code, 0, "check: {}", r.stderr);
        let work = |s: &Session| (s.caches.gen_reuse.templates_checked, s.caches.gen_reuse.discovery_checked);
        assert_eq!(work(&s), (0, 1), "check ran std template or discovery checks (templates, bodies)");
        let r = compile(&build, &mut s);
        assert_eq!(r.code, 0, "build after check: {}", r.stderr);
        assert!(work(&s).0 > 50, "the build checks the std templates: {:?}", work(&s));
        let out = run_bin(&dir.join("plat.bin"));
        assert_eq!(String::from_utf8_lossy(&out.stdout), "hi 1\n");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Warm and cold checks of a resolver-routed file over the item segment
    /// size agree byte for byte at every step: a body edit, a late type
    /// error, a late borrow error, their fixes, and a route flip (the `use`
    /// line goes, so the file leaves the resolver, then comes back). The
    /// warm daemon session parses the file whole; each cold one-shot
    /// session parses it in item segments.
    #[test]
    fn warm_and_cold_agree_on_a_segmented_file() {
        let dir = std::env::temp_dir().join(format!("lust-warmbig-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("big.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let req = Request { json: true, ..req_for(key.clone()) };
        let mut orig = String::from("use std::collections::HashMap;\n");
        for i in 0..320 {
            let prev = if i == 0 { "t".to_string() } else { format!("run{}(t % 7)", i - 1) };
            orig += &format!(
                "#[derive(Debug, Clone, PartialEq)]\nenum Kind{i} {{ A(i64), B {{ x: i64, y: i64 }}, C }}\n\
                 struct S{i} {{ id: i64, name: String, kind: Kind{i}, items: Vec<i64> }}\n\
                 fn make{i}(n: i64) -> S{i} {{\n    let kind = if n % 3 == 0 {{ Kind{i}::A(n) }} else if n % 3 == 1 {{ Kind{i}::B {{ x: n, y: n * 2 }} }} else {{ Kind{i}::C }};\n    \
                 S{i} {{ id: n, name: format!(\"s{{}}\", n), kind, items: vec![n, n + 1, n + 2] }}\n}}\n\
                 fn score{i}(s: &S{i}) -> i64 {{\n    let mut total = s.id + s.name.len() as i64;\n    for v in &s.items {{ total += *v; }}\n    \
                 match &s.kind {{ Kind{i}::A(v) => total + v, Kind{i}::B {{ x, y }} => total + x * y, Kind{i}::C => total - 1 }}\n}}\n\
                 fn run{i}(n: i64) -> i64 {{ let s = make{i}(n); let t = score{i}(&s); if t > 100 {{ t - {prev} }} else {{ t }} }}\n"
            );
        }
        orig += "fn main() { let n = std::env::args().count() as i64; println!(\"{}\", run319(n)); }\n";
        let interner = crate::intern::Interner::default();
        let toks = lexer::lex(&orig, crate::diag::FileId(0), 0, &interner).unwrap().tokens;
        assert!(toks.len() > 16 * 4096, "over the item segment size: {} tokens", toks.len());
        let steps = [
            ("orig", orig.clone()),
            ("body edit", orig.replace("t - run318(t % 7)", "t - run318(t % 7) + 1")),
            ("late type error", orig.clone() + "fn zzz() -> i64 { \"bad\" }\n"),
            ("fixed", orig.clone()),
            ("late borrow error", orig.clone() + "fn zzz() -> usize { let s = String::from(\"a\"); let t = s; s.len() + t.len() }\n"),
            ("fixed again", orig.clone()),
            ("route flip", orig.replacen("use std::collections::HashMap;\n", "", 1)),
            ("route back", orig.clone()),
        ];
        let mut warm = Session::new(dir.join("warm"), true, key.clone());
        let mut codes = Vec::new();
        for (k, (name, text)) in steps.iter().enumerate() {
            std::fs::write(&file, text).unwrap();
            let w = compile(&req, &mut warm);
            assert_eq!(warm.front.resolved_crate, *name != "route flip", "step {name}: routing");
            let c = compile(&req, &mut Session::new(dir.join(format!("cold{k}")), false, key.clone()));
            assert_eq!((w.code, &w.stdout, &w.stderr), (c.code, &c.stdout, &c.stderr), "step {name}: warm vs cold");
            codes.push(w.code);
        }
        assert_eq!(codes, [0, 0, 1, 0, 1, 0, 0, 0], "each step's expected answer");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// What a warm chunk-path Ast must share with a cold parse of the same
    /// text: the spans of items, impls, and fn names; the closures and
    /// `a::b` value paths whole-arena scans see; and per fn (in `fn_loc`
    /// order) the sizes of its `exprs` and `pats` ranges and its closures.
    type ChunkShape = (Vec<(u32, u32)>, usize, usize, Vec<(u32, u32, usize)>);

    fn chunk_shape(s: &Session) -> ChunkShape {
        use crate::ast::Expr;
        let ast = &s.front.ast;
        let mut spans = Vec::new();
        for it in &ast.items {
            spans.push((it.span.lo, it.span.hi));
            match &it.kind {
                ItemKind::Fn(f) => spans.push((f.name_span.lo, f.name_span.hi)),
                ItemKind::Impl(imp) => {
                    spans.push((imp.span.lo, imp.span.hi));
                    spans.extend(imp.fns.iter().map(|f| (f.name_span.lo, f.name_span.hi)));
                }
                _ => {}
            }
        }
        let closure = |e: &Expr| matches!(e, Expr::Closure { .. });
        let closures = ast.exprs.iter().filter(|e| closure(e)).count();
        let paths = ast.exprs.iter().filter(|e| matches!(e, Expr::Path(segs) if segs.len() > 1)).count();
        let fns = s
            .front
            .fn_loc
            .iter()
            .map(|&(item, sub)| {
                let d = fn_def_at(ast, item, sub);
                let n = (d.exprs.0..d.exprs.1).filter(|&x| closure(&ast.exprs[x as usize])).count();
                (d.exprs.1 - d.exprs.0, d.pats.1 - d.pats.0, n)
            })
            .collect();
        (spans, closures, paths, fns)
    }

    /// The chunk path's bodies and signatures modes leave the same Ast a
    /// cold parse builds (fuzz realish seeds 42, 123, 777: a body edit
    /// that removed bytes left the span of a std impl spliced after the
    /// user text in place, and the impl fell out of the std method range,
    /// L0102). Each step's warm answer and Ast shape equal a cold
    /// session's: a body edit that removes lines; a body edit of a fn
    /// with a parameter pattern (signatures mode: bodies mode would widen
    /// its expression range over other fns' closures); a body that drops
    /// a closure and a bad path (their dead nodes must not stay visible);
    /// one write that edits two bodies; a body syntax error, then a
    /// signature edit elsewhere while it stands, then its fix; a body
    /// syntax error, the same text again, then the text before it (fuzz
    /// realish seed 314: the error requests blanked a chunk's items, and
    /// bodies mode must not run on that Ast).
    #[test]
    fn chunk_modes_match_a_cold_parse() {
        let dir = std::env::temp_dir().join(format!("lust-chunk-modes-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("modes.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let req = req_for(key.clone());
        let pad: String = (0..40).map(|i| format!("    let p{i} = {i};\n    t += p{i};\n")).collect();
        // Over 64 KiB, so the file splits into many chunks.
        let fill: String = (0..1600).map(|i| format!("fn fill{i}(n: i64) -> i64 {{\n    n + {i}\n}}\n")).collect();
        let v0 = format!(
            "fn total(xs: &[i64]) -> i64 {{\n    let mut t = 0;\n    for x in xs {{\n        t += x;\n    }}\n{pad}    t\n}}\n\
             {fill}\
             fn pair((a, b): (i64, i64)) -> i64 {{\n    let f = |x: i64| x + a;\n    f(b)\n}}\n\
             fn twice(n: i64) -> i64 {{\n    let g = |x: i64| x * 2;\n    g(n)\n}}\n\
             fn main() {{\n    let r: Result<i64, String> = Ok(total(&[1, 2, 3]));\n    let o: Option<i64> = r.ok().map(|v| v * 2);\n    \
             println!(\"{{}} {{}} {{}} {{}}\", o.unwrap_or(0), pair((1, 2)), twice(3), fill7(1));\n}}\n"
        );
        let v1 = v0.replace(&pad, "");
        let v2 = v1.replace("x + a;", "x + a + 1;");
        let v3 = v2.replace("    let g = |x: i64| x * 2;\n    g(n)\n", "    n * 2\n");
        let v4 = v3.replace("    n * 2\n", "    let m = HashMap::<i64, i64>::new();\n    n * 2\n");
        let v5 = v3.clone();
        let v6 = v5.replace("        t += x;\n", "        t += x + 0;\n").replace("    n * 2\n", "    n * 2 + 0\n");
        let v7 = v6.replace("        t += x + 0;\n", "        t += ;\n");
        let v8 = v7.replace("fn fill1500(n: i64) -> i64 {\n    n + 1500\n", "fn fill1500(n: i64, _k: u8) -> i64 {\n    n + 1500\n");
        let v9 = v8.replace("        t += ;\n", "        t += x;\n");
        // A signature edit first, so every chunk holds parsed items again.
        let v10 = v9.replace("fn fill1500(n: i64, _k: u8) -> i64 {", "fn fill1500(n: i64) -> i64 {");
        let v11 = v10.replace("        t += x;\n", "        t += x;\n        for\n");
        let steps = [
            ("primer", &v0, Some("full")),
            ("lines removed", &v1, Some("bodies")),
            ("param pattern", &v2, Some("signatures")),
            ("closure dropped", &v3, Some("bodies")),
            ("bad path", &v4, None),
            ("bad path gone", &v5, Some("bodies")),
            ("two bodies", &v6, Some("signatures")),
            ("syntax error", &v7, None),
            ("signature edit under it", &v8, None),
            ("fixed", &v9, None),
            ("signature back", &v10, Some("signatures")),
            ("body error again", &v11, None),
            ("same text", &v11, None),
            ("restored", &v10, Some("signatures")),
        ];
        let mut warm = Session::new(dir.join("warm"), true, key.clone());
        let mut codes = Vec::new();
        for (k, (name, text, mode)) in steps.iter().enumerate() {
            std::fs::write(&file, text).unwrap();
            let w = compile(&req, &mut warm);
            let mut cold_session = Session::new(dir.join(format!("cold{k}")), false, key.clone());
            let c = compile(&req, &mut cold_session);
            assert_eq!((w.code, &w.stderr), (c.code, &c.stderr), "step {name}: warm vs cold");
            codes.push(w.code);
            if let Some(mode) = mode {
                assert_eq!(w.code, 0, "step {name}: {}", w.stderr);
                let why = warm.front.last_visits.split_whitespace().find_map(|kv| kv.strip_prefix("why=")).unwrap_or("");
                assert_eq!(why, *mode, "step {name}: chunk mode");
                assert!(chunk_shape(&warm) == chunk_shape(&cold_session), "step {name}: warm Ast shape vs cold");
            }
        }
        assert_eq!(codes, [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0], "each step's expected answer");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
