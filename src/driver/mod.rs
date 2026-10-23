// The driver: session state (session.rs), the whole-request disk cache (cache.rs),
// and the compile pipeline (compile.rs). Callers use the re-exports below, so the
// public paths (`driver::Session`, `driver::compile`, `driver::cache::Cache`) stay
// stable when items move between these files.
pub(crate) mod ast_hash;
mod ir_cache;
pub mod buildscript;
pub mod cache;
mod compile;
mod const_reach;
pub(crate) mod kept_delta;
mod kept_derive;
pub(crate) mod laps;
mod genreuse_oracle;
mod item_oracle;
mod resolve_oracle;
mod macro_scope;
mod item_outline;
pub(crate) mod gen_reuse;
pub mod graph;
mod patch;
pub(crate) mod sig_nodes;
mod span_shift;
mod session;
pub(crate) mod release_c;
pub mod read_cover;

pub use crate::protocol::{Cmd, Request, Response, SessionKey};

/// The source overlay of the compile running now (`Request::overlay`): source texts that
/// stand in for files on disk, by canonical path. `lust test` of a Cargo target adds its
/// harness shims to copies of the crate's files and builds those (testrun/krate.rs). Every
/// crate source read (the root, module files) goes through `read_source`, the warm patch path
/// compares overlay texts instead of trusting file stamps (patch.rs), and the disk cache is off
/// while an overlay is set, as under `protocol::source_override`.
///
/// One slot per process: compiles on the serve loop (or a cold process) run one at a time, and
/// `compile` sets the slot for each. A daemon guard check runs beside them, on background
/// threads (`pool::set_background`) that never read the slot: a guard compiles a request
/// without an overlay (the daemon starts none for one with an overlay).
static SOURCE_OVERLAY: std::sync::RwLock<Option<std::sync::Arc<std::collections::HashMap<String, String>>>> = std::sync::RwLock::new(None);

/// The active overlay as this thread sees it: None on a background thread.
fn active_overlay() -> Option<std::sync::Arc<std::collections::HashMap<String, String>>> {
    if crate::pool::is_background() {
        return None;
    }
    SOURCE_OVERLAY.read().unwrap_or_else(|e| e.into_inner()).clone()
}

/// Makes `overlay` the active one until the returned guard drops (an empty one clears it).
fn enter_overlay(overlay: &std::sync::Arc<std::collections::HashMap<String, String>>) -> impl Drop {
    struct Clear;
    impl Drop for Clear {
        fn drop(&mut self) {
            *SOURCE_OVERLAY.write().unwrap_or_else(|e| e.into_inner()) = None;
        }
    }
    *SOURCE_OVERLAY.write().unwrap_or_else(|e| e.into_inner()) = (!overlay.is_empty()).then(|| overlay.clone());
    Clear
}

/// True when this thread's compile has a source overlay.
pub fn has_source_overlay() -> bool {
    active_overlay().is_some()
}

/// The overlay text for `path`, if the active overlay has one.
pub(crate) fn overlay_text(path: &std::path::Path) -> Option<String> {
    active_overlay().and_then(|m| m.get(&crate::resolve::modules::canonical_string(path)).cloned())
}

/// The text of a crate source file: the overlay's, else the file's.
pub fn read_source(path: &std::path::Path) -> std::io::Result<String> {
    if let Some(text) = overlay_text(path) {
        return Ok(text);
    }
    std::fs::read_to_string(path)
}
pub use compile::{Stamps, defer_cc, drop_parked_cc, finish_parked_cc, parked_cc_result, release_bases, sweep_bases};
pub(crate) use item_oracle::failure as oracle_failure;
pub(crate) use patch::drop_unkept;

/// Compiles one request in `session` (`compile::compile`). Under the
/// patch oracle (`item_oracle.rs`) a daemon check request then compares
/// its answer with a fresh session's.
pub fn compile(req: &Request, session: &mut Session) -> Response {
    let _overlay = enter_overlay(&req.overlay);
    let resp = compile::compile(req, session);
    if item_oracle::on() {
        item_oracle::compare_response(req, session, &resp);
    }
    resp
}

/// `compile` without the oracle's response compare, for the daemon's
/// background guard checks: their file can change while they run, so a
/// second read of it may see other bytes.
pub fn compile_background(req: &Request, session: &mut Session) -> Response {
    let resp = compile::compile(req, session);
    if item_oracle::on() {
        item_oracle::forget(session);
    }
    resp
}
pub use session::Session;
