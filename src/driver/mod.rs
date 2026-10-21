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

/// Source texts that stand in for files on disk, by canonical path, for this
/// process: `lust test` of a Cargo target adds its harness shims to copies of
/// the crate's files and builds those (testrun.rs). Every crate source read
/// (the root, module files) goes through `read_source`, and the disk cache is
/// off while an overlay is set, as under `protocol::source_override`.
static SOURCE_OVERLAY: std::sync::OnceLock<std::collections::HashMap<String, String>> = std::sync::OnceLock::new();

/// Sets this process's source overlay (once; a later call is ignored).
pub fn set_source_overlay(files: std::collections::HashMap<String, String>) {
    let _ = SOURCE_OVERLAY.set(files);
}

/// True when this process has a source overlay.
pub fn has_source_overlay() -> bool {
    SOURCE_OVERLAY.get().is_some_and(|m| !m.is_empty())
}

/// The text of a crate source file: the overlay's, else the file's.
pub fn read_source(path: &std::path::Path) -> std::io::Result<String> {
    if let Some(text) = SOURCE_OVERLAY.get().and_then(|m| m.get(&crate::resolve::modules::canonical_string(path))) {
        return Ok(text.clone());
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
