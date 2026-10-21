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
