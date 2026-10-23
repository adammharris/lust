// `lust`: the thin command-line client. If a daemon serves this directory, it sends the request
// there (a warm, incremental compile). Otherwise it hands the command to `lust-core`, the compiler,
// and starts a daemon in the background so the next command is warm (autostart, below).
// It has no custom allocator and few dependencies, so it starts in about a millisecond.
//
//   lust check <file.rs> [--json] [--timings]     lust check <file.rs> --rustc (oracle)
//   lust build <file.rs> [-o <out>] [-g] [--emit-c <prefix>] [--timings]
//   lust build <file.rs> --release | --profile <name> [-o <out>]  (Cargo or rustc)
//   lust build <file.rs> --release --target <triple>...            (lust + zig cc, per target)
//   lust run   <file.rs> [-- <args>...]
//   lust daemon            serve warm, incremental compiles for this directory
//   lust port scan ...     gap report for a Rust crate (execs `lust-port`)
//
// Autostart: `LUST_NO_DAEMON=1` turns the daemon off entirely (no use, no start). The daemon detaches into its own session,
// logs to `daemon.log` in the cache dir, and exits after `LUST_DAEMON_IDLE` (default 30m).
#[path = "protocol.rs"]
mod protocol;

use protocol::Invocation;
use std::os::unix::io::AsRawFd;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};

unsafe extern "C" {
    fn setsid() -> i32;
    fn flock(fd: i32, operation: i32) -> i32;
    fn fcntl(fd: i32, cmd: i32, arg: i32) -> i32;
}
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;
const F_SETFD: i32 = 2;

/// True when an env flag is set to a value other than "" or "0".
fn env_on(name: &str) -> bool {
    matches!(std::env::var(name), Ok(v) if !v.is_empty() && v != "0")
}

/// Claims the right to start the daemon: an exclusive flock on the lock file. None when
/// a daemon (or a client that is starting one) holds it. The caller hands the locked fd
/// to the daemon it spawns, so the lock is held without a gap from here to the daemon's
/// exit, and a crash releases it. The file is never deleted: removing a file that a live
/// daemon holds a lock on would let a second daemon lock a new file at the same path.
fn claim_start(lock: &Path) -> Option<std::fs::File> {
    let f = std::fs::OpenOptions::new().write(true).create(true).truncate(false).open(lock).ok()?;
    // SAFETY: flock on the live fd of `f`. LOCK_NB: fail at once when the lock is taken.
    (unsafe { flock(f.as_raw_fd(), LOCK_EX | LOCK_NB) } == 0).then_some(f)
}

/// The cache dir for daemon logs. The same rule as the disk cache (src/driver/cache.rs).
fn log_dir(file: &Path) -> PathBuf {
    match std::env::var_os("LUST_CACHE_DIR") {
        Some(d) if !d.is_empty() => PathBuf::from(d),
        _ => file.parent().map_or_else(|| PathBuf::from("."), Path::to_path_buf).join(".lust-cache"),
    }
}

/// Allocator settings for a daemon process. mimalloc gives freed pages back to the OS 10 ms
/// after a request frees them, so the next warm request faults them in again: on ts_goport
/// that cost 100 ms to 2 s per request after a few seconds idle (w-tsedit). A daemon keeps
/// them (its RSS stays at its peak). A value the user set wins.
fn daemon_alloc_env() -> Vec<(&'static str, &'static str)> {
    if std::env::var_os("MIMALLOC_PURGE_DELAY").is_some() { Vec::new() } else { vec![("MIMALLOC_PURGE_DELAY", "-1")] }
}

/// Starts `lust-core daemon` detached (its own session, output to the log file), unless
/// autostart is off or another client or daemon already claims this socket. The current
/// command is still answered cold by the caller; the next one finds the daemon warm.
/// `prewarm`: the daemon checks `file` first (as a one-file program), once this process exits.
fn maybe_autostart(sock: &Path, file: &Path, core: &Path, prewarm: bool) {
    if env_on("LUST_NO_DAEMON") || protocol::source_override().is_some() {
        return;
    }
    let Some(lock) = claim_start(&protocol::daemon_lock_path(sock)) else { return };
    let lock_fd = lock.as_raw_fd();
    let dir = log_dir(file);
    let _ = std::fs::create_dir_all(&dir);
    let log = std::fs::OpenOptions::new().create(true).append(true).open(dir.join("daemon.log"));
    let mut cmd = std::process::Command::new(core);
    // The daemon pre-warms a session for this file, so the next command is warm. It
    // waits for this process to exit first (exec keeps the pid, so that is the cold
    // compile), so the pre-warm never competes with the command in front of it.
    cmd.arg("daemon").envs(daemon_alloc_env()).env("LUST_DAEMON_LOCK_FD", lock_fd.to_string()).stdin(std::process::Stdio::null());
    if prewarm {
        cmd.env("LUST_DAEMON_PREWARM", file).env("LUST_DAEMON_PREWARM_AFTER", std::process::id().to_string());
    }
    if let Ok(f) = log {
        if let Ok(f2) = f.try_clone() {
            cmd.stdout(f).stderr(f2);
        }
    }
    // SAFETY: pre_exec runs after fork, before exec. setsid gives the daemon its own
    // session, so it outlives this client and its terminal. Clearing close-on-exec on
    // the lock fd (in the child only) passes the held flock to the daemon. Both are
    // plain syscalls; no Rust code runs.
    unsafe {
        cmd.pre_exec(move || {
            setsid();
            fcntl(lock_fd, F_SETFD, 0);
            Ok(())
        });
    }
    // Not waited on: the daemon is reparented and serves in the background. This
    // process's copy of the lock fd closes on its own exec; the daemon's copy stays.
    if let Err(e) = cmd.spawn() {
        eprintln!("note: could not start a background daemon: {e}");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The package version and the build hash (which also keys the daemon socket and the cache).
    if matches!(args.first().map(String::as_str), Some("--version" | "-V")) {
        println!("lust {} (build {})", env!("CARGO_PKG_VERSION"), &env!("LUST_BUILD_HASH")[..8]);
        return;
    }
    // `lust port scan ...` runs the standalone `lust-port` binary
    // (tools/lust-port), found next to this executable like `lust-core`.
    if args.first().map(String::as_str) == Some("port") {
        let tool = std::env::current_exe().map(|p| p.with_file_name("lust-port")).unwrap_or_else(|_| "lust-port".into());
        let err = std::process::Command::new(&tool).args(&args[1..]).exec();
        eprintln!("error: cannot run {}: {err}", tool.display());
        std::process::exit(2);
    }
    let core = std::env::current_exe().map(|p| p.with_file_name("lust-core")).unwrap_or_else(|_| "lust-core".into());
    // A build that waits for its sources (`LUST_SOURCES_READY`, resolve/prefetch.rs) reads no
    // workspace file before they are there, and parsing its request reads the manifest: the
    // core takes the build at once and parses it after the wait, with no daemon.
    if protocol::waits_for_sources(&args) {
        let err = std::process::Command::new(&core).args(&args).exec();
        eprintln!("error: cannot run {}: {err}", core.display());
        std::process::exit(2);
    }
    match protocol::parse_args(&args) {
        // Release builds and the rustc oracle run right here, streaming output.
        Some(Invocation::Release { file, out, profile, debug, net }) => {
            protocol::run_release(&file, out.as_deref(), profile.as_deref(), debug, net)
        }
        // The release driver runs in lust-core (cold, one target after
        // another); the client only hands it the same arguments.
        Some(Invocation::ReleaseCc { .. }) => {
            let err = std::process::Command::new(&core).args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
        Some(Invocation::RustcCheck { file }) => protocol::run_rustc_check(&file),
        Some(Invocation::Compile { req, run, args: run_args }) => {
            let sock = protocol::socket_path();
            // LUST_NO_DAEMON means "do not use a daemon at all": neither
            // start one nor send work to a live one.
            // A std or adapter source override is never served warm (see
            // `protocol::source_override`).
            if !env_on("LUST_NO_DAEMON")
                && protocol::source_override().is_none()
                && let Some(resp) = protocol::request(&sock, &req)
            {
                protocol::finish(resp, run, &req.out, &run_args);
            }
            // No daemon answered: start one for the next command, answer this one cold.
            maybe_autostart(&sock, &req.file, &core, true);
            let err = std::process::Command::new(&core).args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
        // `lust test` of a Cargo target sends its build to a daemon
        // (src/testrun/krate.rs): start one for the next run. No pre-warm:
        // a check of the root as a one-file program is not the test build.
        _ if args.first().map(String::as_str) == Some("test") && args.iter().any(|a| a == "--manifest-path") => {
            if let Some(file) = args.get(1) {
                maybe_autostart(&protocol::socket_path(), Path::new(file), &core, false);
            }
            let err = std::process::Command::new(&core).args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
        // A daemon command or bad arguments: let the compiler handle it.
        _ => {
            let mut cmd = std::process::Command::new(&core);
            if args.first().map(String::as_str) == Some("daemon") {
                cmd.envs(daemon_alloc_env());
            }
            let err = cmd.args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
    }
}
