// `lust daemon`: keeps a warm compile session per crate selection (`SessionKey`,
// docs/ARCH.md section 1.8) and serves requests from the `lust` client over a Unix
// socket (see protocol.rs). One request at a time on the serve loop; background
// guard checks (below) compile in their own sessions on their own threads.
// One daemon per socket: it holds an flock on `<socket>.lock` (which holds its pid) for its
// whole life. A second daemon sees the lock taken and exits without touching the socket, so
// a stale socket file can always be removed safely by the lock holder. An autostarting
// client takes the same flock first and passes the locked fd to the daemon it spawns
// (`LUST_DAEMON_LOCK_FD`). Nothing deletes the lock file: a crash releases the flock.
// The daemon exits on its own after an idle span (`LUST_DAEMON_IDLE`, default 30 minutes;
// see protocol::daemon_idle) and removes its socket on the way out. SIGTERM, SIGINT, and
// removal of the socket file take the same controlled exit. Signals use a flag plus a
// self-pipe wakeup; socket removal uses an inotify watch on Linux. In both cases the
// serve loop does the cleanup.
// Temp state: sessions work under `<temp>/lust-daemon-<pid>/`, which every controlled
// exit deletes, and which a starting daemon also deletes for any pid that is gone
// (that is what cleans up after SIGKILL and crashes). Deleting it is safe for built
// executables: base libraries live in a persistent dir, not here (see
// `resolve_base_dir` in driver/compile.rs). On exit each base dir is swept too, so
// bases of deleted executables are removed while bases of kept executables stay.
// Bounds for a long session: at most `max_sessions` warm sessions (LRU eviction), and a
// hang watchdog (`spawn_hang_watchdog`) that exits when a request runs on after its client
// left, so one compile that never ends cannot wedge every later request. Every 100
// requests the log gets a stats line (RSS, sessions, expansion tables).
// Two safety nets watch the warm answers:
//   - A panic in one request is caught. That crate's session is dropped, the request is
//     answered by a fresh session at once, and the daemon keeps serving. A patch oracle
//     failure (LUST_CHECK_ITEMPATCH, driver/item_oracle.rs) is never retried: the client
//     gets it as an internal error (code 3), so a sweep sees it in the answer.
//   - The fresh-session guard: when the incremental answer is an error, the client gets
//     that answer at once and the request is redone in a fresh session in the background.
//     If the answers differ, the event is logged loudly (lines starting with "guard:"),
//     the warm session is dropped, and the next answer for that crate is recomputed in a
//     new session. The fresh compile is a one-shot one (a non-persistent session, as a
//     cold `lust check`): a second persistent session of a large crate doubled the
//     daemon's memory (ts_goport: 14 GB warm, the box's 32 GB OOM-killed the daemon). If they match, the warm session (and its caches)
//     is kept. Success answers are trusted as they are. Background results are compared
//     only when no input of either compile changed from the warm compile's start to the
//     end of the fresh one (`session_inputs`, `crate_inputs`, `changed_input`: every source file, expansion
//     input, Cargo file and build script record, not only the root), and they are applied
//     on the serve loop (`GuardJobs::drain`), never on the worker thread. The fuzz gate
//     waits for all started checks to finish (`guard-check: start/done` log lines) and
//     counts any "guard:" line as a failure, as it did when the guard was synchronous.
use crate::driver::{self, Request, Session};
use crate::protocol::{self, Response, SessionKey};
use std::collections::HashMap;
#[cfg(target_os = "linux")]
use std::ffi::CString;
use std::io::{BufReader, Seek, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::os::unix::io::{AsRawFd, FromRawFd};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::mpsc::{Receiver, Sender};

unsafe extern "C" {
    fn flock(fd: i32, operation: i32) -> i32;
    fn poll(fds: *mut PollFd, nfds: u64, timeout_ms: i32) -> i32;
    fn kill(pid: i32, sig: i32) -> i32;
    fn signal(signum: i32, handler: usize) -> usize;
    fn pipe(fds: *mut i32) -> i32;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn fcntl(fd: i32, cmd: i32, arg: i32) -> i32;
    fn getuid() -> u32;
    #[cfg(target_os = "linux")]
    fn setpriority(which: i32, who: u32, prio: i32) -> i32;
    #[cfg(target_os = "linux")]
    fn inotify_init1(flags: i32) -> i32;
    #[cfg(target_os = "linux")]
    fn inotify_add_watch(fd: i32, path: *const u8, mask: u32) -> i32;
    #[cfg(target_os = "linux")]
    fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
    #[cfg(target_os = "linux")]
    fn close(fd: i32) -> i32;
    #[cfg(target_os = "macos")]
    fn kqueue() -> i32;
    #[cfg(target_os = "macos")]
    fn kevent(kq: i32, changes: *const KEvent, nchanges: i32, events: *mut KEvent, nevents: i32, timeout: *const TimeSpec) -> i32;
}
const SIGINT: i32 = 2;
const SIGTERM: i32 = 15;
const F_SETFD: i32 = 2;
const FD_CLOEXEC: i32 = 1;
#[cfg(target_os = "linux")]
const IN_NONBLOCK: i32 = 0o4000;
#[cfg(target_os = "linux")]
const IN_CLOEXEC: i32 = 0o2000000;
const IN_MOVED_FROM: u32 = 0x40;
const IN_DELETE: u32 = 0x200;

/// Set by the SIGTERM/SIGINT handler; the serve loop sees it and exits
/// through the same cleanup as the idle timeout.
static SHUTDOWN: AtomicBool = AtomicBool::new(false);
/// The write end of the wakeup pipe the handler pokes, so a `poll` for
/// the idle timeout wakes at once instead of sleeping through a signal.
static WAKE_W: AtomicI32 = AtomicI32::new(-1);

/// Async-signal-safe: only a flag store and one pipe byte.
extern "C" fn on_shutdown_signal(_sig: i32) {
    SHUTDOWN.store(true, Ordering::SeqCst);
    let fd = WAKE_W.load(Ordering::SeqCst);
    if fd >= 0 {
        // SAFETY: `fd` is the pipe write end installed by `serve`; one byte.
        unsafe { write(fd, b"x".as_ptr(), 1) };
    }
}
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;
const POLLIN: i16 = 1;
const POLLERR: i16 = 0x8;
const POLLHUP: i16 = 0x10;
#[cfg(target_os = "linux")]
const POLLRDHUP: i16 = 0x2000;
#[cfg(not(target_os = "linux"))]
const POLLRDHUP: i16 = 0;

/// The request the serve loop is compiling: its connection fd and start
/// time, or None between requests. The hang watchdog reads it; the serve
/// loop clears it before the connection closes, so a set fd is always open.
static BUSY: std::sync::Mutex<Option<(i32, std::time::Instant)>> = std::sync::Mutex::new(None);

/// How long a request may run before the watchdog checks its client
/// (`LUST_DAEMON_HANG`, seconds, default 30; 0 turns the watchdog off).
fn hang_limit() -> Option<std::time::Duration> {
    match std::env::var("LUST_DAEMON_HANG").ok().and_then(|v| v.trim().parse::<u64>().ok()) {
        Some(0) => None,
        Some(n) => Some(std::time::Duration::from_secs(n)),
        None => Some(std::time::Duration::from_secs(30)),
    }
}

/// True when the peer of connection `fd` has closed it (the client was
/// killed, timed out, or got Ctrl-C). A client that still waits for its
/// answer has sent its whole request and reads, so no event is pending.
fn client_gone(fd: i32) -> bool {
    let mut pfd = PollFd { fd, events: POLLRDHUP, revents: 0 };
    // SAFETY: one valid pollfd for the duration of the call; timeout 0.
    unsafe { poll(&mut pfd, 1, 0) > 0 && pfd.revents & (POLLRDHUP | POLLHUP | POLLERR) != 0 }
}

/// Starts the hang watchdog. The daemon compiles one request at a time,
/// so a compile that never ends (a compiler bug) used to wedge it: every
/// later request queued behind it forever (fx-resolve3's probe sweep saw
/// every build time out after one such program). A Rust thread cannot be
/// stopped, so when a request has run past `limit` and its client is
/// gone, the daemon removes its socket and temp dir and exits. Queued
/// clients then get no answer and compile cold, and the next client
/// starts a new daemon. A slow compile whose client still waits is left
/// alone.
fn spawn_hang_watchdog(sock: PathBuf, base: PathBuf, limit: std::time::Duration) {
    let _ = std::thread::Builder::new().name("lust-hang-watch".into()).spawn(move || {
        loop {
            std::thread::sleep(std::time::Duration::from_millis(500));
            let busy = BUSY.lock().unwrap_or_else(|e| e.into_inner());
            if let Some((fd, since)) = *busy
                && since.elapsed() >= limit
                && client_gone(fd)
            {
                eprintln!(
                    "lust daemon: a request ran {} s and its client is gone (a compiler hang?); exiting so a new daemon can serve",
                    since.elapsed().as_secs()
                );
                let _ = std::fs::remove_file(&sock);
                let _ = std::fs::remove_dir_all(&base);
                std::process::exit(3);
            }
        }
    });
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

/// Waits until `listener` can accept, a shutdown signal pokes the wake
/// pipe, the socket watch reports an event, or `timeout` passes. None
/// timeout waits forever. True only for a readable listener; the caller
/// checks the signal flag and the socket watch itself. This is how the
/// idle exit costs no latency: no sleep-based polling.
fn wait_readable(listener: &UnixListener, wake: i32, socket_watch: i32, timeout: Option<std::time::Duration>) -> bool {
    let mut pfds = [
        PollFd { fd: listener.as_raw_fd(), events: POLLIN, revents: 0 },
        PollFd { fd: wake, events: POLLIN, revents: 0 },
        PollFd { fd: socket_watch, events: POLLIN, revents: 0 },
    ];
    let ms = timeout.map_or(-1, |d| d.as_millis().min(i32::MAX as u128) as i32);
    // SAFETY: valid pollfds over live fds (an unavailable socket watch is
    // -1, which poll ignores), for the duration of the call.
    unsafe { poll(pfds.as_mut_ptr(), 3, ms) > 0 && pfds[0].revents & POLLIN != 0 }
}

/// Starts an inotify watch for deletion or move-away of `sock` from its
/// parent directory and returns the watch fd, or -1 when the watch cannot
/// be set up (the daemon then keeps the other exits). Linux only.
#[cfg(target_os = "linux")]
fn watch_socket_removal(sock: &Path) -> i32 {
    let parent = match sock.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let Ok(parent) = CString::new(parent.as_os_str().as_bytes()) else { return -1 };
    // SAFETY: inotify_init1 takes only flags; add_watch gets a valid fd
    // and a NUL-terminated path that outlives the call.
    unsafe {
        let fd = inotify_init1(IN_NONBLOCK | IN_CLOEXEC);
        if fd < 0 {
            return -1;
        }
        if inotify_add_watch(fd, parent.as_ptr() as *const u8, IN_DELETE | IN_MOVED_FROM) < 0 {
            close(fd);
            return -1;
        }
        fd
    }
}

/// `struct kevent` (macOS, 64-bit).
#[cfg(target_os = "macos")]
#[repr(C)]
struct KEvent {
    ident: usize,
    filter: i16,
    flags: u16,
    fflags: u32,
    data: isize,
    udata: usize,
}

/// `struct timespec`.
#[cfg(target_os = "macos")]
#[repr(C)]
struct TimeSpec {
    sec: i64,
    nsec: i64,
}

/// The device and inode of the socket this daemon bound, taken when its
/// watch starts (`watch_socket_removal`): a socket at the path with
/// another identity is another daemon's, so this one's was removed.
#[cfg(target_os = "macos")]
static SOCKET_ID: std::sync::OnceLock<(u64, u64)> = std::sync::OnceLock::new();

/// Starts a kqueue watch on the parent directory of `sock` (a vnode
/// write: an entry was added, removed or renamed) and returns the kqueue
/// fd, which `poll` reports readable when an event is queued, or -1 when
/// the watch cannot be set up (the daemon then keeps the other exits).
/// The directory fd stays open for the daemon's life, as the watch needs.
#[cfg(target_os = "macos")]
fn watch_socket_removal(sock: &Path) -> i32 {
    use std::os::unix::fs::OpenOptionsExt;
    const O_EVTONLY: i32 = 0x8000;
    const EVFILT_VNODE: i16 = -4;
    const EV_ADD: u16 = 0x1;
    const EV_CLEAR: u16 = 0x20;
    const NOTE_DELETE: u32 = 0x1;
    const NOTE_WRITE: u32 = 0x2;
    const NOTE_RENAME: u32 = 0x20;
    let parent = match sock.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    // A socket gone before the watch leaves no identity: `socket_removed` then says so.
    if let Ok(md) = sock.symlink_metadata() {
        let _ = SOCKET_ID.set((md.dev(), md.ino()));
    }
    let Ok(dir) = std::fs::OpenOptions::new().read(true).custom_flags(O_EVTONLY).open(parent) else { return -1 };
    // SAFETY: kqueue takes no arguments; kevent gets that live kqueue fd,
    // one valid change record and no event buffer.
    unsafe {
        let kq = kqueue();
        if kq < 0 {
            return -1;
        }
        fcntl(kq, F_SETFD, FD_CLOEXEC);
        let change = KEvent {
            ident: dir.as_raw_fd() as usize,
            filter: EVFILT_VNODE,
            flags: EV_ADD | EV_CLEAR,
            fflags: NOTE_WRITE | NOTE_DELETE | NOTE_RENAME,
            data: 0,
            udata: 0,
        };
        if kevent(kq, &change, 1, std::ptr::null_mut(), 0, std::ptr::null()) < 0 {
            return -1;
        }
        std::mem::forget(dir);
        kq
    }
}

/// No socket watch on other platforms: the daemon keeps its other exits.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn watch_socket_removal(_sock: &Path) -> i32 {
    -1
}

/// True when raw inotify bytes hold a delete or move-away event for `name`.
fn socket_removal_event(buf: &[u8], name: &[u8]) -> bool {
    let mut at = 0usize;
    while at + 16 <= buf.len() {
        let mask = u32::from_ne_bytes(buf[at + 4..at + 8].try_into().unwrap());
        let len = u32::from_ne_bytes(buf[at + 12..at + 16].try_into().unwrap()) as usize;
        let Some(next) = at.checked_add(16).and_then(|n| n.checked_add(len)) else { return false };
        if next > buf.len() {
            return false;
        }
        let raw = &buf[at + 16..next];
        let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
        if mask & (IN_DELETE | IN_MOVED_FROM) != 0 && &raw[..end] == name {
            return true;
        }
        at = next;
    }
    false
}

/// True when the watched socket was removed since the last call. A call
/// with no pending events is one nonblocking read, so the serve loop can
/// ask after every wait at no polling cost.
#[cfg(target_os = "linux")]
fn socket_removed(watch: i32, sock: &Path) -> bool {
    if watch < 0 {
        return false;
    }
    let Some(name) = sock.file_name() else { return false };
    let mut buf = [0u8; 4096];
    // SAFETY: `watch` is a live inotify fd made by `watch_socket_removal`,
    // `buf` has room for the requested count, and the call is nonblocking.
    let n = unsafe { read(watch, buf.as_mut_ptr(), buf.len()) };
    if n <= 0 {
        return false;
    }
    // The fallback existence check covers event-queue overflow and a
    // removal that landed between the bind and the watch setup.
    socket_removal_event(&buf[..n as usize], name.as_bytes()) || sock.symlink_metadata().is_err()
}

/// True when the watched socket was removed since the last call. A call
/// with no pending events is one kevent call with a zero timeout, so the
/// serve loop can ask after every wait at no polling cost. A directory
/// event is any entry change there, so the socket's own stat decides: gone,
/// or another file (another daemon's socket) at its path.
#[cfg(target_os = "macos")]
fn socket_removed(watch: i32, sock: &Path) -> bool {
    if watch < 0 {
        return false;
    }
    let Some(&id) = SOCKET_ID.get() else { return true };
    let mut events: [KEvent; 8] = std::array::from_fn(|_| KEvent { ident: 0, filter: 0, flags: 0, fflags: 0, data: 0, udata: 0 });
    let zero = TimeSpec { sec: 0, nsec: 0 };
    // SAFETY: `watch` is the live kqueue fd made by `watch_socket_removal`,
    // `events` has room for the requested count, and the timeout is zero.
    let n = unsafe { kevent(watch, std::ptr::null(), 0, events.as_mut_ptr(), events.len() as i32, &zero) };
    if n <= 0 {
        return false;
    }
    match sock.symlink_metadata() {
        Ok(md) => id != (md.dev(), md.ino()),
        Err(_) => true,
    }
}

/// No socket watch on other platforms (`watch_socket_removal`).
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn socket_removed(_watch: i32, _sock: &Path) -> bool {
    false
}

/// The pid in a lust temp name (`lust-daemon-<pid>`, `lust-<pid>`,
/// `lust-test-<pid>`, `lust-rustc-check-<pid>.rmeta`), if the name is
/// exactly one of those shapes. Prefixes only: a name like
/// `lust-daemon-glue-<random>` is a test harness dir, not pid-owned.
fn stale_temp_pid(name: &str) -> Option<u32> {
    let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    if let Some(rest) = name.strip_prefix("lust-rustc-check-")
        && let Some(pid) = rest.strip_suffix(".rmeta")
    {
        return if digits(pid) { pid.parse().ok() } else { None };
    }
    for prefix in ["lust-daemon-", "lust-test-", "lust-"] {
        if let Some(rest) = name.strip_prefix(prefix) {
            return if digits(rest) { rest.parse().ok() } else { None };
        }
    }
    None
}

/// True when a process with `pid` exists. Signal 0, which fails with
/// EPERM for a pid owned by another user, plus the /proc fallback.
/// A reused pid reads as alive, which only keeps a stale dir longer.
pub(crate) fn pid_alive(pid: u32) -> bool {
    const EPERM: i32 = 1;
    // SAFETY: signal 0 only probes whether the pid exists.
    let probe = if pid > 0 && pid <= i32::MAX as u32 { unsafe { kill(pid as i32, 0) } } else { -1 };
    probe == 0
        || (probe < 0 && pid > 0 && std::io::Error::last_os_error().raw_os_error() == Some(EPERM))
        || Path::new(&format!("/proc/{pid}")).exists()
}

/// Deletes lust temp dirs and files from processes that are gone:
/// at daemon start, this is the cleanup for daemons and cold compiles
/// that died without one (SIGKILL, crash). Only exact pid-named
/// entries owned by the current user are removed; symlinks and
/// anything still running are left alone. Built executables do not
/// depend on these dirs (base libraries moved to a persistent dir).
fn sweep_stale_temp_dirs() {
    let tmp = std::env::temp_dir();
    let me = std::process::id();
    // SAFETY: getuid has no arguments and cannot fail.
    let uid = unsafe { getuid() };
    let Ok(rd) = std::fs::read_dir(&tmp) else { return };
    for e in rd.flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        let Some(pid) = stale_temp_pid(&name) else { continue };
        if pid == me || pid_alive(pid) {
            continue;
        }
        let path = e.path();
        let Ok(meta) = path.symlink_metadata() else { continue };
        if meta.uid() != uid {
            continue;
        }
        if meta.is_dir() {
            let _ = std::fs::remove_dir_all(&path);
        } else if meta.is_file() {
            let _ = std::fs::remove_file(&path);
        }
    }
}

/// The one controlled daemon exit (idle timeout, shutdown signals, and
/// socket removal):
/// sweep each session's base dir (dead executables lose their bases,
/// kept executables keep theirs), delete the per-daemon temp dir and
/// the socket, then exit. Guard workers may still run on a signal
/// exit; they die with the process, and any dir they recreate in the
/// last instant is stale-pid swept by the next daemon.
fn shutdown(sock: &Path, base: &Path, sessions: &HashMap<SessionKey, Entry>, why: &str) -> ! {
    let mut base_dirs: Vec<PathBuf> = Vec::new();
    for entry in sessions.values() {
        if let Some(dir) = entry.session.base_dir()
            && !base_dirs.iter().any(|d| d == dir)
        {
            base_dirs.push(dir.to_path_buf());
        }
    }
    for dir in &base_dirs {
        driver::sweep_bases(dir, std::process::id());
    }
    let _ = std::fs::remove_dir_all(base);
    let _ = std::fs::remove_file(sock);
    eprintln!("lust daemon: {why}, exiting");
    std::process::exit(0);
}

/// The per-request refresh key of one crate selection: the Cargo graph
/// key (protocol::graph_key, section 1.1) mixed with the build script
/// output hash (driver::buildscript). Routing by SessionKey alone would
/// reuse a session resolved under an old Cargo.toml, lock file, config,
/// or build script; when this key moves, the entry's session is
/// replaced before the request is served. `env` is the request's client
/// env: build script records are checked and re-run in it.
fn refresh_key(key: &SessionKey, env: Option<&[(String, String)]>) -> u64 {
    // Build script first: a stale record re-runs Cargo, which can
    // create or update Cargo.lock, and the graph key must describe
    // the graph as it stands after that run, not before it.
    let build_script = match protocol::manifest_dir(key) {
        Some(dir) => match crate::driver::buildscript::refresh(&dir, &crate::driver::cache::cache_dir(&key.krate.root), env) {
            r @ crate::driver::buildscript::Refresh::Failed { .. } => {
                if let crate::driver::buildscript::Refresh::Failed { error, .. } = &r {
                    eprintln!("lust daemon: build script refresh failed for {}: {error}", dir.display());
                }
                r.hash()
            }
            r => r.hash(),
        },
        None => 0,
    };
    protocol::graph_key(key) ^ build_script.rotate_left(17)
}

struct Entry {
    session: Session,
    /// Directory stem for this crate's sessions; fresh sessions get "<dir>r<n>".
    dir: PathBuf,
    resets: u64,
    /// The refresh key (graph key + build script hash) the current
    /// session was resolved under. See `refresh_key`.
    refresh_key: u64,
    /// Requests served for this key. A background guard carries the count at
    /// its spawn, so a slow older result cannot replace a session that a
    /// newer guard already replaced (`replaced_gen`).
    served: u64,
    replaced_gen: u64,
    /// A background guard found a mismatch: the next request for this key is
    /// recomputed in a brand-new session before it is answered.
    recompute_next: bool,
    /// When a request last used this entry; the least recent one is
    /// evicted first (`evict_lru`).
    last_used: std::time::Instant,
}

impl Entry {
    fn fresh_dir(&mut self) -> PathBuf {
        self.resets += 1;
        let mut d = self.dir.as_os_str().to_owned();
        d.push(format!("r{}", self.resets));
        PathBuf::from(d)
    }

    fn new(dir: PathBuf, key: SessionKey, env: Option<&[(String, String)]>) -> Entry {
        let rk = refresh_key(&key, env);
        Entry {
            session: Session::new(dir.clone(), true, key),
            dir,
            resets: 0,
            refresh_key: rk,
            served: 0,
            replaced_gen: 0,
            recompute_next: false,
            last_used: std::time::Instant::now(),
        }
    }
}

/// Replaces the entry's session with a brand-new one and deletes the
/// old session's object dir. Object dirs are pure temp state now that
/// base libraries live in a persistent dir, so a replaced session
/// (panic recovery, guard mismatch, graph change) must not leave its
/// dir behind for the daemon's whole life.
fn replace_session(entry: &mut Entry, key: &SessionKey) {
    let dir = entry.fresh_dir();
    let old = std::mem::replace(&mut entry.session, Session::new(dir, true, key.clone()));
    let _ = std::fs::remove_dir_all(old.obj_dir());
}

/// What one background fresh-session check found.
enum GuardOutcome {
    /// A fresh compile of the same inputs.
    Fresh(Response),
    /// The fresh compile panicked.
    Panicked,
    /// This input changed after the warm compile started: no comparison is possible.
    Stale(PathBuf),
    /// The serve loop saw this input changed while the check ran and
    /// stopped it (`GuardJobs::cancel_stale`): a stale check, cut short.
    Cancelled(PathBuf),
}

/// Every file a compile in `session` read for `req`: the root, each source
/// file of its map (module files, dependency sources), and each file an
/// expansion read (`include_str!` and friends). `crate_inputs` adds the files
/// that do not depend on the session. The request itself (command, flags,
/// client env and shown paths, crate selection) needs no entry: a guard
/// compiles a clone of the warm request, in this same daemon binary.
/// Cheap (no file system call), so the serve loop takes the warm session's.
/// An FxHash of the text of every file in the session's source map,
/// by path: the bytes the session's last compile read. The guard
/// compares the warm session's snapshot against the fresh one's, so
/// a fresh compile that read different bytes (an edit mid-read can
/// give it a truncated file) is stale by content, whatever the
/// filesystem clock says about the edit (`changed_input` is only as
/// fine as that clock; on a gate box a truncated read compared as a
/// guard mismatch, fx-defcheck round 3). Cheap: the texts are
/// already in the map.
fn session_text_hashes(session: &Session) -> crate::intern::FxMap<PathBuf, u64> {
    let map = &session.front.map;
    let mut out = crate::intern::FxMap::default();
    for k in 0..map.file_count() {
        let f = crate::diag::FileId(k as u32);
        let p = map.path(f);
        if p.is_empty() {
            continue;
        }
        // The map's hash of the bytes read, not of its kept text: a one-file
        // crate keeps none, and hashing "" for it made the proof blind there
        // (sd23_std_impl_hash: a truncated root answered L0130 against L0612).
        out.insert(PathBuf::from(p), map.text_hash(f));
    }
    out
}

fn session_inputs(session: &Session, req: &Request) -> Vec<PathBuf> {
    let front = &session.front;
    let mut paths = vec![req.file.clone()];
    for k in 0..front.map.file_count() {
        let p = front.map.path(crate::diag::FileId(k as u32));
        if !p.is_empty() {
            paths.push(PathBuf::from(p));
        }
    }
    for chunk in &front.chunks {
        for dep in &chunk.expand_deps {
            if let crate::expand::Dep::File { path, .. } = dep {
                paths.push(path.clone());
            }
        }
    }
    paths
}

/// The inputs of any compile of `req` besides its session's own files: the
/// Cargo files the graph key covers and the build script records. Read on
/// the guard's thread (a cache dir can hold many entries).
fn crate_inputs(req: &Request) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = protocol::graph_files(&req.session).into_iter().map(|(_, p)| p).collect();
    paths.extend(driver::buildscript::record_files(&driver::cache::cache_dir(&req.file)));
    paths
}

/// The first of `paths` that may have changed after `start` (the warm
/// compile's start), or None. A file's ctime moves on every write, truncate,
/// rename and delete, and nothing can set it back, so a ctime at or before
/// `start` proves the file held the same bytes from then until now: through
/// the warm compile and the fresh one, edits and reverts (A -> B -> A)
/// included. A missing file counts by its nearest existing directory, whose
/// ctime a delete moves. The proof is as fine as the filesystem's clock: an
/// edit in the first clock tick of the warm compile can read as older, which
/// at worst shows as a mismatch; it never hides one. Linux stamps file times
/// from a coarse clock (a few ms behind `SystemTime::now()`), so a ctime up to
/// `CTIME_SLACK` before `start` also counts as changed (stale, no compare).
fn changed_input(paths: &[PathBuf], start: std::time::SystemTime) -> Option<PathBuf> {
    const CTIME_SLACK: std::time::Duration = std::time::Duration::from_millis(50);
    let start = start.duration_since(std::time::UNIX_EPOCH).unwrap_or_default().saturating_sub(CTIME_SLACK);
    let start = (start.as_secs() as i64, start.subsec_nanos() as i64);
    let newer = |md: &std::fs::Metadata| (md.ctime(), md.ctime_nsec()) > start;
    paths
        .iter()
        .find(|p| match p.symlink_metadata() {
            // A symlinked file: its link and its target both count.
            Ok(md) => newer(&md) || (md.file_type().is_symlink() && std::fs::metadata(p).map_or(true, |t| newer(&t))),
            Err(_) => p.ancestors().skip(1).find_map(|d| d.symlink_metadata().ok()).map_or(true, |md| newer(&md)),
        })
        .cloned()
}

/// Test knob (`LUST_GUARD_HOLD_MS`, default 0): a guard worker waits this
/// long before and after its fresh compile, so a daemon scenario can edit
/// files while a check is in flight.
fn guard_hold() {
    if let Some(ms) = std::env::var("LUST_GUARD_HOLD_MS").ok().and_then(|v| v.trim().parse::<u64>().ok()) {
        std::thread::sleep(std::time::Duration::from_millis(ms));
    }
}

/// One finished background check, sent from its worker thread to the serve loop.
struct GuardDone {
    seq: u64,
    key: SessionKey,
    served: u64,
    /// The answer the client already got.
    warm: Response,
    /// The fresh session's object dir (always removed).
    dir: PathBuf,
    outcome: GuardOutcome,
}

/// Background fresh-session checks: spawn on the serve loop, apply on the
/// serve loop. Workers only compile in their own fresh session and send the
/// result back; they never touch the session map. Start and done log lines
/// come in pairs by sequence number, so a reader of the daemon log (the fuzz
/// gate) can wait until every started check has been applied.
struct GuardJobs {
    tx: Sender<GuardDone>,
    rx: Receiver<GuardDone>,
    next_seq: u64,
    pending: usize,
    /// The checks in flight, for `cancel_stale`. At most one runs at a time:
    /// each is a cold compile, and on a large crate (ts_goport) a reject every
    /// few seconds stacked four to six of them next to the warm session
    /// until the kernel killed the daemon for memory.
    running: Vec<RunningGuard>,
    /// Started checks that wait for the running one, oldest first. One whose
    /// inputs change while it waits ends as `cancelled` and never runs.
    queued: std::collections::VecDeque<QueuedGuard>,
}

/// A started check that has not begun its compile yet (`GuardJobs::spawn`).
struct QueuedGuard {
    seq: u64,
    req: Request,
    warm: Response,
    inputs: Vec<PathBuf>,
    /// The warm session's source texts at spawn (`session_text_hashes`).
    texts: crate::intern::FxMap<PathBuf, u64>,
    /// `inputs` plus the request's root and crate files: what `cancel_stale` watches.
    watch: Vec<PathBuf>,
    start: std::time::SystemTime,
    dir: PathBuf,
    served: u64,
}

/// One check in flight: the warm inputs it compares under, the warm
/// compile's start, and its cancel flag (`pool::set_background`).
struct RunningGuard {
    seq: u64,
    inputs: Vec<PathBuf>,
    start: std::time::SystemTime,
    cancel: std::sync::Arc<AtomicBool>,
    /// The changed input that cancelled it.
    why: Option<PathBuf>,
}

/// The nice value of a guard thread and the phase threads it starts
/// (Linux threads inherit it): serve work runs first when both want a core.
#[cfg(target_os = "linux")]
const GUARD_NICE: i32 = 10;

impl GuardJobs {
    fn new() -> GuardJobs {
        let (tx, rx) = std::sync::mpsc::channel();
        GuardJobs { tx, rx, next_seq: 0, pending: 0, running: Vec::new(), queued: std::collections::VecDeque::new() }
    }

    /// Cancels every check in flight whose inputs changed since its warm
    /// compile started (the test the check itself applies when it ends:
    /// its answer could only be stale). The serve loop calls it as a
    /// request comes in. A check on unchanged inputs runs to its end. A
    /// queued check whose inputs changed ends here, without a compile.
    fn cancel_stale(&mut self) {
        for g in self.running.iter_mut().filter(|g| g.why.is_none()) {
            if let Some(path) = changed_input(&g.inputs, g.start) {
                g.cancel.store(true, Ordering::Relaxed);
                g.why = Some(path);
            }
        }
        let pending = &mut self.pending;
        self.queued.retain(|q| match changed_input(&q.watch, q.start) {
            Some(path) => {
                *pending -= 1;
                let _ = std::fs::remove_dir_all(&q.dir);
                eprintln!("guard-check: done {} cancelled for {} ({} changed while queued)", q.seq, q.req.session.krate.root.display(), path.display());
                false
            }
            None => true,
        });
    }

    /// Starts the oldest queued check whose inputs still stand, when none runs.
    fn start_next(&mut self) {
        if self.running.is_empty() {
            self.cancel_stale();
            if let Some(q) = self.queued.pop_front() {
                self.launch(q);
            }
        }
    }

    /// Redoes `req` in a fresh session on a new thread. `inputs` are the
    /// warm session's input files (`session_inputs`) and `start` is when the
    /// warm compile started. After its compile the worker adds the fresh
    /// session's own inputs and compares only when none of them changed
    /// since `start` (`changed_input`), so an edit anywhere in the crate
    /// during either compile reads as stale, never as a guard mismatch.
    /// While another check runs, this one waits in `queued` (its start
    /// line is logged now, so log readers count it as pending).
    fn spawn(
        &mut self,
        req: Request,
        warm: Response,
        inputs: Vec<PathBuf>,
        texts: crate::intern::FxMap<PathBuf, u64>,
        start: std::time::SystemTime,
        dir: PathBuf,
        served: u64,
    ) {
        self.next_seq += 1;
        let seq = self.next_seq;
        self.pending += 1;
        eprintln!("guard-check: start {seq} for {}", req.file.display());
        let mut watch = inputs.clone();
        watch.push(req.file.clone());
        watch.extend(crate_inputs(&req));
        let q = QueuedGuard { seq, req, warm, inputs, texts, watch, start, dir, served };
        if self.running.is_empty() && self.queued.is_empty() {
            self.launch(q);
        } else {
            self.queued.push_back(q);
        }
    }

    /// Runs one check on its own thread (see `spawn`).
    fn launch(&mut self, q: QueuedGuard) {
        let QueuedGuard { seq, req, warm, inputs, texts, watch, start, dir, served } = q;
        let tx = self.tx.clone();
        let key = req.session.clone();
        let cancel = std::sync::Arc::new(AtomicBool::new(false));
        self.running.push(RunningGuard { seq, inputs: watch, start, cancel: cancel.clone(), why: None });
        // The guard compiles like the serve loop, so it gets the
        // compiler stack size (see `pool::STACK_SIZE`).
        let _ = crate::pool::thread("lust-guard").spawn(move || {
            let work_dir = dir.clone();
            // Background work: off the pool, at a lower priority (on Linux,
            // `setpriority` of process 0 sets this thread's nice), cancellable.
            #[cfg(target_os = "linux")]
            unsafe {
                setpriority(0, 0, GUARD_NICE)
            };
            crate::pool::set_background(Some(cancel.clone()));
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                guard_hold();
                // Non-persistent, as a cold one-shot compile: no read sets,
                // patch base, or kept program, so it needs a fraction of the
                // warm session's memory, and it frees its program at the end.
                let mut fresh = Session::new(work_dir, false, req.session.clone());
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile_background(&req, &mut fresh))) {
                    // A cancelled check never compares, whatever its compile gave.
                    _ if cancel.load(Ordering::Relaxed) => GuardOutcome::Cancelled(PathBuf::new()),
                    Ok(resp) => {
                        guard_hold();
                        // req.file even when it did not parse (then no
                        // session lists it).
                        let mut all = inputs;
                        all.push(req.file.clone());
                        all.extend(session_inputs(&fresh, &req));
                        all.extend(crate_inputs(&req));
                        all.sort();
                        all.dedup();
                        // The ctime proof first (it also covers the
                        // inputs no source map holds). Then the
                        // content proof: every text the fresh
                        // compile read must be a text the warm
                        // session read, byte for byte. An edit the
                        // filesystem clock cannot order (it can lag
                        // the realtime clock by far more than the
                        // ctime slack on a loaded or virtualized
                        // box) still changes the bytes, so a fresh
                        // compile that read a file mid-write (a
                        // truncated root once answered L0130 no
                        // `main` against the warm L0110) reads as
                        // stale here, never as a mismatch.
                        let fresh_texts = session_text_hashes(&fresh);
                        let text_diff = fresh_texts.iter().find(|(p, h)| texts.get(*p) != Some(*h)).map(|(p, _)| p.clone());
                        match changed_input(&all, start) {
                            Some(path) => GuardOutcome::Stale(path),
                            None => match text_diff {
                                Some(path) => GuardOutcome::Stale(path),
                                None => GuardOutcome::Fresh(resp),
                            },
                        }
                    }
                    Err(_) => GuardOutcome::Panicked,
                }
            }));
            // A panic anywhere in the worker still produces a done record, so
            // `pending` and the log's start/done counts always settle.
            let outcome = result.unwrap_or(GuardOutcome::Panicked);
            let _ = tx.send(GuardDone { seq, key, served, warm, dir, outcome });
        });
    }

    /// Applies every finished check. Runs only on the serve loop.
    fn drain(&mut self, sessions: &mut HashMap<SessionKey, Entry>) {
        while let Ok(mut done) = self.rx.try_recv() {
            self.pending -= 1;
            if let Some(k) = self.running.iter().position(|g| g.seq == done.seq) {
                let g = self.running.swap_remove(k);
                if let (GuardOutcome::Cancelled(path), Some(why)) = (&mut done.outcome, g.why) {
                    *path = why;
                }
            }
            apply_guard(sessions, done);
        }
        self.start_next();
    }
}

/// First line of a response's stderr, for guard log lines.
fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(120).collect()
}

/// Applies one finished background check to the session map. On a real
/// mismatch the warm session is replaced by a new empty one and the next
/// answer for the key is marked recomputed; a result from before the last such replacement is
/// dropped (its bug is already reported, its session already replaced).
fn apply_guard(sessions: &mut HashMap<SessionKey, Entry>, done: GuardDone) {
    let file = done.key.krate.root.display().to_string();
    let seq = done.seq;
    match done.outcome {
        GuardOutcome::Stale(ref path) => {
            let _ = std::fs::remove_dir_all(&done.dir);
            eprintln!("guard-check: done {seq} stale for {file} ({} changed during the check)", path.display());
        }
        GuardOutcome::Cancelled(ref path) => {
            let _ = std::fs::remove_dir_all(&done.dir);
            eprintln!("guard-check: done {seq} cancelled for {file} ({} changed during the check)", path.display());
        }
        GuardOutcome::Panicked => {
            let _ = std::fs::remove_dir_all(&done.dir);
            if let Some(entry) = sessions.get_mut(&done.key)
                && done.served > entry.replaced_gen
            {
                eprintln!("guard: background fresh compile panicked for {file}; dropping the session, next answer recomputed");
                replace_session(entry, &done.key);
                entry.replaced_gen = done.served;
                entry.recompute_next = true;
            }
            eprintln!("guard-check: done {seq} panic for {file}");
        }
        GuardOutcome::Fresh(ref fresh) => {
            let same = fresh.code == done.warm.code && fresh.stdout == done.warm.stdout && fresh.stderr == done.warm.stderr;
            // Nothing links the fresh compile's base files: remove them.
            let _ = std::fs::remove_dir_all(&done.dir);
            if same {
                // The warm session was right; keep its caches.
                eprintln!("guard-check: done {seq} match for {file}");
                return;
            }
            match sessions.get_mut(&done.key) {
                Some(entry) if done.served > entry.replaced_gen => {
                    eprintln!(
                        "guard: background fresh session disagreed for {file} (warm {}, fresh {}); dropping the session, next answer recomputed; warm: {}; fresh: {}",
                        done.warm.code,
                        fresh.code,
                        first_line(&done.warm.stderr),
                        first_line(&fresh.stderr)
                    );
                    replace_session(entry, &done.key);
                    entry.replaced_gen = done.served;
                    entry.recompute_next = true;
                    eprintln!("guard-check: done {seq} mismatch for {file}");
                }
                _ => {
                    eprintln!("guard-check: done {seq} mismatch for {file} (already replaced by a newer check)");
                }
            }
        }
    }
}

/// The answer for a panic: an internal error (code 3) that names the
/// patch oracle failure, or None for any other panic.
fn oracle_answer(payload: &(dyn std::any::Any + Send), entry: &mut Entry, req: &Request) -> Option<Response> {
    let line = driver::oracle_failure(payload)?;
    eprintln!("lust daemon: patch oracle failure for {}; answered as an internal error, not retried", req.file.display());
    replace_session(entry, &req.session);
    Some(Response { stderr: format!("error: internal: {line}\n"), code: 3, ..Default::default() })
}

/// Compiles `req` in a brand-new session, which replaces the entry's. The
/// bool is false when even the fresh compile panicked (the entry then holds
/// another new empty session and the answer is the code 3 plain failure).
fn compile_fresh(entry: &mut Entry, req: &Request) -> (Response, bool) {
    let dir = entry.fresh_dir();
    let mut fresh = Session::new(dir, true, req.session.clone());
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut fresh))) {
        Ok(r) => {
            let old = std::mem::replace(&mut entry.session, fresh);
            let _ = std::fs::remove_dir_all(old.obj_dir());
            (r, true)
        }
        Err(payload) => {
            let _ = std::fs::remove_dir_all(fresh.obj_dir());
            if let Some(r) = oracle_answer(&*payload, entry, req) {
                return (r, false);
            }
            eprintln!("guard: compile panicked in a fresh session for {}", req.file.display());
            replace_session(entry, &req.session);
            (Response { stderr: "error: internal: compile failed in a fresh session\n".into(), code: 3, ..Default::default() }, false)
        }
    }
}

/// Compiles with the entry's warm session, with the panic net and the
/// fresh-session guard. An error answer goes to the client at once and is
/// rechecked in the background (`jobs`); a panic, or a request marked
/// recomputed by an earlier mismatch, is answered from a fresh session here.
fn compile_guarded(entry: &mut Entry, req: &Request, jobs: &mut GuardJobs) -> Response {
    entry.served += 1;
    let served = entry.served;
    if entry.recompute_next {
        entry.recompute_next = false;
        eprintln!("guard-check: recomputing {} in a fresh session (marked by a background mismatch)", req.file.display());
        // This answer already comes from a fresh session, so no background
        // check is spawned for it.
        return compile_fresh(entry, req).0;
    }
    let start = std::time::SystemTime::now();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut entry.session))) {
        Ok(r) if r.code == 0 || r.code == 2 => r,
        // A `lust test` harness build reads its overlay, which a guard thread
        // cannot see (`driver::read_source`): no background check for it.
        Ok(r) if !req.overlay.is_empty() => r,
        Ok(r) if r.code == 3 && r.stderr.contains("function count mismatch") => {
            // The warm session's scan and Ast disagree on the fn list
            // (unusual shapes: items moved into bodies). The session
            // state is not a sound basis for an answer, like after a
            // panic: redo in a fresh session at once and hand that out.
            eprintln!("lust daemon: session fn count mismatch for {}; recomputed in a fresh session", req.file.display());
            compile_fresh(entry, req).0
        }
        Ok(r) => {
            // An error answer: hand it out now, verify it in the background.
            let inputs = session_inputs(&entry.session, req);
            let texts = session_text_hashes(&entry.session);
            let dir = entry.fresh_dir();
            jobs.spawn(req.clone(), r.clone(), inputs, texts, start, dir, served);
            r
        }
        Err(payload) => {
            // An oracle failure is the answer: a retry would hide it.
            if let Some(r) = oracle_answer(&*payload, entry, req) {
                return r;
            }
            // A panic has no answer to hand out and the session may be
            // corrupt: redo in a fresh session at once, as before.
            let (r, fresh_ok) = compile_fresh(entry, req);
            if fresh_ok {
                eprintln!(
                    "guard: compile panicked in the warm session for {}; answered from a fresh session (fresh {}); fresh: {}",
                    req.file.display(),
                    r.code,
                    first_line(&r.stderr)
                );
            }
            r
        }
    }
}

/// How many warm sessions the daemon keeps (`LUST_DAEMON_SESSIONS`,
/// default 32, at least 1). Each distinct file or crate selection is one
/// session, so a long run over many small programs (a probe sweep) made
/// one per program and kept them all: RSS and temp space grew with every
/// new file. Past the cap the least recently used session is evicted.
fn max_sessions() -> usize {
    std::env::var("LUST_DAEMON_SESSIONS").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(32).max(1)
}

/// Evicts least recently used sessions until at most `cap` remain,
/// never `keep` (the key being served). An evicted session's object
/// dir is deleted, and so are its base files that no kept executable
/// names. A later request for that key starts a new session. A guard
/// check still running for it finds no entry and drops its result.
fn evict_lru(sessions: &mut HashMap<SessionKey, Entry>, keep: &SessionKey, cap: usize) {
    while sessions.len() > cap {
        let Some(old) = sessions.iter().filter(|(k, _)| *k != keep).min_by_key(|(_, e)| e.last_used).map(|(k, _)| k.clone()) else {
            return;
        };
        let entry = sessions.remove(&old).expect("the key was just found");
        driver::release_bases(&entry.session);
        let _ = std::fs::remove_dir_all(entry.session.obj_dir());
        eprintln!("lust daemon: evicted the least recently used session for crate {} (cap {cap})", old.describe());
    }
}

/// The session entry for `key`, made on first use and marked used now.
/// New keys get the next directory number from `made` (never reused,
/// also after evictions) and one log line naming the full key and its
/// directory; past the session cap the least recently used entry goes.
/// `env`: the client env of the request that asks (see `refresh_key`).
fn entry_for<'m>(
    sessions: &'m mut HashMap<SessionKey, Entry>,
    base: &Path,
    key: &SessionKey,
    env: Option<&[(String, String)]>,
    made: &mut usize,
) -> &'m mut Entry {
    if !sessions.contains_key(key) {
        let dir = base.join(made.to_string());
        *made += 1;
        eprintln!("lust daemon: new session for crate {} in {}", key.describe(), dir.display());
        sessions.insert(key.clone(), Entry::new(dir, key.clone(), env));
        evict_lru(sessions, key, max_sessions());
    }
    let entry = sessions.get_mut(key).expect("the entry was just made");
    entry.last_used = std::time::Instant::now();
    entry
}

/// One resource line every 100 requests, so a daemon.log shows growth
/// over a long session (scripts/daemon-soak.sh asserts the bounds).
fn log_stats(served: u64, sessions: usize) {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let field =
        |name: &str| status.lines().find(|l| l.starts_with(name)).and_then(|l| l.split_whitespace().nth(1)).unwrap_or("?").to_string();
    eprintln!(
        "lust daemon: stats: {served} requests, {sessions} sessions, rss {} kB, {} threads, {} expansions, {} cached expansions",
        field("VmRSS:"),
        field("Threads:"),
        crate::diag::expansion_count(),
        crate::expand::cache_len()
    );
}

/// Serves requests until idle. Each crate selection (`SessionKey`) has its own session.
pub fn serve(sock: &Path) -> ! {
    // Sessions load std once; a std or adapter source override must be
    // read fresh by every compile (see `protocol::source_override`).
    if let Some(var) = protocol::source_override() {
        eprintln!("error: lust daemon does not run with {var} set: compiles under a source override are always cold");
        std::process::exit(2);
    }
    // Clean up temp dirs of daemons and cold compiles that died without
    // a cleanup (SIGKILL, crash). Pid and owner checks protect anything
    // live, including a daemon already serving this socket.
    sweep_stale_temp_dirs();
    // Single instance, decided before anything touches the socket.
    let lock_path = protocol::daemon_lock_path(sock);
    // An autostarting client passes its already locked fd (see client.rs `claim_start`), so
    // the lock has no gap between that client and this daemon. The fcntl both checks the
    // fd is open and sets close-on-exec again, so no child of the daemon inherits it.
    let inherited = std::env::var("LUST_DAEMON_LOCK_FD")
        .ok()
        .and_then(|v| v.parse::<i32>().ok())
        // SAFETY: fcntl F_SETFD on an fd number; it fails harmlessly when the fd is not open.
        .filter(|&fd| unsafe { fcntl(fd, F_SETFD, FD_CLOEXEC) } == 0);
    let mut lock_file = match inherited {
        // SAFETY: the fd is open (checked above) and nothing else in this process owns it.
        Some(fd) => unsafe { std::fs::File::from_raw_fd(fd) },
        None => std::fs::OpenOptions::new().create(true).write(true).truncate(false).open(&lock_path).unwrap_or_else(|e| {
            eprintln!("error: cannot open {}: {e}", lock_path.display());
            std::process::exit(2);
        }),
    };
    // SAFETY: flock on a live fd. LOCK_EX | LOCK_NB: fail at once when another daemon holds it.
    // On an inherited fd this process already holds the lock, so the call succeeds.
    if unsafe { flock(lock_file.as_raw_fd(), LOCK_EX | LOCK_NB) } != 0 {
        eprintln!("lust daemon: another daemon already serves {}", sock.display());
        std::process::exit(0);
    }
    let _ = lock_file.set_len(0);
    let _ = lock_file.rewind();
    let _ = write!(lock_file, "{}", std::process::id());
    let _ = lock_file.flush();
    // `lock_file` stays open for the whole serve; process exit releases the flock.

    let _ = std::fs::remove_file(sock);
    let listener = UnixListener::bind(sock).unwrap_or_else(|e| {
        eprintln!("error: cannot bind {}: {e}", sock.display());
        std::process::exit(2);
    });
    if listener.set_nonblocking(true).is_err() {
        eprintln!("error: cannot set {} nonblocking", sock.display());
        std::process::exit(2);
    }
    // Shutdown signals take the controlled exit: the handler only sets
    // a flag and pokes this pipe (see `wait_readable` and `shutdown`).
    let mut wake_fds = [0i32; 2];
    // SAFETY: `wake_fds` has room for the two fds pipe(2) writes.
    if unsafe { pipe(wake_fds.as_mut_ptr()) } != 0 {
        eprintln!("error: cannot create the daemon wakeup pipe");
        std::process::exit(2);
    }
    let (wake_r, wake_w) = (wake_fds[0], wake_fds[1]);
    // SAFETY: fcntl F_SETFD on the fds just made; tcc children must not inherit them.
    unsafe {
        fcntl(wake_r, F_SETFD, FD_CLOEXEC);
        fcntl(wake_w, F_SETFD, FD_CLOEXEC);
        WAKE_W.store(wake_w, Ordering::SeqCst);
        signal(SIGINT, on_shutdown_signal as usize);
        signal(SIGTERM, on_shutdown_signal as usize);
    }
    // Removing the socket file is a stop request too. The watch wakes
    // the same poll as the listener and the signal pipe; the serve loop
    // checks it before each wait. A removal that lands before the watch
    // starts is caught by the existence check in `socket_removed`.
    let socket_watch = watch_socket_removal(sock);
    eprintln!("lust daemon: listening on {}", sock.display());
    let idle = protocol::daemon_idle();
    let mut last = std::time::Instant::now();
    let base = std::env::temp_dir().join(format!("lust-daemon-{}", std::process::id()));
    let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
    let mut made = 0usize;
    let mut served = 0u64;
    let mut jobs = GuardJobs::new();
    if let Some(limit) = hang_limit() {
        spawn_hang_watchdog(sock.to_path_buf(), base.clone(), limit);
    }
    // Autostart pre-warm: the client that started us names the file it is compiling
    // cold. Checking it here fills a session, so the next command is truly warm. It
    // waits for that cold process to exit first, so it never competes with it. A
    // request that arrives meanwhile waits in the listen backlog.
    if let Ok(pid) = std::env::var("LUST_DAEMON_PREWARM_AFTER")
        && let Ok(pid) = pid.parse::<i32>()
    {
        let start = std::time::Instant::now();
        // SAFETY: signal 0 only probes whether the pid exists.
        while unsafe { kill(pid, 0) } == 0 && start.elapsed() < std::time::Duration::from_secs(60) && !SHUTDOWN.load(Ordering::SeqCst) {
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
    }
    if !SHUTDOWN.load(Ordering::SeqCst)
        && let Ok(file) = std::env::var("LUST_DAEMON_PREWARM")
    {
        let file = PathBuf::from(file);
        let req = protocol::Request {
            cmd: protocol::Cmd::Check,
            session: SessionKey::synthetic(&file, false),
            out: file.with_extension(""),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false, cc: false, overlay: Default::default(),
            client: protocol::Client::default(),
            file: file.clone(),
        };
        let entry = entry_for(&mut sessions, &base, &req.session, req.client.env.as_deref(), &mut made);
        // No client reads this answer, and the file can change while it
        // compiles (the client may write the next version), so it runs as a
        // background check does: no oracle response compare, which would
        // read other bytes. A panic leaves no session to trust.
        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile_background(&req, &mut entry.session))).is_err() {
            sessions.remove(&req.session);
        }
        last = std::time::Instant::now();
    }
    loop {
        if socket_removed(socket_watch, sock) {
            shutdown(sock, &base, &sessions, "socket removed");
        }
        if SHUTDOWN.load(Ordering::SeqCst) {
            shutdown(sock, &base, &sessions, "shutdown signal");
        }
        // Apply any finished guard checks before waiting, so a mismatch
        // replaces its session before the next request for that key.
        jobs.drain(&mut sessions);
        // Block in poll() until a connection lands or the idle span runs out.
        // While guard checks run, wake often to drain them; the idle exit
        // also waits for them, so a mismatch is never lost at shutdown.
        let mut left = idle.map(|d| d.saturating_sub(last.elapsed()));
        if jobs.pending > 0 {
            let cap = std::time::Duration::from_millis(20);
            left = Some(left.map_or(cap, |d| d.min(cap)));
        }
        if !wait_readable(&listener, wake_r, socket_watch, left) {
            if jobs.pending == 0 && idle.is_some_and(|d| last.elapsed() >= d) {
                shutdown(sock, &base, &sessions, "idle timeout");
            }
            continue;
        }
        let mut conn = match listener.accept() {
            Ok((conn, _)) => conn,
            Err(_) => continue,
        };
        last = std::time::Instant::now();
        let _ = conn.set_nonblocking(false);
        let req = {
            let mut reader = BufReader::new(&conn);
            protocol::read_request(&mut reader)
        };
        // A client of another lust build (a rebuilt or replaced binary at
        // an explicit LUST_DAEMON_SOCKET) must never get this compiler's
        // answer: it gets a head it drops, compiles cold, and this daemon
        // exits so the next command starts one of the client's build.
        if req.as_ref().err() == Some(&protocol::ReadError::OtherBuild) {
            let _ = protocol::write_other_build(&mut conn);
            drop(conn);
            shutdown(sock, &base, &sessions, "a client of another lust build connected");
        }
        *BUSY.lock().unwrap_or_else(|e| e.into_inner()) = Some((conn.as_raw_fd(), std::time::Instant::now()));
        let resp = match req {
            Ok(req) => {
                // A daemon never runs user code in memory: that run forks,
                // and guard compiles run on other threads here (src/tcc.rs).
                assert!(req.run_args.is_none(), "the daemon wire carries no run arguments");
                // Finished guard checks for this key land before its next
                // compile, so a marked recompute takes effect here. Checks
                // whose inputs changed since stop: they could only be stale.
                jobs.drain(&mut sessions);
                jobs.cancel_stale();
                let entry = entry_for(&mut sessions, &base, &req.session, req.client.env.as_deref(), &mut made);
                // Graph and build-script routing (sections 1.1, 1.8): if
                // a covered file changed since this session was made,
                // replace it before serving, never after.
                let rk = refresh_key(&req.session, req.client.env.as_deref());
                if entry.refresh_key != rk {
                    eprintln!("lust daemon: graph or build script changed for crate {}; starting a fresh session", req.session.describe());
                    replace_session(entry, &req.session);
                    entry.refresh_key = rk;
                }
                compile_guarded(entry, &req, &mut jobs)
            }
            Err(_) => Response { stderr: "error: bad request\n".into(), code: 2, ..Default::default() },
        };
        let _ = protocol::write_response(&mut conn, &resp);
        *BUSY.lock().unwrap_or_else(|e| e.into_inner()) = None;
        served += 1;
        if served % 100 == 0 {
            log_stats(served, sessions.len());
        }
        last = std::time::Instant::now();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resp(code: i32, stderr: &str) -> Response {
        Response { stdout: String::new(), stderr: stderr.into(), code, ran: false }
    }

    fn done(key: &SessionKey, seq: u64, served: u64, warm: Response, fresh: Response, dir: PathBuf) -> GuardDone {
        GuardDone {
            seq,
            key: key.clone(),
            served,
            warm,
            dir,
            outcome: GuardOutcome::Fresh(fresh),
        }
    }

    /// The background mismatch path, which no live incremental bug reaches
    /// today: a differing fresh answer replaces the session and marks the
    /// next answer recomputed; an older result after that replacement is
    /// dropped; an equal answer keeps the warm session untouched.
    #[test]
    fn guard_apply_replaces_on_mismatch_and_drops_stale_results() {
        let base = std::env::temp_dir().join(format!("lust-guard-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let key = SessionKey::synthetic(Path::new("/tmp/g/main.rs"), false);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base, &key, None, &mut 0);
        entry.served = 5;
        let warm_dir = entry.session.obj_dir().to_path_buf();

        // Mismatch at served=3: a new session replaces the warm one, recompute marked.
        apply_guard(&mut sessions, done(&key, 1, 3, resp(1, "warm err\n"), resp(1, "fresh err\n"), base.join("f1")));
        let entry = sessions.get(&key).unwrap();
        let new_dir = entry.session.obj_dir().to_path_buf();
        assert_ne!(new_dir, warm_dir, "warm session replaced");
        assert!(entry.recompute_next, "next answer marked recomputed");
        assert_eq!(entry.replaced_gen, 3);

        // An older result (served=2) after the replacement changes nothing.
        apply_guard(&mut sessions, done(&key, 2, 2, resp(1, "warm err\n"), resp(0, ""), base.join("f2")));
        let entry = sessions.get(&key).unwrap();
        assert_eq!(entry.session.obj_dir(), new_dir.as_path(), "stale result dropped");
        assert_eq!(entry.replaced_gen, 3);

        // Equal answers keep the current session and clear nothing.
        let same = resp(1, "same err\n");
        apply_guard(&mut sessions, done(&key, 3, 5, same.clone(), same, base.join("f3")));
        let entry = sessions.get(&key).unwrap();
        assert_eq!(entry.session.obj_dir(), new_dir.as_path(), "match keeps the session");
        assert!(entry.recompute_next, "the earlier recompute mark stands");
        let _ = std::fs::remove_dir_all(&base);
    }

    /// A check request for `file` as the client sends it.
    fn check_req(file: &Path) -> Request {
        protocol::Request {
            cmd: protocol::Cmd::Check,
            session: SessionKey::synthetic(file, false),
            out: file.with_extension(""),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false, cc: false, overlay: Default::default(),
            client: protocol::Client::default(),
            file: file.to_path_buf(),
        }
    }

    /// Writes `text` to `path` after the clock has moved past every earlier
    /// timestamp (file times tick in a coarse clock).
    fn write_later(path: &Path, text: &str) {
        std::thread::sleep(std::time::Duration::from_millis(80));
        std::fs::write(path, text).unwrap();
    }

    /// Runs one guard check to its end on the test thread's own channel.
    fn guard_once(
        req: &Request,
        warm: Response,
        inputs: Vec<PathBuf>,
        texts: crate::intern::FxMap<PathBuf, u64>,
        start: std::time::SystemTime,
        dir: PathBuf,
    ) -> GuardDone {
        let mut jobs = GuardJobs::new();
        jobs.spawn(req.clone(), warm, inputs, texts, start, dir, 1);
        jobs.rx.recv_timeout(std::time::Duration::from_secs(120)).expect("the guard check ends")
    }

    /// The ctime proof: untouched files pass; a write, a revert to the same
    /// bytes (A -> B -> A), and a delete after `start` each count as changed.
    #[test]
    fn changed_input_sees_writes_reverts_and_deletes_after_start() {
        let dir = std::env::temp_dir().join(format!("lust-guard-ctime-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let (a, b, c) = (dir.join("a.rs"), dir.join("b.rs"), dir.join("c.rs"));
        for p in [&a, &b, &c] {
            std::fs::write(p, "fn f() {}\n").unwrap();
        }
        std::thread::sleep(std::time::Duration::from_millis(80));
        let start = std::time::SystemTime::now();
        let all = vec![a.clone(), b.clone(), c.clone()];
        assert_eq!(changed_input(&all, start), None, "nothing changed");
        write_later(&b, "fn g() {}\n");
        std::fs::write(&b, "fn f() {}\n").unwrap();
        assert_eq!(changed_input(&all, start), Some(b.clone()), "a revert to the same bytes still moved");
        assert_eq!(changed_input(&[a.clone()], start), None);
        std::fs::remove_file(&c).unwrap();
        assert_eq!(changed_input(&[a.clone(), c.clone()], start), Some(c.clone()), "a delete moves the dir");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The w-sig-small 09:45 false mismatch: a crate whose root is
    /// unchanged while a module file is edited during the guard check.
    /// The check is stale, never a mismatch. Without the edit, the same
    /// check matches the warm answer, and a warm answer that differs from
    /// the fresh one on the same inputs is still a mismatch.
    #[test]
    fn guard_ignores_module_edits_and_catches_real_mismatches() {
        let base = std::env::temp_dir().join(format!("lust-guard-mod-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join("main.rs");
        let store = base.join("store.rs");
        std::fs::write(&root, "mod store;\nfn main() {\n    store::put(1);\n}\n").unwrap();
        std::fs::write(&store, "pub fn put(x: u8) -> u8 {\n    x + true\n}\n").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(80));
        let req = check_req(&root);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base.join("s"), &req.session, None, &mut 0);
        let start = std::time::SystemTime::now();
        let warm = driver::compile(&req, &mut entry.session);
        assert_eq!(warm.code, 1, "store.rs has a type error: {}", warm.stderr);
        let inputs = session_inputs(&entry.session, &req);
        let texts = session_text_hashes(&entry.session);
        assert!(inputs.contains(&store), "the module file is a guard input: {inputs:?}");

        // Same inputs, same answer: a match keeps the warm session.
        let done = guard_once(&req, warm.clone(), inputs.clone(), texts.clone(), start, base.join("f1"));
        assert!(matches!(&done.outcome, GuardOutcome::Fresh(f) if f.stderr == warm.stderr && f.code == warm.code));

        // Same inputs, a warm answer that differs: a real mismatch.
        let wrong = Response { stderr: "error[L0001]: not what a fresh session says\n".into(), ..warm.clone() };
        let done = guard_once(&req, wrong, inputs.clone(), texts.clone(), start, base.join("f2"));
        assert!(matches!(done.outcome, GuardOutcome::Fresh(_)));
        sessions.get_mut(&req.session).unwrap().served = 1;
        apply_guard(&mut sessions, done);
        let entry = sessions.get(&req.session).unwrap();
        assert!(entry.recompute_next, "a mismatch on the same inputs replaces the session");
        assert!(!base.join("f2").exists(), "the fresh compile's dir is removed");

        // The module file is fixed after the warm answer (the root stays
        // byte for byte): the fresh answer differs, but the check is stale.
        write_later(&store, "pub fn put(x: u8) -> u8 {\n    x + 1\n}\n");
        let done = guard_once(&req, warm.clone(), inputs.clone(), texts.clone(), start, base.join("f3"));
        assert!(matches!(&done.outcome, GuardOutcome::Stale(p) if *p == store), "module edit reads as stale");

        // An edit and a revert of the root (A -> B -> A, fx-cgen-rec 11:16):
        // the bytes match again, the check is still stale.
        let text = std::fs::read_to_string(&root).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(80));
        let start = std::time::SystemTime::now();
        write_later(&root, "fn main() {}\n");
        std::fs::write(&root, &text).unwrap();
        let done = guard_once(&req, warm, vec![root.clone()], texts.clone(), start, base.join("f4"));
        assert!(matches!(&done.outcome, GuardOutcome::Stale(p) if *p == root), "a reverted root reads as stale");
        let _ = std::fs::remove_dir_all(&base);
    }

    /// The content proof: a fresh compile that read other bytes than
    /// the warm session's snapshot is stale even when no input's
    /// ctime moved (the rej02 gate flake: the fresh compile read the
    /// root mid-write and answered L0130 no `main`, and the coarse
    /// filesystem clock hid the edit from the ctime proof). The
    /// snapshot is doctored here, which stands in for the fresh
    /// compile having read the truncated file.
    #[test]
    fn guard_stale_when_fresh_read_other_bytes() {
        let base = std::env::temp_dir().join(format!("lust-guard-texts-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join("main.rs");
        std::fs::write(&root, "fn main() {\n    let x: u8 = true;\n}\n").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(80));
        let req = check_req(&root);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base.join("s"), &req.session, None, &mut 0);
        let start = std::time::SystemTime::now();
        let warm = driver::compile(&req, &mut entry.session);
        assert_eq!(warm.code, 1, "a type error: {}", warm.stderr);
        let inputs = session_inputs(&entry.session, &req);
        let mut texts = session_text_hashes(&entry.session);
        assert!(texts.contains_key(&root), "the root text is in the snapshot: {texts:?}");
        // The warm snapshot now claims other bytes for the root than
        // the fresh compile will read, and nothing on disk moves.
        texts.insert(root.clone(), 0);
        let done = guard_once(&req, warm, inputs, texts, start, base.join("f1"));
        assert!(matches!(&done.outcome, GuardOutcome::Stale(p) if *p == root), "other bytes read as stale");
        let _ = std::fs::remove_dir_all(&base);
    }

    /// The content proof on a one-file crate with no doctored snapshot
    /// (sd23_std_impl_hash, rel-cache's gate 15:2x: warm L0612, fresh
    /// L0130 no `main`). The map keeps no text there, so the snapshot
    /// must hash the bytes read. The root is emptied, as a copy caught
    /// between its truncate and its write leaves it, and `start` lies
    /// ahead of every ctime, as a lagging filesystem clock makes it.
    #[test]
    fn guard_stale_when_one_file_root_read_other_bytes() {
        let base = std::env::temp_dir().join(format!("lust-guard-onefile-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join("main.rs");
        std::fs::write(&root, "struct S;\nfn main() {\n    let x: u8 = S;\n}\n").unwrap();
        let req = check_req(&root);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base.join("s"), &req.session, None, &mut 0);
        let warm = driver::compile(&req, &mut entry.session);
        assert_eq!(warm.code, 1, "a type error: {}", warm.stderr);
        let inputs = session_inputs(&entry.session, &req);
        let texts = session_text_hashes(&entry.session);
        std::fs::write(&root, "").unwrap();
        let start = std::time::SystemTime::now() + std::time::Duration::from_secs(3600);
        let done = guard_once(&req, warm, inputs, texts, start, base.join("f1"));
        assert!(matches!(&done.outcome, GuardOutcome::Stale(p) if *p == root), "an emptied root reads as stale");
        let _ = std::fs::remove_dir_all(&base);
    }

    /// One check runs at a time: a second one waits until the first is
    /// applied, then runs; a queued check whose inputs change ends as
    /// `cancelled` without a compile.
    #[test]
    fn guard_runs_one_check_at_a_time() {
        let base = std::env::temp_dir().join(format!("lust-guard-queue-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join("main.rs");
        let store = base.join("store.rs");
        std::fs::write(&root, "mod store;\nfn main() {\n    store::put(1);\n}\n").unwrap();
        std::fs::write(&store, "pub fn put(x: u8) -> u8 {\n    x + true\n}\n").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(80));
        let req = check_req(&root);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base.join("s"), &req.session, None, &mut 0);
        let start = std::time::SystemTime::now();
        let warm = driver::compile(&req, &mut entry.session);
        let inputs = session_inputs(&entry.session, &req);
        let texts = session_text_hashes(&entry.session);
        let mut jobs = GuardJobs::new();
        let recv = |jobs: &GuardJobs| jobs.rx.recv_timeout(std::time::Duration::from_secs(120)).expect("the guard check ends");

        // The second check waits for the first, then runs and matches.
        jobs.spawn(req.clone(), warm.clone(), inputs.clone(), texts.clone(), start, base.join("f1"), 1);
        jobs.spawn(req.clone(), warm.clone(), inputs.clone(), texts.clone(), start, base.join("f2"), 2);
        assert_eq!((jobs.running.len(), jobs.queued.len(), jobs.pending), (1, 1, 2));
        let done = recv(&jobs);
        assert_eq!(done.seq, 1);
        jobs.tx.send(done).unwrap();
        jobs.drain(&mut sessions);
        assert_eq!((jobs.running.len(), jobs.queued.len()), (1, 0), "the queued check starts once the first is applied");
        let done = recv(&jobs);
        assert!(done.seq == 2 && matches!(&done.outcome, GuardOutcome::Fresh(f) if f.stderr == warm.stderr));
        jobs.tx.send(done).unwrap();
        jobs.drain(&mut sessions);
        assert_eq!(jobs.pending, 0);

        // A queued check whose module file changed never compiles.
        jobs.spawn(req.clone(), warm.clone(), inputs.clone(), texts.clone(), start, base.join("f3"), 3);
        jobs.spawn(req.clone(), warm.clone(), inputs, texts.clone(), start, base.join("f4"), 4);
        write_later(&store, "pub fn put(x: u8) -> u8 {\n    x + 1\n}\n");
        jobs.cancel_stale();
        assert!(jobs.queued.is_empty() && jobs.pending == 1, "the queued check ended as cancelled");
        let done = recv(&jobs);
        jobs.tx.send(done).unwrap();
        jobs.drain(&mut sessions);
        assert!(jobs.running.is_empty() && jobs.pending == 0);
        assert!(!sessions.get(&req.session).unwrap().recompute_next);
        let _ = std::fs::remove_dir_all(&base);
    }

    /// A check whose inputs changed since its warm compile started is
    /// cancelled when the serve loop next looks (`cancel_stale`): it ends as
    /// `cancelled`, names the changed file, never compares and never
    /// replaces the session. A check on unchanged inputs is not cancelled and matches.
    /// Guard phases never take the pool, and cancelled work unwinds at
    /// its next phase.
    #[test]
    fn guard_cancels_on_changed_inputs_only() {
        let base = std::env::temp_dir().join(format!("lust-guard-cancel-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join("main.rs");
        let store = base.join("store.rs");
        std::fs::write(&root, "mod store;\nfn main() {\n    store::put(1);\n}\n").unwrap();
        std::fs::write(&store, "pub fn put(x: u8) -> u8 {\n    x + true\n}\n").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(80));
        let req = check_req(&root);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base.join("s"), &req.session, None, &mut 0);
        let start = std::time::SystemTime::now();
        let warm = driver::compile(&req, &mut entry.session);
        assert_eq!(warm.code, 1, "store.rs has a type error: {}", warm.stderr);
        let inputs = session_inputs(&entry.session, &req);
        let texts = session_text_hashes(&entry.session);

        // Unchanged inputs: the check runs to its end and matches.
        let mut jobs = GuardJobs::new();
        jobs.spawn(req.clone(), warm.clone(), inputs.clone(), texts.clone(), start, base.join("f1"), 1);
        jobs.cancel_stale();
        assert!(jobs.running.iter().all(|g| g.why.is_none()), "no input changed");
        let done = jobs.rx.recv_timeout(std::time::Duration::from_secs(120)).expect("the guard check ends");
        assert!(matches!(&done.outcome, GuardOutcome::Fresh(f) if f.stderr == warm.stderr && f.code == warm.code));

        // A module file changed: cancelled, and the outcome names it.
        write_later(&store, "pub fn put(x: u8) -> u8 {\n    x + 1\n}\n");
        let mut jobs = GuardJobs::new();
        jobs.spawn(req.clone(), warm.clone(), inputs, texts.clone(), start, base.join("f2"), 1);
        jobs.cancel_stale();
        assert!(jobs.running.iter().all(|g| g.why.as_ref() == Some(&store)), "the module edit cancels");
        let done = jobs.rx.recv_timeout(std::time::Duration::from_secs(120)).expect("the guard check ends");
        assert!(matches!(done.outcome, GuardOutcome::Cancelled(_)), "a cancelled check never compares");
        jobs.tx.send(done).unwrap();
        jobs.drain(&mut sessions);
        assert!(jobs.running.is_empty() && jobs.pending == 0);
        let entry = sessions.get(&req.session).unwrap();
        assert!(!entry.recompute_next, "a cancelled check never replaces the session");

        // Background phases unwind once cancelled, and stay off the pool.
        let cancel = std::sync::Arc::new(AtomicBool::new(false));
        let out = std::thread::spawn({
            let cancel = cancel.clone();
            move || {
                crate::pool::set_background(Some(cancel.clone()));
                let first = crate::pool::par_map(&[1, 2, 3, 4], |x| x * 2);
                cancel.store(true, Ordering::Relaxed);
                let second = std::panic::catch_unwind(|| crate::pool::par_map(&[1, 2], |x| x + 1));
                (first, second.err().is_some_and(|p| p.downcast_ref::<crate::pool::Cancelled>().is_some()))
            }
        })
        .join()
        .unwrap();
        assert_eq!(out, (vec![2, 4, 6, 8], true));
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Inotify bytes count as socket removal only for a delete or
    /// move-away event that names the socket file itself.
    #[test]
    fn socket_removal_event_matches_delete_of_the_socket_name() {
        let event = |mask: u32, name: &[u8]| {
            let mut b = Vec::new();
            b.extend_from_slice(&1i32.to_ne_bytes());
            b.extend_from_slice(&mask.to_ne_bytes());
            b.extend_from_slice(&0u32.to_ne_bytes());
            b.extend_from_slice(&(name.len() as u32 + 1).to_ne_bytes());
            b.extend_from_slice(name);
            b.push(0);
            b
        };
        let sock: &[u8] = b".lust-daemon-x.sock";
        assert!(socket_removal_event(&event(IN_DELETE, sock), sock), "delete of the socket");
        assert!(socket_removal_event(&event(IN_MOVED_FROM, sock), sock), "move-away of the socket");
        assert!(!socket_removal_event(&event(IN_DELETE, b"other.sock"), sock), "another file");
        assert!(!socket_removal_event(&event(0x100, sock), sock), "a close event is not a removal");
        let mut two = event(IN_DELETE, b"other.sock");
        two.extend(event(IN_DELETE, sock));
        assert!(socket_removal_event(&two, sock), "the socket event may follow another");
        assert!(!socket_removal_event(&event(IN_DELETE, sock)[..8], sock), "truncated bytes never match");
    }

    /// Only exact pid-named lust temp entries are sweep candidates.
    #[test]
    fn stale_temp_pid_parses_only_pid_names() {
        assert_eq!(stale_temp_pid("lust-daemon-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-test-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-rustc-check-123.rmeta"), Some(123));
        assert_eq!(stale_temp_pid("lust-daemon-glue-abc"), None);
        assert_eq!(stale_temp_pid("lust-daemon-"), None);
        assert_eq!(stale_temp_pid("lust-daemon-12a"), None);
        assert_eq!(stale_temp_pid("lust-runtime-0123456789abcdef.o"), None);
        assert_eq!(stale_temp_pid("other-123"), None);
    }

    /// The startup sweep deletes dead-pid lust dirs and files, and keeps
    /// live-pid dirs and non-pid names.
    #[test]
    fn sweep_removes_dead_pid_dirs_and_keeps_live_ones() {
        let tmp = std::env::temp_dir();
        // A pid far above pid_max is never alive on Linux.
        let dead = 4_000_000_001u32;
        let dead_dir = tmp.join(format!("lust-daemon-{dead}"));
        let dead_cold = tmp.join(format!("lust-{dead}"));
        let dead_file = tmp.join(format!("lust-rustc-check-{dead}.rmeta"));
        let live_dir = tmp.join(format!("lust-daemon-{}", std::process::id()));
        let other_dir = tmp.join(format!("lust-daemon-glue-sweeptest{}", std::process::id()));
        for d in [&dead_dir, &dead_cold, &live_dir, &other_dir] {
            let _ = std::fs::remove_dir_all(d);
            std::fs::create_dir_all(d).unwrap();
            std::fs::write(d.join("x.o"), b"x").unwrap();
        }
        std::fs::write(&dead_file, b"x").unwrap();
        sweep_stale_temp_dirs();
        assert!(!dead_dir.exists(), "dead daemon dir swept");
        assert!(!dead_cold.exists(), "dead cold dir swept");
        assert!(!dead_file.exists(), "dead rmeta file swept");
        assert!(live_dir.exists(), "own pid dir kept");
        assert!(other_dir.exists(), "non-pid name kept");
        let _ = std::fs::remove_dir_all(&live_dir);
        let _ = std::fs::remove_dir_all(&other_dir);
    }

    /// The watchdog's peer check: an open client is not gone, a closed one is.
    #[test]
    fn client_gone_sees_a_closed_peer_only() {
        let (ours, theirs) = std::os::unix::net::UnixStream::pair().unwrap();
        assert!(!client_gone(ours.as_raw_fd()));
        drop(theirs);
        assert!(client_gone(ours.as_raw_fd()));
    }

    /// LRU order, the served key's protection, and dir numbers that are never reused.
    #[test]
    fn evict_lru_drops_the_least_recent_entry_and_its_dir() {
        let tmp = std::env::temp_dir().join(format!("lust-daemon-evict-{}", std::process::id()));
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let mut made = 0;
        let keys: Vec<SessionKey> = (0..3).map(|i| SessionKey::synthetic(&tmp.join(format!("f{i}.rs")), false)).collect();
        for k in &keys {
            let e = entry_for(&mut sessions, &tmp, k, None, &mut made);
            std::fs::create_dir_all(e.session.obj_dir()).unwrap();
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        // Touch key 0: key 1 is now the least recently used.
        entry_for(&mut sessions, &tmp, &keys[0], None, &mut made);
        let dir1 = sessions[&keys[1]].session.obj_dir().to_path_buf();
        evict_lru(&mut sessions, &keys[2], 2);
        assert!(sessions.contains_key(&keys[0]) && sessions.contains_key(&keys[2]) && !sessions.contains_key(&keys[1]));
        assert!(!dir1.exists());
        // The served key is never evicted, and dir numbers are not reused.
        evict_lru(&mut sessions, &keys[2], 0);
        assert_eq!(sessions.len(), 1);
        assert_eq!(made, 3);
        let _ = std::fs::remove_dir_all(&tmp);
    }

    /// A replaced session's object dir is deleted at replacement time,
    /// not left until daemon exit.
    #[test]
    fn replace_session_deletes_the_old_obj_dir() {
        let base = std::env::temp_dir().join(format!("lust-replace-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let key = SessionKey::synthetic(Path::new("/tmp/g/main.rs"), false);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base, &key, None, &mut 0);
        let old_dir = entry.session.obj_dir().to_path_buf();
        std::fs::create_dir_all(&old_dir).unwrap();
        std::fs::write(old_dir.join("u1.o"), b"x").unwrap();
        replace_session(entry, &key);
        assert_ne!(entry.session.obj_dir(), old_dir.as_path(), "session moved to a fresh dir");
        assert!(!old_dir.exists(), "old obj dir deleted");
        let _ = std::fs::remove_dir_all(&base);
    }
}
