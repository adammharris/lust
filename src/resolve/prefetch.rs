// Source prefetch (rel-front): a front image build reads its crate's source files on other
// threads while `image::load` puts the image back, from the list the last build wrote
// (`write_list`, `<state>/sources`): reading the files needs nothing of the image. The
// resolve takes a listed file's text from here (`take`) and reads any other file as before;
// a file's text is the one read at the build's start either way. With
// `LUST_SOURCES_READY=<file>` no source file is read before <file> exists: a CI job checks
// its sources out while lust restores the image, then creates the file.
use crate::intern::FxMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::thread::JoinHandle;

/// Names a file that exists once the sources are checked out (`wait_ready`).
pub use crate::protocol::SOURCES_READY_ENV as READY_ENV;
/// The list file in the state directory: one path per line.
const LIST: &str = "sources";

static RUN: Mutex<Option<JoinHandle<FxMap<PathBuf, String>>>> = Mutex::new(None);
static STARTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Waits until the file `LUST_SOURCES_READY` names exists, when one is named. After two
/// minutes the build stops with an error: the job never created it.
pub fn wait_ready() {
    let Some(ready) = std::env::var_os(READY_ENV).filter(|v| !v.is_empty()) else { return };
    let start = std::time::Instant::now();
    while !Path::new(&ready).exists() {
        if start.elapsed() > std::time::Duration::from_secs(120) {
            eprintln!("error: {READY_ENV}: {} did not appear in 120 s", Path::new(&ready).display());
            std::process::exit(2);
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

/// Starts reading the files the last build listed in `dir` (`write_list`), on four threads
/// of their own (the image's readers run beside them); once per process.
pub fn start(dir: &Path) {
    use std::os::unix::ffi::OsStrExt;
    if STARTED.swap(true, std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let list = dir.join(LIST);
    let run = std::thread::Builder::new().name("lust-prefetch".into()).spawn(move || {
        let Ok(bytes) = std::fs::read(&list) else { return FxMap::default() };
        let paths: Vec<PathBuf> = bytes.split(|&b| b == b'\n').filter(|l| !l.is_empty()).map(|l| PathBuf::from(std::ffi::OsStr::from_bytes(l))).collect();
        // While the checkout may still write them, only ask the kernel to read the files
        // ahead (their bytes are not used), so the reads after it hit the page cache.
        if std::env::var_os(READY_ENV).is_some_and(|v| !v.is_empty()) {
            paths.iter().for_each(|p| read_ahead(p));
            wait_ready();
        }
        let part = paths.len().div_ceil(4).max(1);
        std::thread::scope(|s| {
            let readers: Vec<_> = paths
                .chunks(part)
                .map(|ps| s.spawn(move || ps.iter().filter_map(|p| Some((p.clone(), std::fs::read_to_string(p).ok()?))).collect::<Vec<_>>()))
                .collect();
            readers.into_iter().flat_map(|r| r.join().unwrap_or_default()).collect()
        })
    });
    if let Ok(run) = run {
        *RUN.lock().unwrap() = Some(run);
    }
}

/// Asks the kernel to read `path` ahead into the page cache (`posix_fadvise` WILLNEED).
/// Linux only; elsewhere the read itself warms the cache.
#[cfg(not(target_os = "linux"))]
fn read_ahead(_path: &Path) {}

/// Asks the kernel to read `path` ahead into the page cache (`posix_fadvise` WILLNEED).
#[cfg(target_os = "linux")]
fn read_ahead(path: &Path) {
    use std::os::fd::AsRawFd;
    unsafe extern "C" {
        fn posix_fadvise(fd: i32, offset: i64, len: i64, advice: i32) -> i32;
    }
    const WILLNEED: i32 = 3;
    if let Ok(f) = std::fs::File::open(path) {
        // SAFETY: a libc call on a descriptor this function owns; it reads nothing back.
        unsafe { posix_fadvise(f.as_raw_fd(), 0, 0, WILLNEED) };
    }
}

/// The texts `start` read, by path, once it is done; None when no prefetch ran (or a
/// resolve took them already).
pub fn take() -> Option<FxMap<PathBuf, String>> {
    let run = RUN.lock().unwrap().take()?;
    run.join().ok()
}

/// Writes the files `paths` as `dir`'s list for the next build's `start`.
pub fn write_list<'p>(dir: &Path, paths: impl Iterator<Item = &'p Path>) {
    use std::os::unix::ffi::OsStrExt;
    let mut out = Vec::new();
    for p in paths {
        out.extend_from_slice(p.as_os_str().as_bytes());
        out.push(b'\n');
    }
    let tmp = dir.join(format!("{LIST}.tmp"));
    if std::fs::write(&tmp, &out).is_ok() {
        let _ = std::fs::rename(&tmp, dir.join(LIST));
    }
}
