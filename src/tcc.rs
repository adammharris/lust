// C compilation with tcc. Units compile to object files: a few in process with libtcc, many in
// parallel `tcc -c` processes (libtcc serializes compiles behind a global lock). libtcc then links
// in process: a standalone executable, or (for the daemon) a base shared library plus a small
// executable with the changed code.
use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::path::{Path, PathBuf};
use std::process::Command;

/// The release package's support dir, `<prefix>/lib/lust` next to `<prefix>/bin/lust-core`
/// (scripts/release.sh lays it out). `None` for a dev build in `target/`: then tcc and
/// `library/` are the build-time trees.
pub fn install_dir() -> Option<&'static Path> {
    static DIR: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();
    DIR.get_or_init(|| {
        let exe = std::env::current_exe().ok()?;
        let dir = exe.parent()?.parent()?.join("lib/lust");
        dir.is_dir().then_some(dir)
    })
    .as_deref()
}

/// The tcc runtime dir (libtcc1.a and tcc's headers) and the `tcc` binary: the release
/// package's copies, else the tree build.rs linked against (`LUST_TCC_HOME` at build time).
pub fn tcc_paths() -> (PathBuf, PathBuf) {
    match install_dir() {
        Some(d) => (d.join("tcc/lib/tcc"), d.join("tcc/bin/tcc")),
        None => (PathBuf::from(env!("LUST_TCC_LIB_PATH")), PathBuf::from(env!("LUST_TCC_BIN"))),
    }
}

#[repr(C)]
struct TccState {
    _private: [u8; 0],
}

type ErrorFn = extern "C" fn(opaque: *mut c_void, msg: *const c_char);

type ReallocFn = extern "C" fn(ptr: *mut c_void, size: std::ffi::c_ulong) -> *mut c_void;

unsafe extern "C" {
    fn tcc_set_realloc(f: ReallocFn);
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn tcc_new() -> *mut TccState;
    fn tcc_delete(s: *mut TccState);
    fn tcc_set_lib_path(s: *mut TccState, path: *const c_char);
    fn tcc_set_error_func(s: *mut TccState, opaque: *mut c_void, f: ErrorFn);
    fn tcc_set_options(s: *mut TccState, opts: *const c_char) -> c_int;
    fn tcc_set_output_type(s: *mut TccState, ty: c_int) -> c_int;
    fn tcc_compile_string(s: *mut TccState, src: *const c_char) -> c_int;
    fn tcc_add_file(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_add_library_path(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_add_library(s: *mut TccState, name: *const c_char) -> c_int;
    fn tcc_output_file(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_relocate(s: *mut TccState) -> c_int;
    fn tcc_get_symbol(s: *mut TccState, name: *const c_char) -> *mut c_void;
}

// POSIX calls used by `run_in_memory` (linked from libc, always present).
unsafe extern "C" {
    fn prctl(option: c_int, arg2: std::ffi::c_ulong, arg3: std::ffi::c_ulong, arg4: std::ffi::c_ulong, arg5: std::ffi::c_ulong) -> c_int;
    fn fork() -> c_int;
    fn waitpid(pid: c_int, status: *mut c_int, options: c_int) -> c_int;
    fn _exit(code: c_int) -> !;
    fn fflush(stream: *mut c_void) -> c_int;
}

/// libtcc's allocator hook. Size 0 means free.
extern "C" fn tcc_realloc(p: *mut c_void, size: std::ffi::c_ulong) -> *mut c_void {
    // SAFETY: libtcc only passes pointers it got from this same function.
    unsafe {
        if size == 0 {
            mi_free(p);
            std::ptr::null_mut()
        } else {
            mi_realloc(p, size as usize)
        }
    }
}

/// Makes libtcc allocate with mimalloc. A warm daemon then reuses memory between builds instead
/// of faulting in fresh pages from the kernel each time. Call once, before any other tcc call.
pub fn use_mimalloc() {
    // SAFETY: sets a global function pointer before any libtcc state exists.
    unsafe { tcc_set_realloc(tcc_realloc) }
}

/// Linux `PR_SET_THP_DISABLE`.
#[cfg(target_os = "linux")]
const PR_SET_THP_DISABLE: c_int = 41;

/// Turns transparent huge pages on or off for this process (Linux; a
/// no-op elsewhere). A cold one-shot compile turns them off where they
/// cost (`main`, `pool::small_pages_in_parallel`): its threads touch
/// fresh memory sparsely, and the kernel then zeroes a whole 2 MB page
/// for each first touch, under contention in the parallel phases
/// (realish40 touched 320 MB instead of 90 MB). The flag is inherited
/// across fork and exec, so it is on again before user code runs
/// (`protocol::finish`, `run_in_memory`'s child).
pub fn set_huge_pages(on: bool) {
    #[cfg(target_os = "linux")]
    // SAFETY: prctl with PR_SET_THP_DISABLE only sets a flag on this process; it reads no memory.
    unsafe {
        prctl(PR_SET_THP_DISABLE, if on { 0 } else { 1 }, 0, 0, 0);
    }
    #[cfg(not(target_os = "linux"))]
    let _ = on;
}

const TCC_OUTPUT_MEMORY: c_int = 1;
const TCC_OUTPUT_EXE: c_int = 2;
const TCC_OUTPUT_OBJ: c_int = 3;
const TCC_OUTPUT_DLL: c_int = 4;

extern "C" fn on_error(opaque: *mut c_void, msg: *const c_char) {
    // SAFETY: `opaque` is the `Vec<String>` owned by `Tcc`, alive for the state's lifetime.
    let errs = unsafe { &mut *(opaque as *mut Vec<String>) };
    // SAFETY: tcc passes a valid NUL-terminated message.
    errs.push(unsafe { CStr::from_ptr(msg) }.to_string_lossy().into_owned());
}

/// A libtcc state. Errors collect into `errs`.
struct Tcc {
    s: *mut TccState,
    /// Boxed so its address stays fixed: libtcc keeps a pointer to it for the error callback.
    #[allow(clippy::box_collection)]
    errs: Box<Vec<String>>,
}

impl Tcc {
    fn new(output: c_int, debug: bool) -> Result<Tcc, String> {
        let lib = cstr(&tcc_paths().0);
        // No asynchronous unwind tables: tcc writes overlapping .eh_frame
        // FDEs (spike K6), which makes the system linker reject its
        // objects. Lust frames never unwind, so the tables are pure cost.
        let opts =
            CString::new(if debug { "-g -w -fno-asynchronous-unwind-tables" } else { "-w -fno-asynchronous-unwind-tables" }).unwrap();
        // SAFETY: a fresh libtcc state; the error vector is boxed so its address is stable.
        unsafe {
            let s = tcc_new();
            if s.is_null() {
                return Err("tcc_new failed".into());
            }
            let mut t = Tcc { s, errs: Box::default() };
            tcc_set_error_func(s, &mut *t.errs as *mut Vec<String> as *mut c_void, on_error);
            tcc_set_lib_path(s, lib.as_ptr());
            tcc_set_options(s, opts.as_ptr());
            tcc_set_output_type(s, output);
            Ok(t)
        }
    }
    fn fail(&self, what: &str) -> String {
        format!("tcc failed to {what} (this is a lust bug):\n{}", self.errs.join("\n"))
    }
}

impl Drop for Tcc {
    fn drop(&mut self) {
        // SAFETY: `s` came from tcc_new and is deleted once.
        unsafe { tcc_delete(self.s) }
    }
}

fn cstr(p: &Path) -> CString {
    CString::new(p.to_string_lossy().as_bytes()).expect("path contains NUL")
}

/// Compiles `(object path, C source)` pairs.
pub fn compile_units(units: &[(PathBuf, String)], debug: bool) -> Result<(), String> {
    // An object may be a hard link to a disk cache entry (`Cache::unit_object`). tcc
    // replaces its output file, but the cache must not depend on that.
    for (obj, _) in units {
        let _ = std::fs::remove_file(obj);
    }
    if units.len() <= 2 {
        for (obj, src) in units {
            let tcc = Tcc::new(TCC_OUTPUT_OBJ, debug)?;
            let c = CString::new(src.as_str()).map_err(|_| "generated C contains a NUL byte".to_string())?;
            // SAFETY: valid state and NUL-terminated strings that outlive the calls.
            unsafe {
                if tcc_compile_string(tcc.s, c.as_ptr()) != 0 {
                    return Err(tcc.fail("compile the generated C"));
                }
                if tcc_output_file(tcc.s, cstr(obj).as_ptr()) != 0 {
                    return Err(tcc.fail("write an object file"));
                }
            }
        }
        return Ok(());
    }
    // At most one tcc child per core (the pool size): starting every unit's
    // child at once oversubscribes the machine and multiplies peak memory
    // on a large program (one child per unit, hundreds of units). Workers
    // pull units largest first, so the long units start early and the tail
    // is short units filling gaps, instead of one big unit starting last.
    let limit = crate::pool::threads().max(1).min(units.len());
    let mut order: Vec<usize> = (0..units.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(units[i].1.len()));
    let next = std::sync::atomic::AtomicUsize::new(0);
    let errors = std::sync::Mutex::new(String::new());
    std::thread::scope(|scope| {
        for _ in 0..limit {
            scope.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(&i) = order.get(k) else { return };
                let (obj, src) = &units[i];
                let c = obj.with_extension("c");
                let fail = |errors: &std::sync::Mutex<String>, msg: String| {
                    errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&msg);
                };
                if let Err(e) = std::fs::write(&c, src) {
                    fail(&errors, format!("cannot write {}: {e}\n", c.display()));
                    continue;
                }
                let (lib, bin) = tcc_paths();
                let mut cmd = Command::new(bin);
                // -B: the runtime dir, so tcc finds its headers wherever the package lives.
                let mut b = std::ffi::OsString::from("-B");
                b.push(lib);
                cmd.arg(b).arg("-c").arg("-w").arg("-fno-asynchronous-unwind-tables");
                if debug {
                    cmd.arg("-g");
                }
                cmd.arg("-o").arg(obj).arg(&c);
                let child = match cmd.stderr(std::process::Stdio::piped()).spawn() {
                    Ok(child) => child,
                    Err(e) => {
                        fail(&errors, format!("cannot run tcc: {e}\n"));
                        continue;
                    }
                };
                match child.wait_with_output() {
                    Ok(out) if out.status.success() => {}
                    Ok(out) => {
                        let mut msg = String::from_utf8_lossy(&out.stderr).into_owned();
                        // A child killed by a signal (for example the out-of-memory killer)
                        // prints nothing; it still failed, and its object is missing or stale.
                        if out.stderr.is_empty() {
                            msg.push_str(&format!("tcc exited with {}\n", out.status));
                        }
                        fail(&errors, msg);
                    }
                    Err(e) => fail(&errors, format!("tcc failed: {e}\n")),
                }
            });
        }
    });
    let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
    if errors.is_empty() { Ok(()) } else { Err(format!("tcc failed to compile the generated C (this is a lust bug):\n{errors}")) }
}

fn link_objects(tcc: &Tcc, objs: &[PathBuf], out: &Path) -> Result<(), String> {
    // The float methods call libm (sqrt, pow, exp, log, floor, ...),
    // the same entry points rustc lowers them to on this platform.
    let libm = CString::new("m").unwrap();
    // SAFETY: valid state and NUL-terminated strings that outlive the calls.
    unsafe {
        if tcc_add_library(tcc.s, libm.as_ptr()) != 0 {
            return Err(tcc.fail("load libm"));
        }
        for o in objs {
            if tcc_add_file(tcc.s, cstr(o).as_ptr()) != 0 {
                return Err(tcc.fail("load an object file"));
            }
        }
        if tcc_output_file(tcc.s, cstr(out).as_ptr()) != 0 {
            return Err(tcc.fail("link"));
        }
    }
    Ok(())
}

/// Links an executable at `out`. libtcc opens its output without O_CLOEXEC, so a child
/// that another thread spawns while it writes (a tcc or cc compile of a daemon's other
/// session, a guard) keeps the file open for writing for the child's whole life, and an
/// exec of it fails with ETXTBSY until then: a client that runs the binary the daemon just
/// built. tcc writes a private temp file, and a copy of it (a fresh inode, written through
/// a close-on-exec descriptor) is renamed over `out`; a rename alone would keep the inode
/// the child holds. A child cloned during the copy still holds it until its own exec, so a
/// thread that execs `out` at once while others spawn retries on ETXTBSY (tests do). A
/// running old `out` keeps its own inode.
fn link_executable(tcc: &Tcc, objs: &[PathBuf], out: &Path) -> Result<(), String> {
    static SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp = |tag: &str| {
        let mut p = out.as_os_str().to_owned();
        p.push(format!(".{tag}-{}-{n}", std::process::id()));
        PathBuf::from(p)
    };
    let (written, fresh) = (tmp("tcc"), tmp("new"));
    let linked = link_objects(tcc, objs, &written).and_then(|()| {
        std::fs::copy(&written, &fresh).and_then(|_| std::fs::rename(&fresh, out)).map_err(|e| format!("cannot write {}: {e}", out.display()))
    });
    let _ = std::fs::remove_file(&written);
    if linked.is_err() {
        let _ = std::fs::remove_file(&fresh);
    }
    linked
}

/// Links object files into a shared library at `out`. `soname` is the file name the library
/// is installed under. On macOS it becomes the install name (`@rpath/<soname>`), which an
/// executable linked against the library records as the library to load; an ELF executable
/// records the file name it found instead.
pub fn link_shared(objs: &[PathBuf], out: &Path, soname: &str, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_DLL, debug)?;
    if cfg!(target_os = "macos") {
        let opt = CString::new(format!("-install_name @rpath/{soname}")).unwrap();
        // SAFETY: valid state and a NUL-terminated string that outlives the call.
        unsafe { tcc_set_options(tcc.s, opt.as_ptr()) };
    }
    link_objects(&tcc, objs, out)
}

/// Links an executable from `objs` plus `<dir>/lib<base>.so` (`.dylib` on macOS), which it
/// loads at run time.
/// The base name is versioned (for example `base-3`), so a rebuilt base never changes what an
/// executable built earlier loads.
pub fn link_with_base(objs: &[PathBuf], dir: &Path, base: &str, out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_EXE, debug)?;
    // tcc splits an options string on spaces: the dir goes in double
    // quotes (its `"` and `\` escaped), so a path with a space keeps
    // its whole rpath.
    let quoted = dir.to_string_lossy().replace('\\', "\\\\").replace('"', "\\\"");
    let rpath = CString::new(format!("-Wl,-rpath=\"{quoted}\"")).unwrap();
    let base = CString::new(base).unwrap();
    // SAFETY: valid state and NUL-terminated strings that outlive the calls.
    unsafe {
        tcc_set_options(tcc.s, rpath.as_ptr());
        tcc_add_library_path(tcc.s, cstr(dir).as_ptr());
        if tcc_add_library(tcc.s, base.as_ptr()) != 0 {
            return Err(tcc.fail("load libbase.so"));
        }
    }
    link_executable(&tcc, objs, out)
}

/// Links object files into a standalone executable at `out`.
pub fn link(objs: &[PathBuf], out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_EXE, debug)?;
    link_executable(&tcc, objs, out)
}

/// The runtime unit compiled to an object once per lust build, cached in the temp directory.
/// The key is a hash of the runtime source, the debug flag, and the tcc library path: anything
/// that changes the object's bytes changes the key. Stale entries are left for the OS to clean.
pub fn cached_runtime_object(runtime_src: &str, debug: bool) -> Result<PathBuf, String> {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    runtime_src.hash(&mut h);
    debug.hash(&mut h);
    tcc_paths().0.hash(&mut h);
    // The compile options change the object's bytes too; name the set so
    // a flag change does not reuse an object built without it.
    "opts:no-asynchronous-unwind-tables".hash(&mut h);
    let obj = std::env::temp_dir().join(format!("lust-runtime-{:016x}.o", h.finish()));
    if obj.exists() {
        return Ok(obj);
    }
    // Build under a private name, then rename, so two lust processes never see a half object.
    let tmp = std::env::temp_dir().join(format!("lust-runtime-{}-{}.o", std::process::id(), if debug { "g" } else { "o" }));
    compile_units(&[(tmp.clone(), runtime_src.to_string())], debug)?;
    match std::fs::rename(&tmp, &obj) {
        Ok(()) => {}
        // Another process won the race (or the rename failed): use the file that is there,
        // else keep our own copy.
        Err(_) if obj.exists() => {
            let _ = std::fs::remove_file(&tmp);
        }
        Err(_) => return Ok(tmp),
    }
    Ok(obj)
}

/// Compiles `units` (C sources; object paths are ignored) plus the cached runtime object into
/// memory and runs the program's `main` with `argv` (argv[0] included). Returns the exit code
/// exactly as the file-based `lust run` reports it: the program's own code, or 134 when it died
/// by a signal (a panic aborts). No object files, no link, no exec of a built binary. Use only
/// for small programs in a one-shot process: libtcc compiles serially here.
///
/// Compilation, relocation, and the symbol lookup happen in this process and can fail with
/// Err (the caller then falls back to the file-based path; user code has not run). The call
/// into user code happens in a forked child, so a panic or crash in the program cannot kill
/// this process, exit codes match the file-based path, and the child's C stdio buffering sees
/// the same fds a real executable would. The child inherits our stdout and stderr.
///
/// The fork contract: a fork copies only the calling thread, and a thread that holds a lock at
/// the fork (the allocator's, stdio's) leaves it held in the child for good. So no other thread
/// may live at the fork. This call stops the compiler's pool (`pool::stop` joins every pool
/// thread), then `lone_thread` checks the OS thread list and any other live thread gives Err
/// before the fork. The pool stays stopped only until the fork returns. The caller runs this
/// only in one-shot sessions (a daemon runs guard compiles on other threads), and never from
/// inside a `par_map` task. On non-Unix targets this always returns Err.
pub fn run_in_memory(units: &[(PathBuf, String)], runtime_obj: &Path, argv: &[String], debug: bool) -> Result<i32, String> {
    #[cfg(not(unix))]
    {
        let _ = (units, runtime_obj, argv, debug);
        return Err("in-memory run is Unix-only".into());
    }
    #[cfg(unix)]
    {
        let tcc = Tcc::new(TCC_OUTPUT_MEMORY, debug)?;
        // Build argv before the fork, so the child allocates nothing before calling main.
        let cargs: Vec<CString> = argv
            .iter()
            .map(|a| CString::new(a.as_str()).map_err(|_| "program argument contains a NUL byte".to_string()))
            .collect::<Result<_, _>>()?;
        let mut cargv: Vec<*mut c_char> = cargs.iter().map(|a| a.as_ptr() as *mut c_char).collect();
        cargv.push(std::ptr::null_mut());
        // SAFETY: valid state and NUL-terminated strings that outlive the calls.
        let main_sym = unsafe {
            for (_, src) in units {
                let c = CString::new(src.as_str()).map_err(|_| "generated C contains a NUL byte".to_string())?;
                if tcc_compile_string(tcc.s, c.as_ptr()) != 0 {
                    return Err(tcc.fail("compile the generated C"));
                }
            }
            if tcc_add_file(tcc.s, cstr(runtime_obj).as_ptr()) != 0 {
                return Err(tcc.fail("load the runtime object"));
            }
            if tcc_relocate(tcc.s) != 0 {
                return Err(tcc.fail("relocate the program"));
            }
            let name = CString::new("main").unwrap();
            let sym = tcc_get_symbol(tcc.s, name.as_ptr());
            if sym.is_null() {
                return Err(tcc.fail("find main"));
            }
            // The generated main has C's standard signature: int main(int argc, char **argv).
            std::mem::transmute::<*mut c_void, extern "C" fn(c_int, *mut *mut c_char) -> c_int>(sym)
        };
        // No other thread may live at the fork (see above).
        #[cfg(test)]
        let _serial = crate::pool::stop_tests();
        let pool_stopped = crate::pool::stop();
        if !lone_thread() {
            return Err("another thread is alive, and an in-memory run forks".into());
        }
        // Flush Rust and C buffers before the fork, so the child does not write them twice.
        {
            use std::io::Write as _;
            let _ = std::io::stdout().flush();
            let _ = std::io::stderr().flush();
            // SAFETY: fflush(NULL) flushes all C streams.
            unsafe { fflush(std::ptr::null_mut()) };
        }
        // SAFETY: this is the process's only thread (checked above); the child only calls main
        // and _exit.
        let pid = unsafe { fork() };
        if pid == 0 {
            // Child. Do not return, drop, or panic: call user code, flush, _exit.
            // User code gets the system's huge page default back.
            set_huge_pages(true);
            // SAFETY: main_sym was relocated before the fork; cargv outlives the call.
            unsafe {
                let code = main_sym(cargs.len() as c_int, cargv.as_mut_ptr());
                fflush(std::ptr::null_mut());
                _exit(code);
            }
        }
        // Parent. The child is its own process now, so the pool may start again while the
        // program runs.
        drop(pool_stopped);
        if pid < 0 {
            return Err("fork failed for an in-memory run".into());
        }
        let mut status: c_int = 0;
        // SAFETY: pid is our child; status is a valid out-pointer.
        if unsafe { waitpid(pid, &mut status, 0) } < 0 {
            return Err("waitpid failed for an in-memory run".into());
        }
        // WIFEXITED: the low 7 bits are zero and the code is in the next byte. Any signal death
        // maps to 134, as `protocol::finish` does for the file-based run.
        Ok(if status & 0x7f == 0 { (status >> 8) & 0xff } else { 134 })
    }
}

/// True when the OS lists no thread in this process but the caller (Linux:
/// /proc/self/task). A thread joined just before can stay listed for a
/// moment while it exits, so this waits up to 50 ms for the list to settle.
/// False when the list cannot be read. Other Unix targets have no such list
/// and return true: there the pins in `run_in_memory`'s contract must hold.
#[cfg(unix)]
fn lone_thread() -> bool {
    #[cfg(target_os = "linux")]
    {
        let start = std::time::Instant::now();
        loop {
            let Ok(list) = std::fs::read_dir("/proc/self/task") else { return false };
            if list.count() <= 1 {
                return true;
            }
            // A joined pool thread can stay in the task list while the kernel reaps it; on a
            // loaded machine that took over 50 ms (gates at load 150 fell back to the file run).
            if start.elapsed() > std::time::Duration::from_millis(500) {
                return false;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }
    #[cfg(not(target_os = "linux"))]
    true
}

#[cfg(test)]
mod tests {
    /// `set_huge_pages` flips the process flag Linux reports as
    /// `THP_enabled` in /proc/self/status, and back.
    #[cfg(target_os = "linux")]
    #[test]
    fn huge_pages_switch() {
        let read = || {
            let status = std::fs::read_to_string("/proc/self/status").unwrap();
            status.lines().find_map(|l| l.strip_prefix("THP_enabled:")).map(|v| v.trim().to_string())
        };
        if read().is_none() {
            return; // a kernel without the field
        }
        super::set_huge_pages(false);
        assert_eq!(read().as_deref(), Some("0"));
        super::set_huge_pages(true);
        assert_eq!(read().as_deref(), Some("1"));
    }

    /// The external path (more than two units) compiles every unit
    /// through the bounded worker set: all objects land on disk, and
    /// one bad unit fails the whole call with its error text.
    #[test]
    fn compile_units_external_path_compiles_all_and_reports_errors() {
        let dir = std::env::temp_dir().join(format!("lust-tcc-units-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let units: Vec<(std::path::PathBuf, String)> =
            (0..9).map(|i| (dir.join(format!("u{i}.o")), format!("int f{i}(void) {{ return {i}; }}\n"))).collect();
        super::compile_units(&units, false).unwrap();
        for (obj, _) in &units {
            assert!(obj.exists(), "{} was compiled", obj.display());
        }
        let mut bad = units.clone();
        bad[4].1 = "int broken( {\n".to_string();
        let err = super::compile_units(&bad, false).unwrap_err();
        assert!(err.contains("tcc failed to compile"), "{err}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// `lone_thread` counts every thread the OS lists, not only pool threads:
    /// a parked thread makes it false. The other side, one thread at the
    /// fork of a one-shot `lust run`, is what scripts/runtest.sh checks:
    /// every small program must take the in-memory path, and
    /// `run_in_memory` forks only when `lone_thread` holds.
    #[cfg(target_os = "linux")]
    #[test]
    fn lone_thread_sees_other_threads() {
        let (tx, rx) = std::sync::mpsc::channel::<()>();
        let parked = std::thread::spawn(move || {
            let _ = rx.recv();
        });
        assert!(!super::lone_thread());
        drop(tx);
        parked.join().unwrap();
    }
}
