// `std::process` (W-SHIM): the process id, exit, and abort, plus
// `Command` and friends (W-SHIM phase 2). The file is
// `process_os.rs` because `process.rs` is the compiler's own std source
// for `exit` (src/stdload.rs); `platform.rs` names this one with
// `#[path]`. Both exit paths call the same runtime intrinsic.
//
// Spawning runs over fork and execvpe in src/runtime/sysio.c, as std
// does it on Linux: PATH search through the child's environment,
// an error pipe for exec failures, `/dev/null` and pipe stdio, and
// the working directory applied in the child. The environment the
// child sees is std's: the parent's as-is when nothing was changed,
// else the sorted merge of the parent's with the command's changes.

use crate::ffi::{os_str_from_bytes, OsStr, OsString};
use crate::io;
use crate::path::{Path, PathBuf};
use core::fmt;

/// The OS process id.
pub fn id() -> u32 {
    core::intrinsics::sys_getpid()
}

/// Terminates the process with the given exit code. Destructors do not
/// run; buffered stdout is flushed first (the intrinsic does this).
pub fn exit(code: i32) -> ! {
    core::intrinsics::exit(code)
}

/// The name of a signal number, as std prints it on Linux.
#[cfg(target_os = "linux")]
fn signal_name(sig: i32) -> Option<&'static str> {
    Some(match sig {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        5 => "SIGTRAP",
        6 => "SIGABRT",
        7 => "SIGBUS",
        8 => "SIGFPE",
        9 => "SIGKILL",
        10 => "SIGUSR1",
        11 => "SIGSEGV",
        12 => "SIGUSR2",
        13 => "SIGPIPE",
        14 => "SIGALRM",
        15 => "SIGTERM",
        16 => "SIGSTKFLT",
        17 => "SIGCHLD",
        18 => "SIGCONT",
        19 => "SIGSTOP",
        20 => "SIGTSTP",
        21 => "SIGTTIN",
        22 => "SIGTTOU",
        23 => "SIGURG",
        24 => "SIGXCPU",
        25 => "SIGXFSZ",
        26 => "SIGVTALRM",
        27 => "SIGPROF",
        28 => "SIGWINCH",
        29 => "SIGIO",
        30 => "SIGPWR",
        31 => "SIGSYS",
        _ => return None,
    })
}

/// The name of a signal number, as std prints it on macOS: the same
/// names by signal, with Darwin's numbers (SIGEMT and SIGINFO exist
/// there, SIGSTKFLT and SIGPWR do not).
#[cfg(target_os = "macos")]
fn signal_name(sig: i32) -> Option<&'static str> {
    Some(match sig {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        5 => "SIGTRAP",
        6 => "SIGABRT",
        7 => "SIGEMT",
        8 => "SIGFPE",
        9 => "SIGKILL",
        10 => "SIGBUS",
        11 => "SIGSEGV",
        12 => "SIGSYS",
        13 => "SIGPIPE",
        14 => "SIGALRM",
        15 => "SIGTERM",
        16 => "SIGURG",
        17 => "SIGSTOP",
        18 => "SIGTSTP",
        19 => "SIGCONT",
        20 => "SIGCHLD",
        21 => "SIGTTIN",
        22 => "SIGTTOU",
        23 => "SIGIO",
        24 => "SIGXCPU",
        25 => "SIGXFSZ",
        26 => "SIGVTALRM",
        27 => "SIGPROF",
        28 => "SIGWINCH",
        29 => "SIGINFO",
        30 => "SIGUSR1",
        31 => "SIGUSR2",
        _ => return None,
    })
}

/// The exit status of a finished child process: the raw wait status
/// the OS reported.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ExitStatus {
    raw: i32,
}

impl ExitStatus {
    pub(crate) fn from_wait_status(raw: i32) -> ExitStatus {
        ExitStatus { raw }
    }

    /// True when the process exited with code 0.
    pub fn success(&self) -> bool {
        self.raw == 0
    }

    /// The exit code, when the process exited normally.
    pub fn code(&self) -> Option<i32> {
        if self.raw & 0x7f == 0 {
            Some((self.raw >> 8) & 0xff)
        } else {
            None
        }
    }

    /// The raw wait status (`ExitStatusExt::into_raw`).
    pub(crate) fn raw(&self) -> i32 {
        self.raw
    }

    /// glibc's `WIFSIGNALED` then `WTERMSIG`: the signal that ended
    /// the process (`ExitStatusExt::signal`).
    pub(crate) fn signal_raw(&self) -> Option<i32> {
        if (((self.raw & 0x7f) + 1) as i8 >> 1) > 0 { Some(self.raw & 0x7f) } else { None }
    }

    /// glibc's `WIFSTOPPED` then `WSTOPSIG` (`ExitStatusExt::stopped_signal`).
    /// Darwin's: the low 7 bits are 0x7f, the signal (`x >> 8`, unmasked) is
    /// not SIGCONT (that is a continue).
    pub(crate) fn stopped_raw(&self) -> Option<i32> {
        if cfg!(target_os = "macos") {
            return if self.raw & 0x7f == 0x7f && self.raw >> 8 != 0x13 { Some(self.raw >> 8) } else { None };
        }
        if self.raw & 0xff == 0x7f { Some((self.raw >> 8) & 0xff) } else { None }
    }

    /// glibc's `WIFCONTINUED` (0xffff); Darwin's is a stop by SIGCONT
    /// (`ExitStatusExt::continued`).
    pub(crate) fn continued_raw(&self) -> bool {
        if cfg!(target_os = "macos") { self.raw & 0x7f == 0x7f && self.raw >> 8 == 0x13 } else { self.raw == 0xffff }
    }
}

impl fmt::Display for ExitStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // std's unix Display: exited, signaled, stopped, continued, or
        // an unrecognised raw status (`ExitStatusExt::from_raw`).
        let name = |sig: i32| match signal_name(sig) {
            Some(name) => format!(" ({name})"),
            None => String::new(),
        };
        if let Some(code) = self.code() {
            write!(f, "exit status: {code}")
        } else if let Some(sig) = self.signal_raw() {
            let core = if self.raw & 0x80 != 0 { " (core dumped)" } else { "" };
            write!(f, "signal: {sig}{}{core}", name(sig))
        } else if let Some(sig) = self.stopped_raw() {
            write!(f, "stopped (not terminated) by signal: {sig}{}", name(sig))
        } else if self.continued_raw() {
            write!(f, "continued (WIFCONTINUED)")
        } else {
            write!(f, "unrecognised wait status: {} {:#x}", self.raw, self.raw)
        }
    }
}

/// Std's unix inner status Debug: `unix_wait_status(N)`.
struct WaitStatus(i32);

impl fmt::Debug for WaitStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("unix_wait_status").field(&self.0).finish()
    }
}

/// Std derives it over the inner status: `ExitStatus(unix_wait_status(N))`.
impl fmt::Debug for ExitStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ExitStatus").field(&WaitStatus(self.raw)).finish()
    }
}

/// Bytes as std's `Output` Debug prints them: the lossy text, Debug
/// formatted.
struct LossyBytes<'a>(&'a [u8]);

impl fmt::Debug for LossyBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        core::intrinsics::sys_utf8_lossy(self.0, &mut text);
        write!(f, "{text:?}")
    }
}

/// The output of a finished child process (`Command::output`).
pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl fmt::Debug for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Output")
            .field("status", &self.status)
            .field("stdout", &LossyBytes(&self.stdout))
            .field("stderr", &LossyBytes(&self.stderr))
            .finish()
    }
}

/// What one of a child's standard streams connects to.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum StdioKind {
    Inherit,
    Null,
    Piped,
    /// An owned file descriptor (a `File`, a child's pipe).
    Fd(i32),
}

impl StdioKind {
    /// The 2-bit spec of the spawn intrinsic (see sysio.c).
    fn spec(self) -> u32 {
        match self {
            StdioKind::Inherit => 0,
            StdioKind::Null => 1,
            StdioKind::Piped => 2,
            StdioKind::Fd(_) => 3,
        }
    }

    fn fd(self) -> i32 {
        match self {
            StdioKind::Fd(fd) => fd,
            _ => -1,
        }
    }

    /// The name std's alternate `Command` Debug prints.
    fn name(self) -> &'static str {
        match self {
            StdioKind::Inherit => "Inherit",
            StdioKind::Null => "Null",
            StdioKind::Piped => "MakePipe",
            StdioKind::Fd(_) => "File",
        }
    }
}

/// A description of what to do with a child's standard stream
/// (`Command::stdin` and friends).
pub struct Stdio {
    kind: StdioKind,
}

impl Stdio {
    /// The child inherits the stream from the parent.
    pub fn inherit() -> Stdio {
        Stdio { kind: StdioKind::Inherit }
    }

    /// The stream connects to `/dev/null`.
    pub fn null() -> Stdio {
        Stdio { kind: StdioKind::Null }
    }

    /// The stream connects to a pipe the parent holds.
    pub fn piped() -> Stdio {
        Stdio { kind: StdioKind::Piped }
    }

    /// Takes over an owned descriptor (for the `From` impls of
    /// `File` and the child pipes, within this crate).
    pub(crate) fn from_fd(fd: i32) -> Stdio {
        Stdio { kind: StdioKind::Fd(fd) }
    }
}

impl Drop for Stdio {
    fn drop(&mut self) {
        if let StdioKind::Fd(fd) = self.kind {
            if fd >= 0 {
                let _ = core::intrinsics::sys_fd_close(fd);
            }
        }
    }
}

impl fmt::Debug for Stdio {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stdio").finish_non_exhaustive()
    }
}

/// One environment entry: a key and its value (`None` removes the
/// key). Entries are kept sorted by key, as std's command environment
/// is a sorted map.
type EnvEntry = (Vec<u8>, Option<Vec<u8>>);

/// Inserts or replaces an entry in the sorted list.
fn env_insert(list: &mut Vec<EnvEntry>, key: Vec<u8>, value: Option<Vec<u8>>) {
    for i in 0..list.len() {
        if list[i].0 == key {
            list[i].1 = value;
            return;
        }
        if list[i].0 > key {
            list.insert(i, (key, value));
            return;
        }
    }
    list.push((key, value));
}

/// True when the bytes hold a NUL byte.
fn has_nul(bytes: &[u8]) -> bool {
    for i in 0..bytes.len() {
        if bytes[i] == 0 {
            return true;
        }
    }
    false
}

/// std's error for a NUL byte in a program, argument, environment
/// string, or working directory.
fn nul_error() -> io::Error {
    io::Error::simple_message(io::ErrorKind::InvalidInput, "nul byte found in provided data")
}

/// A process builder: a program, its arguments, environment changes,
/// working directory, and stdio configuration.
pub struct Command {
    program: Vec<u8>,
    /// `CommandExt::arg0`: the child's argv[0] when set (else the program).
    arg0: Option<Vec<u8>>,
    args: Vec<Vec<u8>>,
    envs: Vec<EnvEntry>,
    clear: bool,
    cwd: Option<Vec<u8>>,
    stdin: Option<Stdio>,
    stdout: Option<Stdio>,
    stderr: Option<Stdio>,
}

impl Command {
    /// Creates a builder for the program.
    pub fn new<S: AsRef<OsStr>>(program: S) -> Command {
        Command {
            program: program.as_ref().as_encoded_bytes().to_vec(),
            arg0: None,
            args: Vec::new(),
            envs: Vec::new(),
            clear: false,
            cwd: None,
            stdin: None,
            stdout: None,
            stderr: None,
        }
    }

    /// Adds one argument.
    pub fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Command {
        self.args.push(arg.as_ref().as_encoded_bytes().to_vec());
        self
    }

    /// Adds several arguments.
    pub fn args<I, S>(&mut self, args: I) -> &mut Command
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        for arg in args {
            self.arg(arg);
        }
        self
    }

    /// Sets an environment variable for the child.
    pub fn env<K: AsRef<OsStr>, V: AsRef<OsStr>>(&mut self, key: K, val: V) -> &mut Command {
        env_insert(&mut self.envs, key.as_ref().as_encoded_bytes().to_vec(), Some(val.as_ref().as_encoded_bytes().to_vec()));
        self
    }

    /// Sets several environment variables for the child.
    pub fn envs<I, K, V>(&mut self, vars: I) -> &mut Command
    where
        I: IntoIterator<Item = (K, V)>,
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        for (key, val) in vars {
            self.env(key, val);
        }
        self
    }

    /// Removes an environment variable from the child's environment.
    pub fn env_remove<K: AsRef<OsStr>>(&mut self, key: K) -> &mut Command {
        env_insert(&mut self.envs, key.as_ref().as_encoded_bytes().to_vec(), None);
        self
    }

    /// The child gets exactly the variables set on this builder, not
    /// the parent's.
    pub fn env_clear(&mut self) -> &mut Command {
        self.clear = true;
        self
    }

    /// The child's working directory.
    pub fn current_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Command {
        self.cwd = Some(dir.as_ref().as_os_str().as_encoded_bytes().to_vec());
        self
    }

    /// What the child's stdin connects to.
    pub fn stdin(&mut self, cfg: Stdio) -> &mut Command {
        self.stdin = Some(cfg);
        self
    }

    /// What the child's stdout connects to.
    pub fn stdout(&mut self, cfg: Stdio) -> &mut Command {
        self.stdout = Some(cfg);
        self
    }

    /// What the child's stderr connects to.
    pub fn stderr(&mut self, cfg: Stdio) -> &mut Command {
        self.stderr = Some(cfg);
        self
    }

    /// `CommandExt::arg0` (os.rs): the child's argv[0].
    pub(crate) fn set_arg0(&mut self, arg: &OsStr) {
        self.arg0 = Some(arg.as_encoded_bytes().to_vec());
    }

    /// The child's argv[0]: arg0 when set, else the program.
    fn argv0(&self) -> &Vec<u8> {
        match &self.arg0 {
            Some(a) => a,
            None => &self.program,
        }
    }

    /// The program.
    pub fn get_program(&self) -> &OsStr {
        os_str_from_bytes(&self.program)
    }

    /// The working directory, when one was set.
    pub fn get_current_dir(&self) -> Option<&Path> {
        match &self.cwd {
            Some(bytes) => Some(Path::new(os_str_from_bytes(bytes))),
            None => None,
        }
    }

    /// The child environment as packed bytes for the spawn
    /// intrinsic: a mode byte (0 inherit as-is, 1 the sorted merge
    /// that follows, each entry `K=V` and NUL-terminated).
    fn packed_env(&self) -> Vec<u8> {
        if !self.clear && self.envs.is_empty() {
            return vec![0];
        }
        let mut list: Vec<EnvEntry> = Vec::new();
        if !self.clear {
            let mut raw: Vec<u8> = Vec::new();
            core::intrinsics::sys_environ(&mut raw);
            let mut start = 0;
            for i in 0..raw.len() {
                if raw[i] == 0 {
                    let entry = &raw[start..i];
                    let mut eq = entry.len();
                    for j in 0..entry.len() {
                        if entry[j] == b'=' {
                            eq = j;
                            break;
                        }
                    }
                    let value = if eq < entry.len() { entry[eq + 1..].to_vec() } else { Vec::new() };
                    env_insert(&mut list, entry[..eq].to_vec(), Some(value));
                    start = i + 1;
                }
            }
        }
        for i in 0..self.envs.len() {
            let (key, value) = &self.envs[i];
            let value = match value {
                Some(v) => Some(v.clone()),
                None => None,
            };
            env_insert(&mut list, key.clone(), value);
        }
        let mut packed: Vec<u8> = vec![1];
        for i in 0..list.len() {
            let (key, value) = &list[i];
            if let Some(v) = value {
                packed.extend_from_slice(key);
                packed.push(b'=');
                packed.extend_from_slice(v);
                packed.push(0);
            }
        }
        packed
    }

    /// `CommandExt::exec` (os.rs): replaces this process with the
    /// program, unconfigured streams inherited, as std's `exec`. Returns
    /// only the error of a failed exec (std's "nul byte" error first).
    pub(crate) fn exec_here(&mut self) -> io::Error {
        let (argv, cwd) = match self.checked_argv() {
            Ok(parts) => parts,
            Err(e) => return e,
        };
        let env = self.packed_env();
        let specs = [
            Command::kind_of(&self.stdin, StdioKind::Inherit),
            Command::kind_of(&self.stdout, StdioKind::Inherit),
            Command::kind_of(&self.stderr, StdioKind::Inherit),
        ];
        let (word, fds) = self.stdio_word(specs);
        let code = core::intrinsics::sys_proc_exec(&self.program, &argv, &env, &cwd, word, &fds);
        io::Error::from_raw_os_error(code)
    }

    /// The NUL-separated argv and the cwd bytes of a spawn or exec, or
    /// std's error for a NUL byte in the program, an argument, an
    /// environment change, or the working directory.
    fn checked_argv(&self) -> io::Result<(Vec<u8>, Vec<u8>)> {
        if has_nul(&self.program) || has_nul(self.argv0()) {
            return Err(nul_error());
        }
        let mut argv: Vec<u8> = Vec::new();
        argv.extend_from_slice(self.argv0());
        argv.push(0);
        for i in 0..self.args.len() {
            if has_nul(&self.args[i]) {
                return Err(nul_error());
            }
            argv.extend_from_slice(&self.args[i]);
            argv.push(0);
        }
        for i in 0..self.envs.len() {
            let (key, value) = &self.envs[i];
            if let Some(v) = value {
                if has_nul(key) || has_nul(v) {
                    return Err(nul_error());
                }
            }
        }
        let cwd_owned: Vec<u8> = match &self.cwd {
            Some(bytes) => {
                if has_nul(bytes) {
                    return Err(nul_error());
                }
                bytes.clone()
            }
            None => Vec::new(),
        };
        Ok((argv, cwd_owned))
    }

    /// The stdio spec word and packed fds of the spawn and exec
    /// intrinsics (sysio.c has the format).
    fn stdio_word(&self, specs: [StdioKind; 3]) -> (u32, Vec<u8>) {
        let mut fds: Vec<u8> = Vec::new();
        for i in 0..3 {
            let v = specs[i].fd() as i64 as u64;
            for k in 0..8 {
                fds.push((v >> (8 * k)) as u8);
            }
        }
        let word = specs[0].spec() | (specs[1].spec() << 2) | (specs[2].spec() << 4) | if self.cwd.is_some() { 64 } else { 0 };
        (word, fds)
    }

    /// Spawns the child with the given stdio configuration (the
    /// entry points below supply std's defaults for their operation).
    fn spawn_with(&self, specs: [StdioKind; 3]) -> io::Result<Child> {
        let (argv, cwd_owned) = self.checked_argv()?;
        let cwd_bytes: &[u8] = &cwd_owned;
        let env = self.packed_env();
        let (word, fds) = self.stdio_word(specs);
        let mut out: Vec<u8> = Vec::new();
        let code = core::intrinsics::sys_proc_spawn(&self.program, &argv, &env, cwd_bytes, word, &fds, &mut out);
        if code != 0 {
            return Err(io::Error::from_raw_os_error(code));
        }
        let field = |i: usize| {
            let mut v: u64 = 0;
            for k in 0..8 {
                v |= (out[i * 8 + k] as u64) << (8 * k);
            }
            v as i64
        };
        let stdin_fd = field(1);
        let stdout_fd = field(2);
        let stderr_fd = field(3);
        Ok(Child {
            pid: field(0) as u32,
            stdin: if stdin_fd >= 0 { Some(ChildStdin { fd: stdin_fd as i32 }) } else { None },
            stdout: if stdout_fd >= 0 { Some(ChildStdout { fd: stdout_fd as i32 }) } else { None },
            stderr: if stderr_fd >= 0 { Some(ChildStderr { fd: stderr_fd as i32 }) } else { None },
            status: None,
        })
    }

    /// The configured kind of one stream, or the default.
    fn kind_of(cfg: &Option<Stdio>, default: StdioKind) -> StdioKind {
        match cfg {
            Some(s) => s.kind,
            None => default,
        }
    }

    /// Starts the child process. Unconfigured streams are inherited.
    pub fn spawn(&mut self) -> io::Result<Child> {
        self.spawn_with([
            Command::kind_of(&self.stdin, StdioKind::Inherit),
            Command::kind_of(&self.stdout, StdioKind::Inherit),
            Command::kind_of(&self.stderr, StdioKind::Inherit),
        ])
    }

    /// Starts the child, waits for it, and returns its exit status.
    /// Unconfigured streams are inherited.
    pub fn status(&mut self) -> io::Result<ExitStatus> {
        let mut child = self.spawn()?;
        child.wait()
    }

    /// Starts the child, waits for it, and collects its output.
    /// Unconfigured stdout and stderr are piped here, stdin is
    /// connected to `/dev/null`.
    pub fn output(&mut self) -> io::Result<Output> {
        let child = self.spawn_with([
            Command::kind_of(&self.stdin, StdioKind::Null),
            Command::kind_of(&self.stdout, StdioKind::Piped),
            Command::kind_of(&self.stderr, StdioKind::Piped),
        ])?;
        child.wait_with_output()
    }
}

/// A running (or finished) child process.
pub struct Child {
    pid: u32,
    pub stdin: Option<ChildStdin>,
    pub stdout: Option<ChildStdout>,
    pub stderr: Option<ChildStderr>,
    status: Option<ExitStatus>,
}

impl fmt::Debug for Child {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Child").field("stdin", &self.stdin).field("stdout", &self.stdout).field("stderr", &self.stderr).finish_non_exhaustive()
    }
}

impl Child {
    /// The child's process id.
    pub fn id(&self) -> u32 {
        self.pid
    }

    /// Waits for the child to finish (its stdin is closed first, as
    /// in std). Waiting again returns the same status.
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        if let Some(st) = self.status {
            return Ok(st);
        }
        self.stdin = None;
        let v = core::intrinsics::sys_proc_wait(self.pid, true);
        if v >= 0 {
            let st = ExitStatus::from_wait_status(v as i32);
            self.status = Some(st);
            Ok(st)
        } else {
            Err(io::Error::from_raw_os_error((-v) as i32))
        }
    }

    /// The child's exit status, when it has finished.
    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        if let Some(st) = self.status {
            return Ok(Some(st));
        }
        let v = core::intrinsics::sys_proc_wait(self.pid, false);
        if v >= 0 {
            let st = ExitStatus::from_wait_status(v as i32);
            self.status = Some(st);
            Ok(Some(st))
        } else if v == -2 {
            Ok(None)
        } else {
            Err(io::Error::from_raw_os_error((-v) as i32))
        }
    }

    /// Kills the child with SIGKILL. Killing a child that already
    /// exited is fine.
    pub fn kill(&mut self) -> io::Result<()> {
        if let Ok(Some(_)) = self.try_wait() {
            return Ok(());
        }
        let code = core::intrinsics::sys_proc_kill(self.pid);
        if code == 0 {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(code))
        }
    }

    /// Drops stdin, reads stdout and stderr to the end, waits, and
    /// collects the output.
    pub fn wait_with_output(mut self) -> io::Result<Output> {
        self.stdin = None;
        let out_fd = match &self.stdout {
            Some(s) => s.fd,
            None => -1,
        };
        let err_fd = match &self.stderr {
            Some(s) => s.fd,
            None => -1,
        };
        let mut stdout: Vec<u8> = Vec::new();
        let mut stderr: Vec<u8> = Vec::new();
        let code = core::intrinsics::sys_fd_read_both(out_fd, &mut stdout, err_fd, &mut stderr);
        self.stdout = None;
        self.stderr = None;
        let status = self.wait()?;
        if code != 0 {
            return Err(io::Error::from_raw_os_error(code));
        }
        Ok(Output { status, stdout, stderr })
    }
}

/// The child's stdin pipe handle.
pub struct ChildStdin {
    fd: i32,
}

/// The child's stdout pipe handle.
pub struct ChildStdout {
    fd: i32,
}

/// The child's stderr pipe handle.
pub struct ChildStderr {
    fd: i32,
}

impl Drop for ChildStdin {
    fn drop(&mut self) {
        if self.fd >= 0 {
            let _ = core::intrinsics::sys_fd_close(self.fd);
        }
    }
}

impl Drop for ChildStdout {
    fn drop(&mut self) {
        if self.fd >= 0 {
            let _ = core::intrinsics::sys_fd_close(self.fd);
        }
    }
}

impl Drop for ChildStderr {
    fn drop(&mut self) {
        if self.fd >= 0 {
            let _ = core::intrinsics::sys_fd_close(self.fd);
        }
    }
}

impl fmt::Debug for ChildStdin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChildStdin").finish_non_exhaustive()
    }
}

impl fmt::Debug for ChildStdout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChildStdout").finish_non_exhaustive()
    }
}

impl fmt::Debug for ChildStderr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChildStderr").finish_non_exhaustive()
    }
}

impl io::Write for ChildStdin {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        io::write_fd(self.fd, buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl io::Read for ChildStdout {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        io::read_fd(self.fd, buf)
    }
}

impl io::Read for ChildStderr {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        io::read_fd(self.fd, buf)
    }
}

impl From<ChildStdin> for Stdio {
    fn from(mut child: ChildStdin) -> Stdio {
        let fd = child.fd;
        child.fd = -1;
        Stdio::from_fd(fd)
    }
}

impl From<ChildStdout> for Stdio {
    fn from(mut child: ChildStdout) -> Stdio {
        let fd = child.fd;
        child.fd = -1;
        Stdio::from_fd(fd)
    }
}

impl From<ChildStderr> for Stdio {
    fn from(mut child: ChildStderr) -> Stdio {
        let fd = child.fd;
        child.fd = -1;
        Stdio::from_fd(fd)
    }
}

/// The bytes as an `OsString` (for the `Command` Debug forms).
fn os_string(bytes: &[u8]) -> OsString {
    OsString::__from_vec(bytes.to_vec())
}

/// The `CommandEnv` value of the alternate `Command` Debug.
struct EnvDebug<'a> {
    clear: bool,
    envs: &'a [EnvEntry],
}

impl fmt::Debug for EnvDebug<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vars: Vec<(OsString, Option<OsString>)> = Vec::new();
        for i in 0..self.envs.len() {
            let (key, value) = &self.envs[i];
            let value = match value {
                Some(v) => Some(os_string(v)),
                None => None,
            };
            vars.push((os_string(key), value));
        }
        f.debug_struct("CommandEnv").field("clear", &self.clear).field("vars", &MapOf(vars)).finish()
    }
}

/// A helper so vars can be built before the struct starts writing.
/// (The map contents themselves are written by this Debug.)
struct MapOf(Vec<(OsString, Option<OsString>)>);

impl fmt::Debug for MapOf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for i in 0..self.0.len() {
            let (k, v) = &self.0[i];
            map.entry(k, v);
        }
        map.finish()
    }
}

/// One stdio field of the alternate `Command` Debug.
struct StdioField(StdioKind);

impl fmt::Debug for StdioField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.name())
    }
}

/// Bytes std holds as a `CString` in a `Command`: `ByteStr`'s Debug.
struct CBytes<'a>(&'a [u8]);

impl fmt::Debug for CBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::ffi::__lust_bytestr_debug(self.0, f)
    }
}

impl fmt::Debug for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            // std keeps the program, argv, and cwd as CStrings: their
            // Debug is `ByteStr`'s (`CBytes`).
            let mut args: Vec<CBytes<'_>> = vec![CBytes(self.argv0())];
            for i in 0..self.args.len() {
                args.push(CBytes(&self.args[i]));
            }
            let mut s = f.debug_struct("Command");
            s.field("program", &CBytes(&self.program));
            s.field("args", &args);
            if self.clear || !self.envs.is_empty() {
                s.field("env", &EnvDebug { clear: self.clear, envs: &self.envs });
            }
            if let Some(cwd) = &self.cwd {
                s.field("cwd", &Some(CBytes(cwd)));
            }
            if let Some(cfg) = &self.stdin {
                s.field("stdin", &Some(StdioField(cfg.kind)));
            }
            if let Some(cfg) = &self.stdout {
                s.field("stdout", &Some(StdioField(cfg.kind)));
            }
            if let Some(cfg) = &self.stderr {
                s.field("stderr", &Some(StdioField(cfg.kind)));
            }
            // std has the field on Linux only.
            if cfg!(target_os = "linux") {
                s.field("create_pidfd", &false);
            }
            return s.finish();
        }
        if let Some(cwd) = &self.cwd {
            write!(f, "cd {:?} && ", CBytes(cwd))?;
        }
        if self.clear || !self.envs.is_empty() {
            // The `env` command is only needed to clear or remove
            // variables; plain assignments are shell syntax already.
            let mut needs_env_cmd = self.clear;
            for i in 0..self.envs.len() {
                if self.envs[i].1.is_none() {
                    needs_env_cmd = true;
                }
            }
            if needs_env_cmd {
                write!(f, "env ")?;
            }
            if self.clear {
                write!(f, "-i ")?;
            } else {
                for i in 0..self.envs.len() {
                    let (key, value) = &self.envs[i];
                    if value.is_none() {
                        let mut text = String::new();
                        core::intrinsics::sys_utf8_lossy(key, &mut text);
                        write!(f, "-u {text} ")?;
                    }
                }
            }
            for i in 0..self.envs.len() {
                let (key, value) = &self.envs[i];
                if let Some(v) = value {
                    let mut text = String::new();
                    core::intrinsics::sys_utf8_lossy(key, &mut text);
                    write!(f, "{text}={:?} ", os_string(v))?;
                }
            }
        }
        // std prints a changed argv[0] after the program in brackets.
        if *self.argv0() != self.program {
            write!(f, "[{:?}] ", CBytes(&self.program))?;
        }
        write!(f, "{:?}", CBytes(self.argv0()))?;
        for i in 0..self.args.len() {
            write!(f, " {:?}", os_string(&self.args[i]))?;
        }
        Ok(())
    }
}
