// The external C compiler backend (`lust build --release --target ...`):
// one lust front-end run per target cfg, then every emitted C unit compiles
// in parallel with `zig cc` (or clang/cc where that reaches the target) and
// links into the release binary. tcc stays the dev backend; this path runs
// only for `Request::cc` builds, which the daemon never serves.
//
// Flags are rel-opt's release set (round 1 report): optimized, with the
// aliasing and wrapping rules the emitted C relies on, plus -fexceptions
// and -lunwind so a unit set built for zero-cost unwinding (rel-opt round
// 2) links unchanged. `LUST_CC` replaces the compiler command (for example
// `LUST_CC="clang-18"` on a box with no zig, for host-reachable targets).
// A build with unwind tables has one C++ unit (a name ending in `.cc`, the
// throw and the catch of src/runtime/unwind.cc): the C++ driver of the same
// compiler (`CcSpec::cxx`) compiles it and links the binary, which brings
// in the C++ runtime and personality.
//
// Objects go through the disk cache: `unit_key` below is the one seam a
// smarter object cache (rel-cache) takes over. Its inputs are the C text,
// the compiler identity, the flag string, the Rust target triple, and with
// PGO (`cc/pgo.rs`) the unit's own part of the profile; an object is a
// function of those alone.
use std::path::{Path, PathBuf};
use std::process::Command;

mod memo;
pub(crate) mod pgo;
mod rtinl;
mod stream;

pub use memo::{CcError, UnitIn};
pub use stream::Stream;

/// One target's compiler setup: the command words, the flags every unit
/// gets, and how the link differs from a host link.
#[derive(Clone, Debug)]
pub struct CcSpec {
    /// The Rust triple as the user named it (the front end's cfg target).
    pub triple: String,
    /// Compiler command words, for example ["zig", "cc", "-target", "aarch64-linux-musl"].
    pub cmd: Vec<String>,
    /// The C++ driver of the same compiler (`cxx_for`), for a `.cc` unit and its link.
    pub cxx: Vec<String>,
    /// Static link (musl release binaries, as ts-rust ships them).
    pub statik: bool,
    /// File name suffix of the output (".exe" on Windows triples).
    pub exe_suffix: &'static str,
}

/// The zig target spelling of a Rust triple. The front end keeps the Rust
/// cfg (a windows-msvc triple checks as msvc); only the C compiler and
/// linker see gnu, which is all zig ships libraries for.
pub fn zig_target(triple: &str) -> Option<&'static str> {
    Some(match triple {
        "x86_64-unknown-linux-gnu" => "x86_64-linux-gnu",
        "x86_64-unknown-linux-musl" => "x86_64-linux-musl",
        "aarch64-unknown-linux-gnu" => "aarch64-linux-gnu",
        "aarch64-unknown-linux-musl" => "aarch64-linux-musl",
        "aarch64-apple-darwin" => "aarch64-macos",
        "x86_64-apple-darwin" => "x86_64-macos",
        "x86_64-pc-windows-msvc" | "x86_64-pc-windows-gnu" => "x86_64-windows-gnu",
        "aarch64-pc-windows-msvc" => "aarch64-windows-gnu",
        _ => return None,
    })
}

/// True when `prog` names zig (`zig`, `/opt/zig/zig`).
fn is_zig(prog: &str) -> bool {
    Path::new(prog).file_stem().is_some_and(|s| s == "zig")
}

/// The clang flags that give zig cc's code for a zig target when zig's clang runs directly
/// (`unit_words`): the triple, no libc headers, and what zig cc adds (static relocation,
/// NDEBUG, sync unwind tables, the CPU's tuning), from zig 0.15's `ZIG_VERBOSE_CC=1` child
/// command. `direct_clang_gives_zig_cc_code` checks the code. Other targets keep zig cc.
fn direct_flags(zig_target: &str) -> Option<&'static [&'static str]> {
    match zig_target {
        "x86_64-linux-musl" => Some(&["--target=x86_64-linux-musl", "-nostdinc", "-fno-pic", "-fno-pie", "-DNDEBUG", "-funwind-tables", "-mtune=x86-64"]),
        _ => None,
    }
}

/// The command words that compile a C unit: `spec.cmd`, or for a release build through zig
/// cc to a target `direct_flags` lists, zig's clang run directly. zig cc runs three processes
/// a compile (itself, with its object cache and a thread pool; a clang child; an `ld.lld -r`
/// child that relinks the one object): 10-20% of the CPU of a warm merge's missed units
/// (tsgo replay m9, m11). The direct clang is one process with the same code. A unit that
/// includes a system header keeps zig cc, which supplies libc's; LUST_CC's words after the
/// target carry over.
fn unit_words(spec: &CcSpec, debug: bool, sys_headers: bool) -> std::borrow::Cow<'_, [String]> {
    let cmd = &spec.cmd;
    let direct = match cmd.as_slice() {
        [zig, cc, t, zt, ..] if !debug && !sys_headers && is_zig(zig) && cc == "cc" && t == "-target" => direct_flags(zt),
        _ => None,
    };
    match direct {
        Some(flags) => [cmd[0].clone(), "clang".into()].into_iter().chain(flags.iter().map(|f| f.to_string())).chain(cmd[4..].iter().cloned()).collect(),
        None => cmd.as_slice().into(),
    }
}

/// The C++ driver that goes with a C compiler command: `zig cc` -> `zig c++`,
/// `clang[-N]` -> `clang++[-N]`, `[prefix-]gcc[-N]` -> `[prefix-]g++[-N]`, `cc` ->
/// `c++`; other names stay (they must take C++ themselves). `LUST_CXX` (words)
/// replaces it.
fn cxx_for(cmd: &[String]) -> Vec<String> {
    if let Ok(cxx) = std::env::var("LUST_CXX") {
        let words: Vec<String> = cxx.split_whitespace().map(str::to_string).collect();
        if !words.is_empty() {
            return words;
        }
    }
    let mut v = cmd.to_vec();
    if v.first().is_some_and(|c| is_zig(c)) {
        if let Some(w) = v.iter_mut().find(|w| *w == "cc") {
            *w = "c++".into();
        }
        return v;
    }
    let Some(first) = v.first_mut() else { return v };
    let path = Path::new(first.as_str());
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("").to_string();
    let cxx = if name.contains("++") {
        name
    } else if let Some(i) = name.rfind("clang") {
        format!("{}clang++{}", &name[..i], &name[i + 5..])
    } else if let Some(i) = name.rfind("gcc") {
        format!("{}g++{}", &name[..i], &name[i + 3..])
    } else if name == "cc" {
        "c++".into()
    } else {
        name
    };
    *first = path.with_file_name(cxx).to_string_lossy().into_owned();
    v
}

/// True when `prog` is an executable on PATH.
fn on_path(prog: &str) -> bool {
    if prog.contains('/') {
        return Path::new(prog).exists();
    }
    std::env::var_os("PATH").is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(prog).exists()))
}

/// The compiler spec for one Rust triple. `LUST_CC` (words split on
/// spaces) wins; a zig command gets `-target` appended when it does not
/// carry one. Without it: zig when present, else the host `cc` for a
/// triple this host already is (same arch and OS), else an error that
/// names the fix.
pub fn spec_for(triple: &str) -> Result<CcSpec, String> {
    let zt = zig_target(triple).ok_or_else(|| format!("no C compiler target for `{triple}`"))?;
    let statik = triple.ends_with("-musl");
    let exe_suffix = if triple.contains("windows") { ".exe" } else { "" };
    if let Ok(cc) = std::env::var("LUST_CC") {
        let mut cmd: Vec<String> = cc.split_whitespace().map(str::to_string).collect();
        if cmd.is_empty() {
            return Err("LUST_CC is empty".into());
        }
        if is_zig(&cmd[0]) && !cmd.iter().any(|a| a == "-target") {
            if cmd.len() == 1 {
                cmd.push("cc".into());
            }
            cmd.extend(["-target".into(), zt.into()]);
        }
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
    }
    if on_path("zig") {
        let cmd: Vec<String> = vec!["zig".into(), "cc".into(), "-target".into(), zt.into()];
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
    }
    let (arch, os) = (triple.split('-').next().unwrap_or(""), triple);
    let host_like = arch == std::env::consts::ARCH
        && ((os.contains("linux") && std::env::consts::OS == "linux") || (os.contains("darwin") && std::env::consts::OS == "macos"));
    if host_like && on_path("cc") {
        // A host clang/gcc reaches this target as far as this driver
        // checks (same arch and OS; a musl static link still needs the
        // musl toolchain, which the link error will name).
        let cmd = vec!["cc".to_string()];
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
    }
    Err(format!(
        "no C compiler for target `{triple}`: install zig (zig cc cross-compiles it) or set LUST_CC to a cross compiler command"
    ))
}

/// The C flags of every unit, one string so the cache key and the command
/// line can never disagree.
pub fn cflags(debug: bool) -> String {
    // -fsigned-char pins plain C char signed on every target (aarch64
    // defaults to unsigned): generated code keeps Rust bytes in
    // uint8_t and chars in uint32_t, so nothing should depend on it,
    // and after this flag nothing can (it also matches MSVC where the
    // windows-gnu build would otherwise differ on arm64).
    // -fomit-frame-pointer: zig cc keeps a frame pointer in every fn
    // (7% of a release tsgo's instructions); nothing walks them, as
    // unwinding reads .eh_frame. Targets whose ABI needs one keep it.
    // -O2: zig cc gives clang -O2 for -O1, -O2 and -O3 alike.
    // -g0: zig cc emits DWARF by default, which the release link strips
    // (`ldflags`); on a fn of 400 KB of C it was 7/8 of the compile.
    let base = "-O2 -std=gnu11 -w -fsigned-char -fno-strict-aliasing -fwrapv -fexceptions -fno-asynchronous-unwind-tables -fomit-frame-pointer";
    if debug { format!("{base} -g") } else { format!("{base} -g0") }
}

/// mimalloc as one C unit that replaces malloc and free (`MI_MALLOC_OVERRIDE`): the
/// allocator of musl release builds, whose own malloc ran tsgo 3.2x slower. Allocation
/// strategy is not observable. `MI_BUILD_RELEASE`: without it (or NDEBUG) mimalloc builds
/// its debug mode, with asserts on every call and warnings on stderr when memory runs out
/// (rustc's binary prints only its own message). None when the build had no mimalloc
/// source (build.rs).
pub fn mimalloc_unit() -> Option<String> {
    let src = include_str!(concat!(env!("OUT_DIR"), "/mimalloc.c"));
    (!src.is_empty()).then(|| format!("#define MI_MALLOC_OVERRIDE 1\n#define MI_BUILD_RELEASE 1\n{src}"))
}

/// Vector memcpy, memmove, memcmp, bcmp and memchr as one C unit for musl targets
/// (src/runtime/memfast.c): musl's and zig's forms are byte or word loops, which a release
/// tsgo spent 2.3 G instructions in on the TypeORM check. The results are libc's.
pub fn memfast_unit() -> String {
    include_str!("runtime/memfast.c").to_string()
}

/// The flags of a `.cc` unit (the runtime's throw and catch).
pub fn cxxflags(debug: bool) -> String {
    let base = "-O2 -w -fexceptions -fomit-frame-pointer";
    if debug { format!("{base} -g") } else { format!("{base} -g0") }
}

/// The link-time extras for one spec: libm for the float methods, the
/// unwinder for zig targets (its libc has none linked by default on musl
/// and windows-gnu), static where the spec asks, and a strip for release
/// size unless debug info was asked for.
fn ldflags(spec: &CcSpec, debug: bool) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    if spec.statik {
        v.push("-static".into());
    }
    if !debug {
        v.push("-s".into());
    } else {
        v.push("-g".into());
    }
    if spec.cmd.first().is_some_and(|c| is_zig(c)) {
        v.push("-lunwind".into());
    }
    if !spec.triple.contains("windows") {
        v.push("-pthread".into());
    }
    v.push("-lm".into());
    // Extra link flags, for measurement (for example section GC or hot/cold text grouping).
    if let Ok(extra) = std::env::var("LUST_RELEASE_LDFLAGS") {
        v.extend(extra.split_whitespace().map(str::to_string));
    }
    v
}

/// The compiler identity for keys: the command, its `--version` first line,
/// and the size and modification time of the binary it resolves to (an
/// in-place toolchain update moves the key). Computed once per process.
fn compiler_id(cmd: &[String]) -> String {
    static ID: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<Vec<String>, String>>> = std::sync::OnceLock::new();
    // One spec per process in practice (one lust-core per target); a map
    // keeps a second spec honest anyway.
    let map = ID.get_or_init(Default::default);
    if let Some(id) = map.lock().unwrap_or_else(|e| e.into_inner()).get(cmd).cloned() {
        return id;
    }
    // `zig cc --version` also writes an empty `a.o` in its working directory: run it in an
    // empty dir of its own, not in the user's. A relative compiler path must not resolve
    // against that dir (as in `unit_command`).
    static SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("lust-cc-version-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let prog = if cmd[0].contains('/') { std::fs::canonicalize(&cmd[0]).unwrap_or_else(|_| PathBuf::from(&cmd[0])) } else { PathBuf::from(&cmd[0]) };
    let ver = Command::new(prog)
        .args(&cmd[1..])
        .arg("--version")
        .current_dir(&dir)
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).lines().next().unwrap_or("").to_string())
        .unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    let stamp = std::fs::metadata(resolve_bin(&cmd[0])).map(|m| format!("{} {:?}", m.len(), m.modified().ok())).unwrap_or_default();
    let id = format!("{} | {ver} | {stamp}", cmd.join(" "));
    map.lock().unwrap_or_else(|e| e.into_inner()).insert(cmd.to_vec(), id.clone());
    id
}

/// The file a command name runs: the first PATH entry that has it, links resolved (the name
/// as given when none does).
fn resolve_bin(prog: &str) -> PathBuf {
    let bin = std::env::var_os("PATH")
        .and_then(|path| std::env::split_paths(&path).map(|d| d.join(prog)).find(|p| p.is_file()))
        .unwrap_or_else(|| PathBuf::from(prog));
    std::fs::canonicalize(&bin).unwrap_or(bin)
}

/// The disk cache key of one unit's object under this backend: the C (or,
/// `cxx`, C++) text, the compiler, the flags, the target, and `profile`, the
/// digest of the PGO data this unit's object depends on (see
/// `pgo::Mode::key_part`). A unit that includes system headers (the runtime
/// unit, the C++ unit) keys on its preprocessed text instead, so a header or
/// sysroot change moves its key; the other units include nothing.
pub fn unit_key(c_text: &str, pre: Option<&[u8]>, spec: &CcSpec, debug: bool, profile: Option<&str>, cxx: bool) -> String {
    let sys_headers = pre.is_some() || c_text.contains("#include <");
    let (words, flags) = if cxx { (spec.cxx.as_slice().into(), cxxflags(debug)) } else { (unit_words(spec, debug, sys_headers), cflags(debug)) };
    let id = compiler_id(&words);
    let own = pre.is_none().then(|| sys_headers.then(|| preprocessed(c_text, &words, &flags, cxx)).flatten()).flatten();
    let text = pre.or(own.as_deref()).unwrap_or(c_text.as_bytes());
    let (a, b) = crate::driver::cache::hash128(
        &[b"cc-v2", spec.triple.as_bytes(), id.as_bytes(), flags.as_bytes(), &[debug as u8, cxx as u8], profile.unwrap_or("").as_bytes(), text],
        37,
    );
    format!("{a:016x}{b:016x}")
}

/// `unit_key` of an LLVM unit (`compile_pair`): its C half, its IR and its helpers' C as
/// parts, with `extra` (the IR compile's flags, the runtime IR's digest), not copied into one
/// text first (~1 MB a unit, every unit every build). Its C has no `#include`.
fn ll_unit_key(c: &str, ll: &str, hc: &str, extra: &str, spec: &CcSpec, debug: bool, profile: Option<&str>) -> String {
    let flags = cflags(debug);
    let (a, b) = crate::driver::cache::hash128(
        &[
            b"cc-v2 llvm-v5",
            spec.triple.as_bytes(),
            compiler_id(&spec.cmd).as_bytes(),
            flags.as_bytes(),
            &[debug as u8],
            profile.unwrap_or("").as_bytes(),
            extra.as_bytes(),
            c.as_bytes(),
            ll.as_bytes(),
            hc.as_bytes(),
        ],
        37,
    );
    format!("{a:016x}{b:016x}")
}

/// The command that compiles one C (or C++) unit `src` into `obj` (`build` and the streamed
/// build, `stream.rs`, both run it): the compiler words, the flags of every unit, the unit's key
/// for zig's cache, and with PGO the unit's flags, run from its own dir (`pgo::STATIC_FILE`).
fn unit_command(
    words: &[String],
    flags: &[String],
    obj: &Path,
    key: Option<&str>,
    pgo: Option<(Vec<String>, &Path)>,
    src: &Path,
) -> Command {
    // A relative compiler path must not resolve against `work` (PGO compiles there).
    let prog = if words[0].contains('/') {
        std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0]))
    } else {
        PathBuf::from(&words[0])
    };
    let mut cmd = cc_command(prog);
    cmd.args(&words[1..]).args(flags).arg("-o").arg(obj);
    if let Some(k) = key {
        cmd.arg(format!("-DLUST_UNIT_KEY={k}"));
    }
    match pgo {
        Some((pf, dir)) => {
            cmd.args(pf).current_dir(dir).arg("-c").arg(pgo::STATIC_FILE);
        }
        None => {
            cmd.arg("-c").arg(src);
        }
    }
    cmd
}

/// A command that runs the C compiler (or links through it). gcc 7+, clang 16+ and zig cc
/// take `__DATE__` and `__TIME__` from `SOURCE_DATE_EPOCH`, fixed here unless the caller
/// set it: mimalloc's unit prints them, so its object, and its key (the preprocessed text,
/// `unit_key`), changed every second and a release binary with the build time.
fn cc_command(prog: impl AsRef<std::ffi::OsStr>) -> Command {
    let mut cmd = Command::new(prog);
    if std::env::var_os("SOURCE_DATE_EPOCH").is_none() {
        cmd.env("SOURCE_DATE_EPOCH", "0");
    }
    cmd
}

/// `c_text` (C++ text with `cxx`) after the preprocessor of the compiler
/// `words` with `flags`, or None when it cannot run (the key then holds the
/// raw text, and a failed compile reports the real error).
fn preprocessed(c_text: &str, words: &[String], flags: &str, cxx: bool) -> Option<Vec<u8>> {
    preprocessed_into(c_text, words, flags, cxx, None)
}

/// `preprocessed`, and with `deps` the headers it read, as a make rule in that file (`-MD`).
fn preprocessed_into(c_text: &str, words: &[String], flags: &str, cxx: bool, deps: Option<&Path>) -> Option<Vec<u8>> {
    use std::io::Write as _;
    let mut cmd = cc_command(&words[0]);
    cmd.args(&words[1..]).args(flags.split_whitespace()).args(["-E", "-P", "-x", if cxx { "c++" } else { "c" }, "-", "-o", "-"]);
    if let Some(d) = deps {
        cmd.arg("-MD").arg("-MF").arg(d);
    }
    let mut child = cmd.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::null()).spawn().ok()?;
    let mut stdin = child.stdin.take()?;
    let text = c_text.to_string();
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()));
    let out = child.wait_with_output().ok()?;
    writer.join().ok()?.ok()?;
    out.status.success().then_some(out.stdout)
}

/// `preprocessed`, kept in `work` for the next build, one file per unit `name` and command.
/// A release build has 2-3 units with system headers (the runtime, mimalloc, the C++ unit),
/// and their keys read their preprocessed text: ~100-150 ms of `zig cc -E` before the first
/// key, every build. The kept text is used again only when everything it follows from is
/// the same: the -E command (the compiler words with their target, defines and -I order,
/// the flags, the language), the compiler's identity (`compiler_id`: its version line and
/// binary), what -E reads from the environment (`preprocess_env`: the build time __DATE__ and
/// __TIME__ give, header search paths, zig's settings), the text's digest, and the content
/// digest of every header the preprocessor read (its `-MD` list). Headers are compared by
/// content, not by stamps: a restored disk or a checkout can give a changed header an old
/// mtime, and reading the ~100 headers costs about a millisecond. A header that shadows a
/// listed one from an earlier include dir is not seen (as in make); for zig those dirs are
/// zig's own, which the binary's identity covers. A text that uses `__TIMESTAMP__` (its
/// input file's mtime, a temp file under zig) is not kept.
fn preprocessed_kept(work: &Path, name: &str, c_text: &str, words: &[String], flags: &str, cxx: bool) -> Option<Vec<u8>> {
    preprocessed_kept_in(work, name, c_text, words, flags, cxx, &preprocess_env())
}

/// What a preprocessor run reads from the environment, besides its argv: SOURCE_DATE_EPOCH
/// (__DATE__ and __TIME__; `cc_command` sets 0 when it is unset), the header search paths the
/// C drivers take from it, the clang driver's own overrides, and zig's settings (its lib dir,
/// a libc file), not zig's cache dirs, where a run caches, not what it reads.
fn preprocess_env() -> String {
    let mut vars: Vec<(String, String)> = std::env::vars()
        .filter(|(k, _)| {
            matches!(k.as_str(), "CPATH" | "C_INCLUDE_PATH" | "CPLUS_INCLUDE_PATH" | "OBJC_INCLUDE_PATH" | "OBJCPLUS_INCLUDE_PATH" | "SDKROOT" | "COMPILER_PATH" | "GCC_EXEC_PREFIX")
                || k.ends_with("_DEPLOYMENT_TARGET")
                || k.starts_with("CCC_")
                || (k.starts_with("ZIG_") && !matches!(k.as_str(), "ZIG_GLOBAL_CACHE_DIR" | "ZIG_LOCAL_CACHE_DIR") && !k.starts_with("ZIG_VERBOSE"))
        })
        .collect();
    vars.sort();
    let epoch = std::env::var("SOURCE_DATE_EPOCH").unwrap_or_else(|_| "0".into());
    format!("SOURCE_DATE_EPOCH={epoch} {vars:?}")
}

/// `preprocessed_kept` under the environment `env` (`preprocess_env`).
fn preprocessed_kept_in(work: &Path, name: &str, c_text: &str, words: &[String], flags: &str, cxx: bool, env: &str) -> Option<Vec<u8>> {
    if c_text.contains("__TIMESTAMP__") {
        return preprocessed(c_text, words, flags, cxx);
    }
    let hex = |parts: &[&[u8]], seed| {
        let (a, b) = crate::driver::cache::hash128(parts, seed);
        format!("{a:016x}{b:016x}")
    };
    let slot = hex(&[b"pre-v2", name.as_bytes(), words.join(" ").as_bytes(), flags.as_bytes(), &[cxx as u8]], 41);
    let inputs = hex(&[compiler_id(words).as_bytes(), env.as_bytes(), c_text.as_bytes()], 43);
    let (out, deps) = (work.join(format!("pre-{slot}.i")), work.join(format!("pre-{slot}.deps")));
    let header = |p: &str| std::fs::read(p).ok().map(|b| hex(&[&b], 47));
    if let Ok(rec) = std::fs::read_to_string(&deps)
        && let Some((first, headers)) = rec.split_once('\n')
        && first == inputs
        && headers.lines().all(|l| l.split_once('\t').is_some_and(|(d, p)| header(p).as_deref() == Some(d)))
        && let Ok(bytes) = std::fs::read(&out)
    {
        return Some(bytes);
    }
    let rule_file = work.join(format!("pre-{slot}.d.{}", std::process::id()));
    let bytes = preprocessed_into(c_text, words, flags, cxx, Some(&rule_file));
    let rule = std::fs::read_to_string(&rule_file).unwrap_or_default();
    let _ = std::fs::remove_file(&rule_file);
    let bytes = bytes?;
    // The rule's prerequisites: the headers, and the input itself ("<stdin>", or zig's temp
    // copy of stdin), which is not one. A header that cannot be read keeps nothing.
    let mut rec = format!("{inputs}\n");
    for h in rule.split_once(": ").map_or("", |(_, r)| r).replace("\\\n", " ").split_whitespace().filter(|h| !h.contains("stdin")) {
        match header(h) {
            Some(d) => rec.push_str(&format!("{d}\t{h}\n")),
            None => return Some(bytes),
        }
    }
    let tmp = |p: &Path| PathBuf::from(format!("{}.tmp{}", p.display(), std::process::id()));
    if std::fs::write(tmp(&out), &bytes).and_then(|_| std::fs::rename(tmp(&out), &out)).is_ok() {
        let _ = std::fs::write(tmp(&deps), rec).and_then(|_| std::fs::rename(tmp(&deps), &deps));
    }
    Some(bytes)
}

/// The flags of an LLVM unit's own compile (its IR plus its C half's bitcode).
/// `LUST_LL_OPT` replaces the optimization level (default -O2; for measurement).
pub fn llflags(debug: bool) -> String {
    let opt = std::env::var("LUST_LL_OPT").unwrap_or_else(|_| "-O2".into());
    let base = format!("{opt} -w -fexceptions");
    if debug { format!("{base} -g") } else { base }
}

/// Compiles one LLVM backend unit into `obj`: the C unit `src` and the helpers' C `hc` to
/// bitcode with the C flags (no LLVM passes yet), then the IR `ll` with both linked in, so
/// the optimizer sees one module (cgen/ll.rs: the C helpers inline into the LLVM fns). The
/// helpers link as builtin bitcode: only what the IR names, internalized, so the copies
/// left after inlining are dropped instead of compiled. `pgo`: the unit's PGO flags
/// (`pgo::Mode::unit_flags`) for that last step, which then runs inside `src`'s dir on the
/// IR's bare file name, as the profile names the module's static fns by it. `rt_inl`: the
/// runtime's inlinable copy (`compile_runtime_ir`), linked as builtin bitcode too. `nopre`:
/// no PGO pre-inliner (see `build`).
#[allow(clippy::too_many_arguments)]
fn compile_pair(
    spec: &CcSpec,
    cflags: &[String],
    debug: bool,
    src: &Path,
    ll: &str,
    hc: &str,
    obj: &Path,
    pgo: Option<&[String]>,
    rt_inl: Option<&Path>,
    nopre: bool,
    key: Option<&str>,
) -> Result<(), String> {
    let key_def: Vec<String> = key.map(|k| format!("-DLUST_UNIT_KEY={k}")).into_iter().collect();
    let bc = src.with_extension("c.bc");
    let ll_path = src.with_extension("ll");
    let hc_path = src.with_extension("hc.c");
    let hbc = src.with_extension("hc.bc");
    // One C file when the plain C marks its body (`cgen::ll::BODY_MARK`): the helpers' C
    // already declares every type the wrappers name, so the body follows it, one parse of
    // the unit header instead of two. That file links as builtin bitcode too; the IR lists
    // the body's fns (the wrappers and trampolines other units call) in `llvm.used`, which
    // keeps them external.
    let merged = std::fs::read_to_string(src).ok().and_then(|c| c.split_once(crate::cgen::ll::BODY_MARK).map(|(_, body)| body.to_string()));
    let (ll, hc) = match &merged {
        Some(body) => {
            let mut used = String::new();
            let mut names = Vec::new();
            for n in pgo::defined_externs(body) {
                if !ll.contains(&format!("@{n}(")) {
                    used.push_str(&format!("declare void @{n}()\n"));
                }
                names.push(format!("ptr @{n}"));
            }
            if !names.is_empty() {
                used.push_str(&format!("@llvm.used = appending global [{} x ptr] [{}], section \"llvm.metadata\"\n", names.len(), names.join(", ")));
            }
            (format!("{ll}\n{used}"), format!("{hc}\n{body}"))
        }
        None => (ll.to_string(), hc.to_string()),
    };
    std::fs::write(&ll_path, &ll).map_err(|e| format!("cannot write {}: {e}\n", ll_path.display()))?;
    std::fs::write(&hc_path, &hc).map_err(|e| format!("cannot write {}: {e}\n", hc_path.display()))?;
    let run = |cmd: &mut Command| -> Result<(), String> {
        match cmd.output() {
            Ok(o) if o.status.success() => Ok(()),
            Ok(o) => Err(format!("({})\n{}", o.status, String::from_utf8_lossy(&o.stderr))),
            Err(e) => Err(format!("cannot run {}: {e}\n", spec.cmd.join(" "))),
        }
    };
    let words = &spec.cmd;
    // No `noundef` on C values: the C halves pass aggregates' bits as integers
    // (cgen/ll.rs `Pass::Bits`, `Pass::Pair`), which may hold uninitialized bytes.
    let to_bc = |from: &Path, to: &Path| {
        run(cc_command(&words[0])
            .args(&words[1..])
            .args(cflags)
            .args(["-emit-llvm", "-Xclang", "-disable-llvm-passes", "-Xclang", "-no-enable-noundef-analysis", "-c"])
            .args(&key_def)
            .arg(from)
            .arg("-o")
            .arg(to))
    };
    if merged.is_none() {
        to_bc(src, &bc)?;
    }
    to_bc(&hc_path, &hbc)?;
    // A relative compiler path must not resolve against the work dir (PGO compiles there).
    let prog = if words[0].contains('/') { std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0])) } else { PathBuf::from(&words[0]) };
    let mut cmd = cc_command(prog);
    cmd.args(&words[1..]).args(llflags(debug).split_whitespace()).arg("-c");
    if nopre {
        cmd.args(["-mllvm", "-disable-preinline"]);
    }
    match (pgo, ll_path.parent(), ll_path.file_name()) {
        (Some(flags), Some(dir), Some(file)) => cmd.args(flags).current_dir(dir).arg(file),
        _ => cmd.arg(&ll_path),
    };
    let abs = |p: &Path| std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let mut linked: Vec<&Path> = Vec::new();
    if merged.is_none() {
        cmd.args(["-Xclang", "-mlink-bitcode-file", "-Xclang"]).arg(abs(&bc));
        linked.push(&bc);
    }
    cmd.args(["-Xclang", "-mlink-builtin-bitcode", "-Xclang"]).arg(abs(&hbc));
    linked.push(&hbc);
    if let Some(rt) = rt_inl {
        cmd.args(["-Xclang", "-mlink-builtin-bitcode", "-Xclang"]).arg(abs(rt));
        linked.push(rt);
    }
    // zig cc caches a compile by its source (the IR) and its args, not by the bitcode it
    // links through -Xclang: a unit whose IR stays while its C changes (a callee's id, a
    // layout) would get the object of the last build at this path. Their digest goes in
    // the args.
    let mut bytes = Vec::with_capacity(linked.len());
    for p in linked {
        bytes.push(std::fs::read(p).map_err(|e| format!("cannot read {}: {e}\n", p.display()))?);
    }
    let (a, b) = crate::driver::cache::hash128(&bytes.iter().map(Vec::as_slice).collect::<Vec<_>>(), 53);
    cmd.arg(format!("-DLUST_LINKED_DIGEST={a:016x}{b:016x}")).args(&key_def);
    run(cmd.arg("-o").arg(obj))
}

/// Compiles the runtime unit `src` through LLVM IR (`rtinl.rs`): the C to IR with the full
/// pipeline (and the unit's profile: `pgo`, then inside `src`'s dir), `rtinl::split`, its
/// object `obj` from the IR with every internal symbol exported (no IR passes again), and
/// `inl`, the bitcode of the copy the LLVM units inline from (fns of at most `max`
/// instructions).
fn compile_runtime_ir(spec: &CcSpec, cflags: &[String], src: &Path, obj: &Path, inl: &Path, max: usize, pgo: Option<&[String]>, key: Option<&str>) -> Result<(), String> {
    let words = &spec.cmd;
    let prog = if words[0].contains('/') { std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0])) } else { PathBuf::from(&words[0]) };
    let run = |extra: &[&str], input: &Path, out: &Path, pgo: Option<&[String]>| -> Result<(), String> {
        let mut cmd = Command::new(&prog);
        cmd.args(&words[1..]).args(cflags).args(extra).args(key.map(|k| format!("-DLUST_UNIT_KEY={k}")));
        match (pgo, input.parent(), input.file_name()) {
            (Some(flags), Some(dir), Some(file)) => cmd.args(flags).current_dir(dir).arg(file),
            _ => cmd.arg(input),
        };
        match cmd.arg("-o").arg(out).output() {
            Ok(o) if o.status.success() => Ok(()),
            Ok(o) => Err(format!("({})\n{}", o.status, String::from_utf8_lossy(&o.stderr))),
            Err(e) => Err(format!("cannot run {}: {e}\n", words.join(" "))),
        }
    };
    let (ir, obj_ll, inl_ll) = (src.with_extension("rt.ll"), src.with_extension("obj.ll"), src.with_extension("inl.ll"));
    let ir = std::fs::canonicalize(src.parent().unwrap_or(Path::new("."))).map(|d| d.join(ir.file_name().unwrap_or_default())).unwrap_or(ir);
    run(&["-S", "-emit-llvm"], src, &ir, pgo)?;
    let text = std::fs::read_to_string(&ir).map_err(|e| format!("cannot read {}: {e}\n", ir.display()))?;
    let parts = rtinl::split(&text, max);
    std::fs::write(&obj_ll, parts.obj).map_err(|e| format!("cannot write {}: {e}\n", obj_ll.display()))?;
    std::fs::write(&inl_ll, parts.inl).map_err(|e| format!("cannot write {}: {e}\n", inl_ll.display()))?;
    run(&["-Xclang", "-disable-llvm-passes", "-c"], &obj_ll, obj, None)?;
    run(&["-emit-llvm", "-Xclang", "-disable-llvm-passes", "-c"], &inl_ll, inl, None)
}

/// What the PGO split (`pgo::defined_externs`, `pgo::defined_statics`, `pgo::stable_name`)
/// reads for an LLVM unit: its C half, then a C definition line for each external fn its IR
/// defines (its own and the `available_externally` copies, whose bodies the profile annotates
/// too), and a static one for each fn that ends up internal in the unit's module: the IR's
/// internal fns, the helpers it calls, and the static fns of its helpers' C `hc`.
fn ll_profile_text(c: &str, ll: &str, hc: &str) -> String {
    let mut out = c.to_string();
    let name = |line: &str| line.find(" @").and_then(|at| line[at + 2..].find('(').map(|len| line[at + 2..at + 2 + len].to_string()));
    for line in ll.lines() {
        let local = line.starts_with("define internal ") || line.starts_with("define private ");
        if let Some(n) = line.starts_with("define ").then(|| name(line)).flatten() {
            out.push_str(&format!("\n{}void {n}(void) {{\n}}\n", if local { "static " } else { "" }));
        } else if line.starts_with("declare ")
            && let Some(n) = name(line).filter(|n| n.starts_with("lh_"))
        {
            // A helper the IR calls: its C (in `hc`) links into the module as an internal fn.
            out.push_str(&format!("\nstatic void {n}(void) {{\n}}\n"));
        }
    }
    for n in pgo::defined_statics(hc) {
        out.push_str(&format!("\nstatic void {n}(void) {{\n}}\n"));
    }
    out
}

/// What a unit key holds besides the unit's text (`unit_key`, `llflags`, the profile): a
/// unit memo (`memo.rs`) written under another tag is dropped as a whole.
fn memo_tag(spec: &CcSpec, debug: bool, work: &Path) -> String {
    let profile = std::env::var_os("LUST_PGO_USE").map(|p| pgo::profile_digest(Path::new(&p), work).unwrap_or_default()).unwrap_or_default();
    let pgo_env: Vec<String> = ["LUST_PGO_BITS", "LUST_PGO_PREINLINE", "LUST_PGO_CGPROFILE", "LUST_PROFDATA"].iter().map(|v| std::env::var(v).unwrap_or_default()).collect();
    let (a, b) = crate::driver::cache::hash128(
        &[
            env!("LUST_BUILD_HASH").as_bytes(),
            spec.triple.as_bytes(),
            compiler_id(&spec.cmd).as_bytes(),
            cflags(debug).as_bytes(),
            llflags(debug).as_bytes(),
            pgo_env.join(" ").as_bytes(),
            profile.as_bytes(),
        ],
        59,
    );
    format!("memo-v2 {a:016x}{b:016x}")
}

/// The memo entry of a unit's fingerprint (`memo_state` and `build` both ask it). It serves
/// the fingerprint under any unit name: release unit names are positions, and a unit inserted
/// before others renames them all.
fn memo_entry<'a>(memo: &'a std::collections::HashMap<u128, memo::Entry>, u: &UnitIn) -> Option<&'a memo::Entry> {
    u.fp.and_then(|fp| memo.get(&fp))
}

/// The memo state of a build (`build`, `memo_misses`): the memo's tag when the units carry
/// fingerprints, its entries, and the names of the units passed without text that `build`
/// cannot take, sorted: no memo entry for its fingerprint (`memo_entry`), or its object left
/// the cache (an LLVM unit's three parts come with text or without as one). Reads the memo
/// file and stats the cache's objects only.
fn memo_state(
    units: &[UnitIn],
    spec: &CcSpec,
    debug: bool,
    cache: Option<&crate::driver::cache::Cache>,
    work: &Path,
) -> (Option<String>, std::collections::HashMap<u128, memo::Entry>, Vec<String>) {
    // The memo (`memo.rs`), for a build given fingerprints. Not with runtime IR
    // (`LUST_LL_RTINL`): LLVM unit keys hold its digest, known only after it compiles.
    let rt_max: usize = std::env::var("LUST_LL_RTINL").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let instrumented = std::env::var_os("LUST_PGO_GEN").is_some_and(|v| v == "1");
    let tag = (units.iter().any(|u| u.fp.is_some()) && rt_max == 0 && !instrumented).then(|| memo_tag(spec, debug, work));
    let memo = tag.as_deref().map(|t| memo::load(work, t)).unwrap_or_default();
    let entry_of = |u: &UnitIn| memo_entry(&memo, u);
    // A unit without text: its memo entry, with the object in the cache. An LLVM unit's
    // parts come as one (its key covers the three texts): with text, or all without.
    let mut parts: std::collections::HashMap<&str, Vec<&UnitIn>> = std::collections::HashMap::new();
    for u in units {
        parts.entry(u.name.strip_suffix(".ll").or_else(|| u.name.strip_suffix(".hc")).unwrap_or(&u.name)).or_default().push(u);
    }
    let mut need: Vec<String> = Vec::new();
    for (whole, ps) in &parts {
        let bare = ps.iter().filter(|p| p.text.is_none()).count();
        let known = || {
            ps.iter().find(|p| p.name == *whole).and_then(|c| entry_of(c)).is_some_and(|e| cache.is_some_and(|k| k.has_unit_object(&e.key)))
        };
        if bare > 0 && (bare < ps.len() || !known()) {
            need.extend(ps.iter().filter(|p| p.text.is_none()).map(|p| p.name.clone()));
        }
    }
    need.sort();
    (tag, memo, need)
}

/// The units passed without text that `build` would send back with `CcError::NeedText`
/// for these same inputs (one rule: `build` asks `memo_state` too). A caller that cannot
/// answer `NeedText` later (a release cc step parked after the save fork) assembles these
/// first. Another process can still evict an object in between: `build` then answers
/// `NeedText`, which that caller treats as a failed build.
pub fn memo_misses(units: &[UnitIn], spec: &CcSpec, debug: bool, cache: Option<&crate::driver::cache::Cache>, work: &Path) -> Vec<String> {
    memo_state(units, spec, debug, cache, work).2
}

/// Compiles every unit and links `out`. `units` are in link order (a name ending in `.cc`
/// is C++ text, for `spec.cxx`; `u<N>.ll` and `u<N>.hc` are the IR and helpers' C of the
/// LLVM unit `u<N>`); `work` is a scratch dir for C files and objects the caller owns, and
/// holds the unit memo (`memo.rs`) for the next build. A unit without text needs its
/// fingerprint in the memo and its object in the cache, else `CcError::NeedText` names the
/// units to pass again with text (an LLVM unit's three parts come with text or without as
/// one). Returns a one-line summary, or the compiler's error text.
pub fn build(units: &[UnitIn], spec: &CcSpec, out: &Path, debug: bool, cache: Option<&crate::driver::cache::Cache>, work: &Path) -> Result<String, CcError> {
    build_with(units, spec, out, debug, cache, work, None)
}

/// `build`, with the units a `Stream` took while they assembled: for each, the stream's key,
/// and its object once its compile exited (it is not compiled again).
pub fn build_with(
    units: &[UnitIn],
    spec: &CcSpec,
    out: &Path,
    debug: bool,
    cache: Option<&crate::driver::cache::Cache>,
    work: &Path,
    stream: Option<Stream>,
) -> Result<String, CcError> {
    // The streamed units compile on from here, `jobs` at once, while this prepares the rest.
    if let Some(s) = &stream {
        s.go();
    }
    std::fs::create_dir_all(work).map_err(|e| format!("cannot create {}: {e}", work.display()))?;
    let flags: Vec<String> = cflags(debug).split_whitespace().map(str::to_string).collect();
    let cxx_flags: Vec<String> = cxxflags(debug).split_whitespace().map(str::to_string).collect();
    let is_cxx = |name: &str| name.ends_with(".cc");
    let rt_max: usize = std::env::var("LUST_LL_RTINL").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let instrumented = std::env::var_os("LUST_PGO_GEN").is_some_and(|v| v == "1");
    let (tag, memo, need) = memo_state(units, spec, debug, cache, work);
    if !need.is_empty() {
        return Err(CcError::NeedText(need));
    }
    let entry_of = |u: &UnitIn| memo_entry(&memo, u);
    // The LLVM backend (cgen/ll.rs): a unit `u<N>.ll` is the LLVM IR of the C unit `u<N>`, and
    // `u<N>.hc` the C of its helpers; the three compile as one module into `u<N>.o`
    // (`compile_pair`) and key on all three texts. For PGO such a unit is `<name>.ll`: the
    // profile names the combined module's static fns by the IR's file name.
    let ll_of: std::collections::HashMap<&str, &str> =
        units.iter().filter_map(|u| Some((u.name.strip_suffix(".ll")?, u.text.as_deref()?))).collect();
    let hc_of: std::collections::HashMap<&str, &str> =
        units.iter().filter_map(|u| Some((u.name.strip_suffix(".hc")?, u.text.as_deref()?))).collect();
    let textless_parts: std::collections::HashSet<&str> =
        units.iter().filter(|u| u.text.is_none() && (u.name.ends_with(".ll") || u.name.ends_with(".hc"))).map(|u| u.name.as_str()).collect();
    let units: Vec<&UnitIn> = units.iter().filter(|u| !u.name.ends_with(".ll") && !u.name.ends_with(".hc")).collect();
    // A unit without text is a memo entry; `text` is empty for it.
    let entries: Vec<Option<&memo::Entry>> = units.iter().map(|u| u.text.is_none().then(|| entry_of(u)).flatten()).collect();
    let text = |i: usize| units[i].text.as_deref().unwrap_or("");
    // PGO (`pgo.rs`): the C units compile from inside `work` under content-derived
    // names, as the profile names their static functions by file, and each key holds
    // that unit's own part of the profile. The C++ unit is not profiled.
    let pgo_on = std::env::var_os("LUST_PGO_GEN").is_some() || std::env::var_os("LUST_PGO_USE").is_some();
    let work = &if pgo_on { std::fs::canonicalize(work).map_err(|e| format!("cannot resolve {}: {e}", work.display()))? } else { work.to_path_buf() };
    // Per unit, on every thread (a warm build reads every unit's text here, ~1 GB for tsgo):
    // the text the PGO split reads (an LLVM unit's C half plus its IR's definitions), the
    // unit's file name, and the preprocessed text of a C unit with `#include`s, which its key
    // and its PGO definitions both read.
    let idx: Vec<usize> = (0..units.len()).collect();
    let ll_texts: Vec<Option<String>> =
        crate::pool::par_map(&idx, |&i| {
            let name = units[i].name.as_str();
            ll_of.get(name).filter(|_| pgo_on).map(|ll| ll_profile_text(text(i), ll, hc_of.get(name).copied().unwrap_or("")))
        });
    let oracle = std::env::var_os("LUST_CHECK_UNIT_FP").is_some_and(|v| v == "1");
    // The units the stream took: their key and the file name they compile as (it compiles them).
    let took: Vec<Option<(String, String)>> = units.iter().map(|u| stream.as_ref().and_then(|s| s.key_and_file(&u.name))).collect();
    // What each C or LLVM unit given text defines (`pgo::definitions_of`), one scan: its PGO
    // file name and the split read it. A unit the stream took is not compiled here, so it is
    // scanned only for the oracle's own key.
    let scans: Vec<Option<pgo::Defs>> = crate::pool::par_map(&idx, |&i| {
        (pgo_on && entries[i].is_none() && !is_cxx(&units[i].name) && (took[i].is_none() || oracle))
            .then(|| pgo::definitions_of(ll_texts[i].as_deref().unwrap_or(text(i))))
    });
    let names: Vec<String> = crate::pool::par_map(&idx, |&i| match (entries[i], &took[i], &scans[i]) {
        // A PGO name is its text's (`pgo::stable_name`, as the stream names it); else the
        // unit's name now: its object goes there, whatever name the entry had in the last build.
        (Some(e), _, _) if pgo_on => e.file.rsplit_once('.').map_or(e.file.clone(), |(stem, _)| stem.to_string()),
        (None, Some((_, file)), _) => file.clone(),
        (None, None, Some(d)) => pgo::stable_name(&d.0).unwrap_or_else(|| units[i].name.clone()),
        _ => units[i].name.clone(),
    });
    // The text a unit with system headers keys on (`unit_key`), kept for the next build
    // (`preprocessed_kept`); the C++ unit's with its own driver and flags, as `unit_key` makes it.
    let (cflags_text, cxxflags_text) = (cflags(debug), cxxflags(debug));
    let pre: Vec<Option<Vec<u8>>> = crate::pool::par_map(&idx, |&i| {
        let (name, cxx) = (&units[i].name, is_cxx(&units[i].name));
        let (words, flags) = if cxx { (&spec.cxx, &cxxflags_text) } else { (&spec.cmd, &cflags_text) };
        text(i).contains("#include <").then(|| preprocessed_kept(work, name, text(i), words, flags, cxx)).flatten()
    });
    // The LLVM units by their PGO names (`ll_of` and `hc_of` stay by unit name).
    let is_ll: Vec<bool> = (0..units.len()).map(|i| entries[i].map_or(ll_of.contains_key(units[i].name.as_str()), |e| e.file.ends_with(".ll"))).collect();
    let pfile = |i: usize| if is_ll[i] { format!("{}.ll", names[i]) } else { format!("{}.c", names[i]) };
    // What each unit scanned defines, for a profile to use. Memo units and those the stream
    // took are not compiled here (their keys are kept), and a unit's records follow from its
    // own definitions alone (`pgo::split`), so they are not split.
    let defs = std::env::var_os("LUST_PGO_USE").filter(|_| !instrumented).map(|_| {
        let files: Vec<(String, &pgo::Defs, Option<&[u8]>)> = (0..units.len()).filter_map(|i| Some((pfile(i), scans[i].as_ref()?, pre[i].as_deref()))).collect();
        pgo::unit_defs(&files, (0..units.len()).all(|i| scans[i].is_some() || is_cxx(&units[i].name)))
    });
    let pgo = pgo::Mode::from_env(spec, work, defs.as_ref(), stream.as_ref().and_then(Stream::warm))?;
    let pgo_of = |i: usize| pgo.as_ref().filter(|_| !is_cxx(&names[i]));
    // A C unit of glue (`pgo::fnless`: no program fn, no system header) compiles the fns its
    // profile calls cold with no optimization (`pgo::use_flags`).
    let fnless = |i: usize| !is_ll[i] && pre[i].is_none() && scans[i].as_ref().is_some_and(pgo::fnless);
    // An instrumented build needs a compiler with a profile runtime (`pgo::gen_spec`).
    let gen_spec = if matches!(pgo, Some(pgo::Mode::Gen)) { Some(pgo::gen_spec(spec)?) } else { None };
    let spec = gen_spec.as_ref().unwrap_or(spec);
    let pre_of = |i: usize| if gen_spec.is_some() { None } else { pre[i].as_deref() };
    // zig cc caches each compile by its source and args, which miss inputs lust's key holds
    // (the bitcode an LLVM unit links, a profile, the environment a preprocessed text shows):
    // every unit compile carries its exact key (`-DLUST_UNIT_KEY`), so zig can only hit where
    // lust's key matches. Keys are made for zig builds without a lust cache too.
    let keyed = cache.is_some() || is_zig(&spec.cmd[0]);
    // Largest units first, bounded workers: the tcc driver's shape
    // (src/tcc.rs), for the same reason (the tail is short units).
    let mut order: Vec<usize> = (0..units.len()).collect();
    let len = |i: usize| entries[i].map_or(text(i).len() + ll_of.get(units[i].name.as_str()).map_or(0, |l| l.len()), |e| e.len);
    order.sort_by_key(|&i| std::cmp::Reverse(len(i)));
    let objs: Vec<PathBuf> = names.iter().map(|name| work.join(format!("{name}.o"))).collect();
    let hits = std::sync::atomic::AtomicUsize::new(0);
    // `LUST_LL_RTINL=<max instructions>` (0 or unset: off): with LLVM units, the runtime unit
    // compiles through IR first (`compile_runtime_ir`) and every LLVM unit links the
    // runtime's fns of at most that size as inlinable IR (not in an instrumented build,
    // whose counters must stay the runtime's). LLVM unit keys hold that copy's digest.
    // Off by default: a PGO build lost half its fns' profile with it (the training build has
    // no runtime IR, and the PGO pre-inliner inlines runtime fns before it hashes CFGs).
    let rt = (rt_max > 0 && !ll_of.is_empty() && !matches!(pgo, Some(pgo::Mode::Gen)))
        .then(|| (0..units.len()).position(|i| text(i).starts_with("#define LUST_IMPL 1\n")))
        .flatten();
    let rt_inl = work.join("runtime.inl.bc");
    // PGO with runtime IR: the training build has none (an instrumented runtime cannot be
    // copied), so LLVM's PGO pre-inliner, which inlines small callees before it hashes each
    // fn's CFG, would inline runtime fns in the use build only and the hashes would differ
    // (half the fns lost their profile). Both builds skip the pre-inliner then.
    // (`pgo::no_preinline` puts the flag in every PGO compile already.)
    let nopre = rt_max > 0 && pgo.is_some() && !pgo::no_preinline();
    let rt_digest = match rt {
        Some(r) => {
            let part = pgo_of(r).map(|m| m.key_part(&pfile(r), fnless(r)));
            // The marker is a declaration: the key reads the preprocessed text, without comments.
            let key = keyed.then(|| unit_key(&format!("{}\ntypedef int lust_rtinl_{rt_max};\n", text(r)), None, spec, debug, part.as_deref(), false));
            let cached = matches!((cache, &key), (Some(c), Some(k)) if c.unit_object(k, &objs[r]) && c.unit_object(&format!("{k}-inl"), &rt_inl));
            if cached {
                hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            } else {
                let src = match pgo_of(r) {
                    Some(_) => {
                        let d = work.join(format!("{}.d", names[r]));
                        std::fs::create_dir_all(&d).map_err(|e| format!("cannot create {}: {e}", d.display()))?;
                        d.join(pgo::STATIC_FILE)
                    }
                    None => work.join(format!("{}.c", names[r])),
                };
                std::fs::write(&src, text(r)).map_err(|e| format!("cannot write {}: {e}", src.display()))?;
                let pf = pgo_of(r).map(|m| m.unit_flags(&pfile(r), fnless(r))).transpose()?;
                compile_runtime_ir(spec, &flags, &src, &objs[r], &rt_inl, rt_max, pf.as_deref(), key.as_deref())
                    .map_err(|e| format!("the C compiler failed for target {} (runtime IR):\n{e}", spec.triple))?;
                pgo_of(r).map_or(Ok(()), |m| m.after_compile(&objs[r]))?;
                if let (Some(c), Some(k)) = (cache, &key) {
                    c.store_unit_object(k, &objs[r]);
                    c.store_unit_object(&format!("{k}-inl"), &rt_inl);
                }
            }
            let bytes = std::fs::read(&rt_inl).map_err(|e| format!("cannot read {}: {e}", rt_inl.display()))?;
            let (a, b) = crate::driver::cache::hash128(&[&bytes], 47);
            format!("{a:016x}{b:016x}")
        }
        None => String::new(),
    };
    let keys: Vec<Option<String>> = crate::pool::par_map(&idx, |&i| {
        if let Some(e) = entries[i] {
            return Some(e.key.clone());
        }
        let (unit, c) = (&units[i].name, text(i));
        let mine = || {
            let part = pgo_of(i).map(|m| m.key_part(&pfile(i), fnless(i)));
            keyed.then(|| match ll_of.get(unit.as_str()) {
                Some(ll) => {
                    let hc = hc_of.get(unit.as_str()).copied().unwrap_or("");
                    ll_unit_key(c, ll, hc, &format!("{} {nopre} rtinl {rt_digest}", llflags(debug)), spec, debug, part.as_deref())
                }
                None => unit_key(c, pre_of(i), spec, debug, part.as_deref(), is_cxx(&names[i])),
            })
        };
        // A streamed unit has the stream's key: the same inputs. The oracle checks it.
        match took[i].as_ref().filter(|_| keyed) {
            Some((k, _)) => {
                if oracle && mine().as_deref() != Some(k.as_str()) {
                    panic!("LUST_CHECK_UNIT_FP: the stream keyed unit {unit} {k}, build {:?}", mine());
                }
                Some(k.clone())
            }
            None => mine(),
        }
    });
    // The memo for the next build: this build's units with a fingerprint (not those whose
    // key reads a preprocessed text, so a header change is seen, nor the C++ unit). With
    // LUST_CHECK_UNIT_FP=1 every unit comes with text, and a fingerprint the last build gave
    // another key is a stale fingerprint: the session missed an input. A thread writes it
    // while the units compile (joined before the link; the write is atomic, so a build that
    // fails first keeps the last memo).
    let memo_saved = if let (Some(tag), true) = (&tag, keyed) {
        let mut next = Vec::new();
        for i in 0..units.len() {
            let (Some(fp), Some(key)) = (units[i].fp, &keys[i]) else { continue };
            if pre[i].is_some() || is_cxx(&units[i].name) || text(i).contains("#include <") {
                continue;
            }
            if oracle && let Some(old) = memo.get(&fp).filter(|e| &e.key != key) {
                panic!("LUST_CHECK_UNIT_FP: unit {} has the input fingerprint {fp:032x} of the last build, whose text had key {}; its text now has key {key}", units[i].name, old.key);
            }
            // A memo unit's key, file and length are its entry's (`keys`, `names`, `len`).
            next.push((fp, memo::Entry { name: units[i].name.clone(), key: key.clone(), file: pfile(i), len: len(i) }));
        }
        let (work, tag) = (work.to_path_buf(), tag.clone());
        Some(std::thread::spawn(move || memo::save(&work, &tag, &next)))
    } else {
        None
    };
    // While the misses compile, read the objects the cache holds for this build, 16 at once, so
    // the link finds them in the page cache: lld page-faults its inputs in with few reads in
    // flight, slow from a cold page cache (a CI job's freshly mounted disk). The link waits for
    // it. LUST_LINK_PREFETCH=0 turns it off.
    let prefetch = cache.filter(|_| std::env::var_os("LUST_LINK_PREFETCH").is_none_or(|v| v != "0")).map(|c| {
        let paths: Vec<PathBuf> = keys.iter().flatten().map(|k| c.unit_object_path(k)).collect();
        std::thread::spawn(move || {
            let t = std::time::Instant::now();
            let at = std::sync::atomic::AtomicUsize::new(0);
            std::thread::scope(|s| {
                for _ in 0..16 {
                    s.spawn(|| {
                        while let Some(p) = paths.get(at.fetch_add(1, std::sync::atomic::Ordering::Relaxed)) {
                            if let Ok(mut f) = std::fs::File::open(p) {
                                let _ = std::io::copy(&mut f, &mut std::io::sink());
                            }
                        }
                    });
                }
            });
            t.elapsed().as_secs_f64()
        })
    });
    let next = std::sync::atomic::AtomicUsize::new(0);
    let errors = std::sync::Mutex::new(String::new());
    // Memo units whose object left the cache since the check above (another build evicted it).
    let lost = std::sync::Mutex::new(Vec::new());
    let limit = crate::pool::threads().max(1).min(units.len().max(1));
    let t_compile = std::time::Instant::now();
    std::thread::scope(|scope| {
        for _ in 0..limit {
            scope.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(&i) = order.get(k) else { return };
                if Some(i) == rt {
                    continue;
                }
                let (name, c) = (&names[i], text(i));
                let obj = &objs[i];
                if let Some(done) = stream.as_ref().and_then(|s| s.finish(&units[i].name)) {
                    match done {
                        // Linked again here, so this build's cache notes it as used.
                        Ok(true) => {
                            if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                                cache.unit_object(key, obj);
                            }
                            hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                        Ok(false) => match pgo_of(i).map_or(Ok(()), |m| m.after_compile(obj)) {
                            Ok(()) => {
                                if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                                    cache.store_unit_object(key, obj);
                                }
                            }
                            Err(e) => errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&format!("--- unit {name}: {e}\n")),
                        },
                        Err(e) => errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&e),
                    }
                    continue;
                }
                if let (Some(cache), Some(key)) = (cache, &keys[i])
                    && cache.unit_object(key, obj)
                {
                    hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    continue;
                }
                if entries[i].is_some() {
                    lost.lock().unwrap_or_else(|e| e.into_inner()).push(units[i].name.clone());
                    continue;
                }
                // The object may be a hard link to a cache entry (`Cache::unit_object`);
                // a compiler that wrote its output in place would change the entry.
                let _ = std::fs::remove_file(obj);
                let cxx = is_cxx(name);
                // PGO: a C unit compiles as `<unit>.d/lust.c`, so its static fns' records do not
                // carry the unit's name (`pgo::STATIC_FILE`).
                let pgo_dir = (!cxx && pgo_of(i).is_some() && !ll_of.contains_key(units[i].name.as_str())).then(|| work.join(format!("{name}.d")));
                if let Some(d) = &pgo_dir
                    && let Err(e) = std::fs::create_dir_all(d)
                {
                    errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&format!("cannot create {}: {e}\n", d.display()));
                    continue;
                }
                let src = match &pgo_dir {
                    Some(d) => d.join(pgo::STATIC_FILE),
                    None if cxx => work.join(name),
                    None => work.join(format!("{name}.c")),
                };
                let fail = |msg: String| errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&msg);
                if let Err(e) = std::fs::write(&src, c) {
                    fail(format!("cannot write {}: {e}\n", src.display()));
                    continue;
                }
                if let Some(ll) = ll_of.get(units[i].name.as_str()) {
                    let pf = match pgo_of(i).map(|m| m.unit_flags(&pfile(i), fnless(i))).transpose() {
                        Ok(pf) => pf,
                        Err(e) => {
                            fail(format!("--- unit {name}: {e}\n"));
                            continue;
                        }
                    };
                    match compile_pair(spec, &flags, debug, &src, ll, hc_of.get(units[i].name.as_str()).copied().unwrap_or(""), obj, pf.as_deref(), rt.map(|_| rt_inl.as_path()), nopre, keys[i].as_deref())
                        .and_then(|()| pgo_of(i).map_or(Ok(()), |m| m.after_compile(obj)))
                    {
                        Ok(()) => {
                            if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                                cache.store_unit_object(key, obj);
                            }
                        }
                        Err(e) => fail(format!("--- unit {name} (LLVM)\n{e}")),
                    }
                    continue;
                }
                let (words, unit_flags) = if cxx {
                    (spec.cxx.as_slice().into(), &cxx_flags)
                } else {
                    (unit_words(spec, debug, pre_of(i).is_some() || c.contains("#include <")), &flags)
                };
                let pf = match pgo_of(i).map(|m| m.unit_flags(&pfile(i), fnless(i))) {
                    Some(Ok(pf)) => Some((pf, pgo_dir.as_deref().unwrap_or(work))),
                    Some(Err(e)) => {
                        fail(format!("--- unit {name}: {e}\n"));
                        continue;
                    }
                    None => None,
                };
                let mut cmd = unit_command(&words, unit_flags, obj, keys[i].as_deref(), pf, &src);
                match cmd.output() {
                    Ok(o) if o.status.success() => {
                        if let Err(e) = pgo_of(i).map_or(Ok(()), |m| m.after_compile(obj)) {
                            fail(format!("--- unit {name}: {e}\n"));
                        } else if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                            cache.store_unit_object(key, obj);
                        }
                    }
                    Ok(o) => {
                        let mut msg = format!("--- unit {name} ({})\n", o.status);
                        msg.push_str(&String::from_utf8_lossy(&o.stderr));
                        fail(msg);
                    }
                    Err(e) => fail(format!("cannot run {}: {e}\n", words.join(" "))),
                }
            });
        }
    });
    // One size-cap eviction after the stores (it keeps this build's objects). It stats every
    // file in the cache dir (~6000 in a warm tsgo chain, more on a long-lived CI disk), so it
    // runs beside the link: the link reads only the work dir's links, and the eviction removes
    // only cache files this build did not use. The scope joins it.
    std::thread::scope(|scope| {
        if let Some(c) = cache {
            scope.spawn(move || c.evict_objects());
        }
        let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
        if !errors.is_empty() {
            return Err(CcError::Failed(format!("the C compiler failed for target {}:\n{errors}", spec.triple)));
        }
        let mut lost = lost.into_inner().unwrap_or_else(|e| e.into_inner());
        if !lost.is_empty() {
            let ll: Vec<String> = lost.iter().flat_map(|n| [format!("{n}.ll"), format!("{n}.hc")]).filter(|p| textless_parts.contains(p.as_str())).collect();
            lost.extend(ll);
            lost.sort();
            return Err(CcError::NeedText(lost));
        }
        if let Some(saving) = memo_saved {
            saving.join().map_err(|_| "the unit memo's writer panicked".to_string())??;
        }
        let compile_s = t_compile.elapsed().as_secs_f64();
        let prefetch_s = prefetch.map(|h| h.join().unwrap_or(0.0));
        let t_link = std::time::Instant::now();
        // A build with a C++ unit links with the C++ driver (its runtime and personality).
        let link = if units.iter().any(|u| is_cxx(&u.name)) { &spec.cxx } else { &spec.cmd };
        let mut cmd = cc_command(&link[0]);
        cmd.args(&link[1..]).args(ldflags(spec, debug)).args(pgo.as_ref().map(pgo::Mode::link_flags).unwrap_or_default()).args(&objs).arg("-o").arg(out);
        match cmd.output() {
            Ok(o) if o.status.success() => Ok(format!(
                "{} units ({} from cache, clang {:.2}s, {}link {:.2}s{}), linked {}",
                units.len(),
                hits.load(std::sync::atomic::Ordering::Relaxed),
                compile_s,
                prefetch_s.map(|p| format!("prefetch {p:.2}s, ")).unwrap_or_default(),
                t_link.elapsed().as_secs_f64(),
                pgo.as_ref().map(|m| format!(", {}", m.describe())).unwrap_or_default(),
                out.display()
            )),
            Ok(o) => Err(CcError::Failed(format!("link failed for target {} ({})\n{}", spec.triple, o.status, String::from_utf8_lossy(&o.stderr)))),
            Err(e) => Err(CcError::Failed(format!("cannot run {}: {e}", link.join(" ")))),
        }
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn an_llvm_unit_owns_the_records_of_its_ir_fns_and_copies() {
        let c = "void f_aa(void) {\n}\n";
        let ll = "define void @fl_aa(ptr %p) uwtable {\nentry:\n  ret void\n}\ndefine available_externally i64 @fl_bb() {\nentry:\n  ret i64 0\n}\ndefine internal void @k() {\nentry:\n  ret void\n}\n";
        let text = super::ll_profile_text(c, ll, "");
        assert_eq!(super::pgo::defined_externs(&text), vec!["f_aa", "fl_aa", "fl_bb"]);
    }

    /// A unit passed without text links the object its fingerprint's text made in the last
    /// build in the work dir; an unknown fingerprint, or an object the cache lost since,
    /// asks for the text.
    #[test]
    fn a_unit_without_text_links_the_last_builds_object() {
        use super::{CcError, UnitIn};
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let root = std::env::temp_dir().join(format!("lust-cc-memo-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let cache = crate::driver::cache::Cache::at(&root.join("cache"));
        let (work, bin) = (root.join("work"), root.join("bin"));
        let main = |ret: u32| Some(format!("int f(void);\nint main(void) {{\n  return f() + {ret};\n}}\n"));
        let f = Some("int f(void) {\n  return 3;\n}\n".to_string());
        let unit = |name: &str, fp: u128, text: Option<String>| UnitIn { name: name.into(), fp: Some(fp), text };
        let run = |units: &[UnitIn]| super::build(units, &spec, &bin, false, Some(&cache), &work);
        run(&[unit("u0", 1, main(1)), unit("u1", 7, f.clone())]).unwrap();
        let r = run(&[unit("u0", 2, main(2)), unit("u1", 7, None)]).unwrap();
        assert!(r.contains("2 units (1 from cache"), "u1 comes from its memo entry and the cache: {r}");
        match run(&[unit("u0", 2, None), unit("u1", 8, None)]) {
            Err(CcError::NeedText(n)) => assert_eq!(n, ["u1"], "an unknown fingerprint needs its text"),
            r => panic!("{r:?}"),
        }
        for e in std::fs::read_dir(root.join("cache")).unwrap().flatten() {
            let _ = std::fs::remove_file(e.path());
        }
        match run(&[unit("u0", 2, None), unit("u1", 7, None)]) {
            Err(CcError::NeedText(n)) => assert_eq!(n, ["u0", "u1"], "a memo entry whose object left the cache needs its text"),
            r => panic!("{r:?}"),
        }
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A streamed build (`Stream`) links the binary a plain build links: a unit handed to the
    /// stream before `build_with` compiles once (or comes from the cache) and is not compiled
    /// again, and the binary is byte-identical.
    #[test]
    fn a_streamed_build_links_what_build_links() {
        use super::UnitIn;
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let root = std::env::temp_dir().join(format!("lust-cc-stream-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let main = "int f(void);\nint g(void);\nint main(void) {\n  return f() + g();\n}\n";
        let (f, g) = ("int f(void) {\n  return 3;\n}\n", "int g(void) {\n  return 4;\n}\n");
        let units = || vec![UnitIn::text("u0", main.into()), UnitIn::text("u1", f.into()), UnitIn::text("u2", g.into())];
        let plain = crate::driver::cache::Cache::at(&root.join("c1"));
        super::build(&units(), &spec, &root.join("a"), false, Some(&plain), &root.join("w1")).unwrap();
        // The stream's cache already holds g's object (a build of another main and g): u2 is a
        // hit, u1 a miss the stream compiles, u0 a miss build compiles.
        let streamed = crate::driver::cache::Cache::at(&root.join("c2"));
        let only_g = "int g(void);\nint main(void) {\n  return g();\n}\n";
        super::build(&[UnitIn::text("u0", only_g.into()), UnitIn::text("u2", g.into())], &spec, &root.join("x"), false, Some(&streamed), &root.join("w0")).unwrap();
        let Some(stream) = super::Stream::start(&spec.triple, false, Some(crate::driver::cache::Cache::at(&root.join("c2"))), root.join("w2")) else { return };
        stream.add("u1", f);
        stream.add("u2", g);
        let r = super::build_with(&units(), &spec, &root.join("b"), false, Some(&streamed), &root.join("w2"), Some(stream)).unwrap();
        assert!(r.contains("3 units (1 from cache"), "u2 hit, u1 compiled by the stream, u0 by build: {r}");
        assert_eq!(std::fs::read(root.join("a")).unwrap(), std::fs::read(root.join("b")).unwrap(), "the same binary");
        assert_eq!(std::process::Command::new(root.join("b")).status().ok().and_then(|s| s.code()), Some(7));
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A fingerprint finds its object under another unit name: release unit names are
    /// positions, and a unit inserted before others renames them.
    #[test]
    fn a_fingerprint_finds_its_object_under_a_new_name() {
        use super::UnitIn;
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let root = std::env::temp_dir().join(format!("lust-cc-rename-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let cache = crate::driver::cache::Cache::at(&root.join("cache"));
        let (work, bin) = (root.join("work"), root.join("bin"));
        let unit = |name: &str, fp: u128, text: Option<&str>| UnitIn { name: name.into(), fp: Some(fp), text: text.map(str::to_string) };
        let main = "int f(void);\nint main(void) {\n  return f();\n}\n";
        let f = "int f(void) {\n  return 3;\n}\n";
        super::build(&[unit("u0", 1, Some(main)), unit("u1", 7, Some(f))], &spec, &bin, false, Some(&cache), &work).unwrap();
        let moved = [unit("u0", 1, Some(main)), unit("u1", 9, Some("int h(void) {\n  return 0;\n}\n")), unit("u2", 7, None)];
        assert!(super::memo_misses(&moved, &spec, false, Some(&cache), &work).is_empty());
        let r = super::build(&moved, &spec, &bin, false, Some(&cache), &work).unwrap();
        assert!(r.contains("3 units (2 from cache"), "u2 takes u1's object: {r}");
        assert_eq!(std::process::Command::new(&bin).status().ok().and_then(|s| s.code()), Some(3));
        let _ = std::fs::remove_dir_all(&root);
    }

    /// `memo_misses` answers what `build` answers for the same inputs: the units it sends
    /// back with `NeedText` (an LLVM unit's parts with mixed text among them), or none
    /// when it builds.
    #[test]
    fn memo_misses_agrees_with_build() {
        use super::{CcError, UnitIn};
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let root = std::env::temp_dir().join(format!("lust-cc-misses-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let cache = crate::driver::cache::Cache::at(&root.join("cache"));
        let (work, bin) = (root.join("work"), root.join("bin"));
        let main = |ret: u32| Some(format!("int f(void);\nint main(void) {{\n  return f() + {ret};\n}}\n"));
        let f = || Some("int f(void) {\n  return 3;\n}\n".to_string());
        let unit = |name: &str, fp: u128, text: Option<String>| UnitIn { name: name.into(), fp: Some(fp), text };
        super::build(&[unit("u0", 1, main(1)), unit("u1", 7, f())], &spec, &bin, false, Some(&cache), &work).unwrap();
        let cases = [
            vec![unit("u0", 2, main(2)), unit("u1", 7, None)],
            vec![unit("u0", 2, None), unit("u1", 8, None)],
            vec![unit("u0", 3, main(3)), unit("u1", 7, None), unit("u1.ll", 9, Some("ir".into())), unit("u1.hc", 9, None)],
        ];
        for units in &cases {
            let misses = super::memo_misses(units, &spec, false, Some(&cache), &work);
            match super::build(units, &spec, &bin, false, Some(&cache), &work) {
                Err(CcError::NeedText(n)) => assert_eq!(n, misses),
                Ok(_) => assert!(misses.is_empty(), "built, but the pre-check named {misses:?}"),
                Err(e) => panic!("{e}"),
            }
        }
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A cache hit hard-links the object into the work dir; a later compile of other C to
    /// the same object path must not write through the link into the cache entry.
    #[test]
    fn a_compile_never_writes_through_a_linked_cache_entry() {
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let root = std::env::temp_dir().join(format!("lust-cc-link-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let cache = crate::driver::cache::Cache::at(&root.join("cache"));
        let (work, bin) = (root.join("work"), root.join("bin"));
        let build = |ret: u32| {
            let units = vec![super::UnitIn::text("u0", format!("int main(void) {{\n  return {ret};\n}}\n"))];
            super::build(&units, &spec, &bin, false, Some(&cache), &work).unwrap()
        };
        build(1);
        let entry = std::fs::read_dir(root.join("cache")).unwrap().flatten().map(|e| e.path()).find(|p| p.extension().is_some_and(|x| x == "o")).unwrap();
        let bytes = std::fs::read(&entry).unwrap();
        assert!(build(1).contains("(1 from cache"));
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let ino = |p: &std::path::Path| std::fs::metadata(p).unwrap().ino();
            assert_eq!(ino(&entry), ino(&work.join("u0.o")), "a hit links the entry");
        }
        build(2);
        assert_eq!(std::fs::read(&entry).unwrap(), bytes, "the compile of other C left the entry alone");
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn zig_targets_cover_the_release_triples() {
        assert_eq!(super::zig_target("aarch64-unknown-linux-musl"), Some("aarch64-linux-musl"));
        assert_eq!(super::zig_target("x86_64-pc-windows-msvc"), Some("x86_64-windows-gnu"));
        assert_eq!(super::zig_target("aarch64-apple-darwin"), Some("aarch64-macos"));
        assert_eq!(super::zig_target("riscv64gc-unknown-linux-gnu"), None);
    }

    fn zig_spec(target: &str) -> super::CcSpec {
        let cmd: Vec<String> = ["zig", "cc", "-target", target].into_iter().map(str::to_string).collect();
        super::CcSpec { triple: String::new(), cxx: super::cxx_for(&cmd), cmd, statik: true, exe_suffix: "" }
    }

    #[test]
    fn unit_words_run_zig_clang_only_for_a_listed_target_in_a_release_build() {
        let spec = zig_spec("x86_64-linux-musl");
        let direct = super::unit_words(&spec, false, false);
        assert_eq!(direct[..3], ["zig", "clang", "--target=x86_64-linux-musl"].map(String::from));
        assert_eq!(super::unit_words(&spec, true, false)[..], spec.cmd[..], "a debug build keeps zig cc");
        assert_eq!(super::unit_words(&spec, false, true)[..], spec.cmd[..], "a unit with system headers keeps zig cc");
        let arm = zig_spec("aarch64-linux-musl");
        assert_eq!(super::unit_words(&arm, false, false)[..], arm.cmd[..], "an unlisted target keeps zig cc");
        let mut extra = zig_spec("x86_64-linux-musl");
        extra.cmd.extend(["-mllvm".to_string(), "-x".to_string()]);
        assert_eq!(super::unit_words(&extra, false, false)[direct.len()..], ["-mllvm", "-x"].map(String::from), "LUST_CC's extra words carry over");
    }

    /// The direct clang gives zig cc's code: the same assembly for C that shows each flag
    /// (the CPU's tuning in a loop and a switch, unwind tables in a leaf, a global, a cleanup).
    #[test]
    fn direct_clang_gives_zig_cc_code() {
        if !super::on_path("zig") {
            return;
        }
        let dir = std::env::temp_dir().join(format!("lust-direct-cc-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join("u.c");
        std::fs::write(
            &src,
            "typedef unsigned long u64;\nstruct P { u64 a, b, c; };\nextern void g(struct P *);\nextern void drop(void *);\nextern int counter;\n\
             static const char *names[] = { \"one\", \"two\", \"three\" };\n\
             u64 f(struct P *p, u64 n, double x) {\n  struct P q __attribute__((cleanup(drop))) = *p;\n  u64 s = 0;\n\
               for (u64 i = 0; i < n; i++) s += p->a * i + (u64)(x * i);\n\
               switch (n & 3) { case 0: s ^= 7; break; case 1: s += names[1][0]; break; case 2: g(&q); break; default: s -= 1; }\n\
               g(&q);\n  return s + q.b;\n}\nint leaf(int x) { counter++; return x * 3; }\n",
        )
        .unwrap();
        let spec = zig_spec("x86_64-linux-musl");
        let asm = |words: &[String], out: &str| {
            let out = dir.join(out);
            let st = std::process::Command::new(&words[0]).args(&words[1..]).args(super::cflags(false).split_whitespace()).arg("-S").arg(&src).arg("-o").arg(&out).status().unwrap();
            assert!(st.success(), "{} failed", words.join(" "));
            std::fs::read_to_string(out).unwrap()
        };
        let direct = super::unit_words(&spec, false, false);
        assert_ne!(direct[..], spec.cmd[..]);
        assert_eq!(asm(&direct, "direct.s"), asm(&spec.cmd, "zig-cc.s"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A kept preprocessed text comes back only for the same inputs: another define, or one
    /// changed byte in a header it read, runs the preprocessor again.
    #[test]
    fn a_kept_preprocessed_text_misses_on_a_changed_define_or_header() {
        if !super::on_path("cc") {
            return;
        }
        let dir = std::env::temp_dir().join(format!("lust-pre-kept-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let inc = dir.join("inc");
        std::fs::create_dir_all(&inc).unwrap();
        std::fs::write(inc.join("t.h"), "#define T 1\n").unwrap();
        let text = "#include <t.h>\nint t = T + X;\n";
        let words = |x: &str| vec!["cc".to_string(), format!("-I{}", inc.display()), format!("-DX={x}")];
        let kept = |w: &[String]| String::from_utf8(super::preprocessed_kept(&dir, "u1", text, w, "-O2", false).expect("cc preprocesses")).unwrap();
        assert!(kept(&words("2")).contains("int t = 1 + 2;"));
        // Mark the kept text, to see when a call reads it back.
        let out = std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).find(|p| p.extension().is_some_and(|e| e == "i")).expect("a kept text");
        std::fs::write(&out, "kept\n").unwrap();
        assert_eq!(kept(&words("2")), "kept\n", "the same inputs read the kept text");
        assert!(kept(&words("3")).contains("int t = 1 + 3;"), "another define runs the preprocessor");
        std::fs::write(inc.join("t.h"), "#define T 7\n").unwrap();
        assert!(kept(&words("2")).contains("int t = 7 + 2;"), "a changed header byte runs the preprocessor");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Another build time (SOURCE_DATE_EPOCH, which __DATE__ reads) is another input: the
    /// text kept under one epoch is not used under another (tsgo's mimalloc unit holds
    /// __DATE__). A text with __TIMESTAMP__ is never kept.
    #[test]
    fn a_kept_preprocessed_text_misses_under_another_build_time() {
        if !super::on_path("cc") {
            return;
        }
        let dir = std::env::temp_dir().join(format!("lust-pre-epoch-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let text = "#include <stddef.h>\nconst char *built = __DATE__;\n";
        let words = vec!["cc".to_string()];
        let kept = |t: &str, env: &str| String::from_utf8(super::preprocessed_kept_in(&dir, "u2", t, &words, "-O2", false, env).expect("cc preprocesses")).unwrap();
        kept(text, "SOURCE_DATE_EPOCH=100000 []");
        let out = std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).find(|p| p.extension().is_some_and(|e| e == "i")).expect("a kept text");
        std::fs::write(&out, "kept\n").unwrap();
        assert_eq!(kept(text, "SOURCE_DATE_EPOCH=100000 []"), "kept\n", "the same build time reads the kept text");
        assert_ne!(kept(text, "SOURCE_DATE_EPOCH=200000 []"), "kept\n", "another build time runs the preprocessor");
        let stamped = "#include <stddef.h>\nconst char *built = __TIMESTAMP__;\n";
        kept(stamped, "SOURCE_DATE_EPOCH=100000 []");
        assert_eq!(std::fs::read_dir(&dir).unwrap().flatten().filter(|e| e.path().extension().is_some_and(|x| x == "i")).count(), 1, "a __TIMESTAMP__ text is not kept");
        let env = std::env::var("SOURCE_DATE_EPOCH").unwrap_or_else(|_| "0".into());
        assert!(super::preprocess_env().starts_with(&format!("SOURCE_DATE_EPOCH={env} ")), "the build time cc_command gives is in the key");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn cxx_driver_matches_the_c_driver() {
        let words = |s: &str| s.split_whitespace().map(str::to_string).collect::<Vec<String>>();
        assert_eq!(super::cxx_for(&words("zig cc -target x86_64-linux-musl")), words("zig c++ -target x86_64-linux-musl"));
        assert_eq!(super::cxx_for(&words("/usr/bin/clang-18")), words("/usr/bin/clang++-18"));
        assert_eq!(super::cxx_for(&words("x86_64-linux-musl-gcc")), words("x86_64-linux-musl-g++"));
        assert_eq!(super::cxx_for(&words("cc")), words("c++"));
        assert_eq!(super::cxx_for(&words("clang++")), words("clang++"));
    }

    /// The key text of a unit with `#include`s is its preprocessed text: `__DATE__` and
    /// `__TIME__` in it must not be the clock's, or the unit misses the cache every second.
    #[test]
    fn the_preprocessor_sees_a_fixed_build_time() {
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        if std::env::var_os("SOURCE_DATE_EPOCH").is_some() {
            return;
        }
        let text = "#include <stddef.h>\nconst char *built = __DATE__ \" \" __TIME__;\n";
        let pre = super::preprocessed(text, &spec.cmd, &super::cflags(false), false).expect("the host C compiler preprocesses");
        let pre = String::from_utf8_lossy(&pre);
        assert!(pre.contains("\"Jan  1 1970\" \" \" \"00:00:00\""), "{pre}");
    }

    /// zig cc caches a compile by its source and args: an LLVM unit whose IR stays while the
    /// C it links as bitcode changes must compile again, not get the last object at its path.
    #[test]
    fn an_llvm_unit_whose_c_changes_compiles_again_under_zig() {
        if !super::on_path("zig") {
            return;
        }
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        let dir = std::env::temp_dir().join(format!("lust-zig-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let (src, obj) = (dir.join("u9.c"), dir.join("u9.o"));
        std::fs::write(&src, "").unwrap();
        let ll = "declare i32 @h()\ndefine i32 @fl_aa() {\nentry:\n  %r = call i32 @h()\n  ret i32 %r\n}\n";
        let flags: Vec<String> = super::cflags(false).split_whitespace().map(str::to_string).collect();
        let calls = |hc: &str, callee: &str| {
            super::compile_pair(&spec, &flags, false, &src, ll, hc, &obj, None, None, false, None).expect("compiles");
            std::fs::read(&obj).unwrap().windows(callee.len()).any(|w| w == callee.as_bytes())
        };
        assert!(calls("int old_fn(void);\nint h(void) { return old_fn(); }\n", "old_fn"));
        assert!(calls("int new_fn(void);\nint h(void) { return new_fn(); }\n", "new_fn"), "the object of the old C");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An LLVM unit's key moves with each of its texts, and with where one ends and the next
    /// begins (the parts are hashed with their lengths).
    #[test]
    fn an_llvm_unit_key_moves_with_each_text() {
        let spec = super::CcSpec { triple: "x86_64-unknown-linux-musl".into(), cxx: vec!["c++".into()], cmd: vec!["cc".into()], statik: false, exe_suffix: "" };
        let key = |c: &str, ll: &str, hc: &str, extra: &str| super::ll_unit_key(c, ll, hc, extra, &spec, false, None);
        let base = key("c", "ll", "hc", "x");
        for other in [key("c2", "ll", "hc", "x"), key("c", "ll2", "hc", "x"), key("c", "ll", "hc2", "x"), key("c", "ll", "hc", "y"), key("cl", "l", "hc", "x")] {
            assert_ne!(base, other);
        }
        assert_eq!(base, key("c", "ll", "hc", "x"));
    }

    #[test]
    fn unit_key_moves_with_every_input() {
        let spec = |triple: &str, cmd: &str| {
            let cmd: Vec<String> = cmd.split_whitespace().map(str::to_string).collect();
            super::CcSpec { triple: triple.into(), cxx: super::cxx_for(&cmd), cmd, statik: false, exe_suffix: "" }
        };
        let key = |text: &str, triple: &str, cmd: &str, debug: bool, profile: Option<&str>, cxx: bool| super::unit_key(text, None, &spec(triple, cmd), debug, profile, cxx);
        let base = key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, false);
        assert_ne!(base, key("int g(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, false), "C text");
        assert_ne!(base, key("int f(void);", "x86_64-unknown-linux-musl", "zig cc", false, None, false), "target");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", true, None, false), "debug");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "clang", false, None, false), "compiler");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, Some("p1"), false), "profile");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, true), "C++");
    }
}
