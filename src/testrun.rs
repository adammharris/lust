// `lust test <file.rs> [filter]`: finds `#[test]` functions, builds one test binary, and runs
// each test in its own child process with a timeout. A panicking test ends its child only (it
// unwinds, as under `rustc --test`, and exits 101), never the run.
//
// The test binary is the user file plus a generated `main` that dispatches on
// `std::env::args().count()`: the runner passes i+1 dummy arguments to run test i. With no extra
// arguments the binary runs every test in order. A user `main` is renamed in place (same byte
// length, so every span still matches the user file); `rustc --test` ignores `main` the same way.
// Tests in inline modules (at any depth) are named by their path (`tests::adds`), as in rustc;
// the harness reaches them through a `pub(crate)` fn it adds at each module's closing brace,
// on that line (`harness_shims`). A module file (`mod name;`) is an error: the harness is a copy
// of this one file and could not read the tests in it.
//
// Exit status follows cargo test: 0 when every selected test passes, 101 when the build fails or
// any test fails or times out, 2 for bad arguments or an unreadable file. A filtered test is
// never reported as a pass; it is counted in `filtered_out`. A `#[ignore]` test is reported as
// ignored and never runs. A `#[should_panic]` test passes only when it panics with the
// expected text, when one is written.
use crate::ast::{Ast, Attr, AttrInput, Expr, Item, ItemKind, TyExpr};
use crate::diag::{self, Diag, FileId, SourceMap};
use crate::driver::{self, Cmd, Request, SessionKey};
use crate::intern::{Interner, Known};
use crate::{lexer, parser};
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

mod krate;

const USAGE: &str = "usage: lust test <file.rs> [filter...] [--json] [--list] [--timeout SECONDS] [--max-errors N]\n       lust test <root.rs> --manifest-path <Cargo.toml> --lib | --test <name> [--package <name>] [--features <a,b>] [--no-default-features] [--all-features] [filter...] [--exact] [--skip FILTER] [--ignored | --include-ignored] [--test-threads N] [--json] [--list] [--timeout SECONDS]";

struct Opts {
    file: PathBuf,
    /// libtest's filters: a test runs when its name contains one of them
    /// (all run when there are none), or equals one under `--exact`.
    filters: Vec<String>,
    /// `--skip`: a test whose name contains one (equals one under `--exact`) does not run.
    skip: Vec<String>,
    exact: bool,
    /// `--ignored` runs only the `#[ignore]` tests, `--include-ignored` runs them too.
    ignored: bool,
    include_ignored: bool,
    /// `--test-threads N` (Cargo-target mode): else `RUST_TEST_THREADS`, else the core count.
    threads: Option<usize>,
    json: bool,
    list: bool,
    timeout: Duration,
    max_errors: usize,
}

impl Opts {
    /// True when libtest's filters select the test `name`.
    fn selects(&self, name: &str) -> bool {
        let hit = |f: &String| if self.exact { name == f } else { name.contains(f.as_str()) };
        (self.filters.is_empty() || self.filters.iter().any(hit)) && !self.skip.iter().any(hit)
    }
}

/// Parses `lust test` arguments (without the word `test`).
fn parse_opts(args: &[String]) -> Result<Opts, String> {
    let (mut file, mut filters, mut json, mut list) = (None, Vec::new(), false, false);
    let (mut timeout, mut max_errors) = (Duration::from_secs(10), diag::DEFAULT_MAX_ERRORS);
    let (mut skip, mut exact, mut ignored, mut include_ignored, mut threads) = (Vec::new(), false, false, false, None);
    let threads_of = |v: &str| v.parse().ok().filter(|&n: &usize| n > 0).ok_or_else(|| USAGE.to_string());
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            // libtest's own flags, as `cargo test -- <flags>` passes them.
            "--" | "--nocapture" | "--show-output" => {}
            "--exact" => exact = true,
            "--ignored" => ignored = true,
            "--include-ignored" => include_ignored = true,
            "--skip" => skip.push(it.next().ok_or(USAGE)?.clone()),
            "--test-threads" => threads = Some(threads_of(it.next().ok_or(USAGE)?)?),
            _ if a.starts_with("--test-threads=") => threads = Some(threads_of(&a["--test-threads=".len()..])?),
            _ if a.starts_with("--skip=") => skip.push(a["--skip=".len()..].to_string()),
            "--json" => json = true,
            "--list" => list = true,
            "--timeout" => timeout = parse_secs(it.next().ok_or(USAGE)?)?,
            "--max-errors" => max_errors = it.next().and_then(|v| v.parse().ok()).ok_or(USAGE)?,
            _ if a.starts_with("--timeout=") => timeout = parse_secs(&a["--timeout=".len()..].to_string())?,
            _ if a.starts_with("--max-errors=") => max_errors = a["--max-errors=".len()..].parse().map_err(|_| USAGE.to_string())?,
            _ if a.starts_with("--") => return Err(USAGE.into()),
            _ if file.is_none() => file = Some(PathBuf::from(a)),
            _ => filters.push(a.clone()),
        }
    }
    Ok(Opts { file: file.ok_or(USAGE)?, filters, skip, exact, ignored, include_ignored, threads, json, list, timeout, max_errors })
}

fn parse_secs(s: &String) -> Result<Duration, String> {
    let v: f64 = s.parse().map_err(|_| USAGE.to_string())?;
    if v <= 0.0 {
        return Err(USAGE.into());
    }
    Ok(Duration::from_secs_f64(v))
}

/// One test case result.
struct Outcome {
    name: String,
    status: &'static str, // "pass", "fail", "timeout", or "ignored"
    duration_ms: f64,
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
}

/// Runs the binary once for test `index`, capturing output and enforcing the timeout.
fn run_one(run: &Run, index: usize, name: &str, timeout: Duration) -> Outcome {
    let start = Instant::now();
    let mut cmd = Command::new(run.bin);
    if let Some(dir) = run.cwd {
        cmd.current_dir(dir);
    }
    cmd.envs(run.env.iter().cloned());
    cmd.args(std::iter::repeat_n("x", index + 1)).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return Outcome {
                name: name.into(),
                status: "fail",
                duration_ms: millis(start),
                exit_code: None,
                stdout: String::new(),
                stderr: format!("cannot run the test binary: {e}"),
            };
        }
    };
    let mut out_pipe = child.stdout.take().expect("piped");
    let mut err_pipe = child.stderr.take().expect("piped");
    let out_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let err_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = err_pipe.read_to_end(&mut buf);
        buf
    });
    let (status, timed_out) = loop {
        match child.try_wait() {
            Ok(Some(s)) => break (Some(s), false),
            Ok(None) if start.elapsed() < timeout => std::thread::sleep(Duration::from_millis(2)),
            Ok(None) => {
                let _ = child.kill();
                break (child.wait().ok(), true);
            }
            Err(_) => break (child.wait().ok(), false),
        }
    };
    let stdout = String::from_utf8_lossy(&out_thread.join().unwrap_or_default()).into_owned();
    let stderr = String::from_utf8_lossy(&err_thread.join().unwrap_or_default()).into_owned();
    let exit_code = status.and_then(|s| s.code());
    let status = if timed_out {
        "timeout"
    } else if exit_code == Some(0) {
        "pass"
    } else {
        "fail"
    };
    Outcome { name: name.into(), status, duration_ms: millis(start), exit_code, stdout, stderr }
}

fn millis(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

/// One `#[test]` fn and its harness attributes. `should_panic` is
/// `Some(expected)` for `#[should_panic]`, where `expected` is the
/// panic text it must contain, or `None` inside for the bare form.
#[derive(Clone)]
struct TestCase {
    /// The path from the crate root (`tests::adds`), as rustc --test names it.
    name: String,
    /// The inline modules from the crate root to the fn (empty at the root).
    module: Vec<String>,
    /// The fn's own name.
    fn_name: String,
    ignored: bool,
    should_panic: Option<Option<String>>,
}

/// Finds the `#[test]` fns in `items`, the crate root or an inline module body
/// whose path is `module`, as rustc --test does: in every inline module, also
/// nested ones. `mods` gets each inline module that holds a test, with the byte
/// offset of its closing `}`, where the harness adds the fns that reach the
/// tests (`harness_shims`). A test lust cannot reach is an error, never a test
/// that silently does not run.
fn find_tests(
    items: &[Item],
    module: &[String],
    src: &str,
    ast: &Ast,
    interner: &Interner,
    tests: &mut Vec<TestCase>,
    mods: &mut Vec<(Vec<String>, usize)>,
    bad: &mut Vec<Diag>,
) {
    for item in items {
        match &item.kind {
            ItemKind::Fn(def) if def.is_test => {
                let fn_name = interner.get(def.name).to_string();
                let ret_ok = def.ret.is_none_or(|t| matches!(ast.ty(t), TyExpr::Unit));
                if def.self_param.is_some() || !def.params.is_empty() || !ret_ok {
                    bad.push(Diag::new(
                        "L0110",
                        def.name_span,
                        format!("test function `{fn_name}` must take no arguments and return `()`"),
                        format!("Change the signature to `fn {fn_name}() {{ ... }}`."),
                    ));
                } else {
                    let (ignored, should_panic) = harness_attrs(&item.attrs, ast, interner);
                    let name = module.iter().chain([&fn_name]).cloned().collect::<Vec<_>>().join("::");
                    tests.push(TestCase { name, module: module.to_vec(), fn_name, ignored, should_panic });
                }
            }
            ItemKind::Impl(imp) => {
                for def in &imp.fns {
                    if def.is_test {
                        bad.push(diag::unsupported(def.name_span, "#[test] functions inside impl blocks"));
                    }
                }
            }
            ItemKind::Mod(m) => {
                let mut path = module.to_vec();
                path.push(interner.get(m.name).to_string());
                let Some(body) = &m.body else {
                    // The harness is built from a copy of this one file, so it
                    // cannot read the module's file or the tests in it.
                    bad.push(diag::unsupported(m.name_span, "module files (`mod name;`) in `lust test`"));
                    continue;
                };
                let before = tests.len();
                find_tests(body, &path, src, ast, interner, tests, mods, bad);
                if tests.len() > before {
                    // A module a macro wrote has no closing brace of its own in the file.
                    let close = (m.span.hi as usize).checked_sub(1).filter(|&c| src.as_bytes().get(c) == Some(&b'}'));
                    match close {
                        Some(c) if src.get(m.name_span.lo as usize..m.name_span.hi as usize) == Some(interner.get(m.name)) => {
                            mods.push((path, c))
                        }
                        _ => bad.push(diag::unsupported(m.name_span, "#[test] fns in a module that a macro writes, in `lust test`")),
                    }
                }
            }
            _ => {}
        }
    }
}

/// The text the harness adds before the closing `}` of each module in `mods`:
/// one `pub(crate)` fn per selected test in or under that module, which calls
/// the test (or the same fn of the child module on the way to it). Test `i`
/// is `__lust_test_{i}`. A private test fn in a private module is reachable
/// this way, as rustc's harness reaches it. The text has no newline, so lines
/// (and panic locations) still match the user file. Returned last offset first,
/// for in-place insertion.
fn harness_shims(selected: &[TestCase], mods: &[(Vec<String>, usize)]) -> Vec<(usize, String)> {
    let mut out: Vec<(usize, String)> = mods
        .iter()
        .filter_map(|(path, close)| {
            let text: String = selected
                .iter()
                .enumerate()
                .filter(|(_, t)| t.module.starts_with(path))
                .map(|(i, t)| {
                    let target = match t.module.get(path.len()) {
                        None => t.fn_name.clone(),
                        Some(child) => format!("{child}::__lust_test_{i}"),
                    };
                    format!(" pub(crate) fn __lust_test_{i}() {{ self::{target}() }}")
                })
                .collect();
            (!text.is_empty()).then_some((*close, text))
        })
        .collect();
    out.sort_by(|a, b| b.0.cmp(&a.0));
    out
}

/// The harness call that runs selected test `i`.
fn harness_call(i: usize, t: &TestCase) -> String {
    match t.module.first() {
        None => t.fn_name.clone(),
        Some(top) => format!("{top}::__lust_test_{i}"),
    }
}

/// The string literal in an attribute input, whichever of the three
/// stored shapes holds it (`= "x"` trees, a parenthesized list, or an
/// `Eq` expression from a cfg_attr expansion).
fn attr_str(input: &AttrInput, ast: &Ast) -> Option<String> {
    fn in_trees(trees: &[lexer::TokenTree], ast: &Ast) -> Option<String> {
        trees.iter().find_map(|t| match t {
            lexer::TokenTree::Token(tok) => match tok.tok {
                lexer::Tok::Str(i, _) => ast.strings.get(i as usize).cloned(),
                _ => None,
            },
            lexer::TokenTree::Delim(_, inner, _) => in_trees(inner, ast),
        })
    }
    match input {
        AttrInput::None => None,
        AttrInput::Eq(e) => match ast.expr(*e) {
            Expr::Str(i) => ast.strings.get(*i as usize).cloned(),
            _ => None,
        },
        AttrInput::List(_, trees) => in_trees(trees, ast),
    }
}

/// Reads `#[ignore]` and the first `#[should_panic]` from one item.
/// A second `should_panic` does not change the result, as in rustc
/// (probed: the first expected text wins). The parser already judged
/// each written form, so a bare `should_panic` and one whose string
/// this reader cannot find both count as no expected text.
fn harness_attrs(attrs: &[Attr], ast: &Ast, interner: &Interner) -> (bool, Option<Option<String>>) {
    let mut ignored = false;
    let mut should_panic = None;
    for a in attrs {
        if a.path.len() != 1 {
            continue;
        }
        match interner.get(a.path[0].name) {
            "ignore" => ignored = true,
            "should_panic" if should_panic.is_none() => should_panic = Some(attr_str(&a.input, ast)),
            _ => {}
        }
    }
    (ignored, should_panic)
}

/// The JSON summary record printed last in `--json` mode.
fn summary_json(file: &str, hash: &str, build: &str, outcomes: &[Outcome], filtered_out: usize, start: Instant) -> String {
    let count = |s: &str| outcomes.iter().filter(|o| o.status == s).count();
    format!(
        "{{\"schema\":{},\"kind\":\"summary\",\"file\":{},\"source_hash\":{},\"build\":\"{}\",\"total\":{},\"passed\":{},\"failed\":{},\"timed_out\":{},\"ignored\":{},\"filtered_out\":{},\"duration_ms\":{:.3}}}",
        diag::SCHEMA,
        diag::json_str(file),
        diag::json_str(hash),
        build,
        outcomes.len(),
        count("pass"),
        count("fail"),
        count("timeout"),
        count("ignored"),
        filtered_out,
        millis(start)
    )
}

/// Entry point for `lust test`. Returns the process exit code.
pub fn run(args: &[String]) -> i32 {
    // A Cargo target (`--manifest-path`, `--lib`, `--test <name>`, ...): krate.rs.
    if let Some((rest, crate_args)) = krate::split_args(args) {
        return match parse_opts(&rest) {
            Ok(o) => krate::run(&o, &crate_args),
            Err(u) => {
                eprintln!("{u}");
                2
            }
        };
    }
    let opts = match parse_opts(args) {
        Ok(o) => o,
        Err(u) => {
            eprintln!("{u}");
            return 2;
        }
    };
    let start = Instant::now();
    let abs = |p: &PathBuf| std::path::absolute(p).unwrap_or_else(|_| p.clone());
    let file = abs(&opts.file);
    let path = file.to_string_lossy().into_owned();
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return 2;
        }
    };
    let hash = diag::source_hash(&src);
    // Prints rendered diagnostics in the right stream for the mode, plus the JSON summary.
    let fail_build = |text: String, filtered_out: usize| -> i32 {
        if opts.json {
            print!("{text}");
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        } else {
            eprint!("{text}");
        }
        101
    };

    // Parse once to find the tests, their names, and the user's `main` (if any). This
    // one-shot parse has its own source map with the user file as file 0.
    let mut map = SourceMap::default();
    map.add_file(&path, &src);
    let interner = Interner::default();
    let known = Known::new(&interner);
    let lexed = match lexer::lex(&src, FileId(0), 0, &interner).and_then(|l| {
        let ctx = crate::expand::ExpandCtx::for_file(&interner, &known, std::path::Path::new(&path), &src, true);
        crate::expand::expand_lexed(l, &ctx)
    }) {
        Ok(l) => l,
        Err(d) => return fail_build(diag::render(&mut [d], &map, &src, opts.json, opts.max_errors), 0),
    };
    let ast = match parser::parse(&lexed, &interner, &known) {
        Ok(a) => a,
        Err(d) => return fail_build(diag::render(&mut [d], &map, &src, opts.json, opts.max_errors), 0),
    };
    let mut tests: Vec<TestCase> = Vec::new();
    let mut fn_names: Vec<String> = Vec::new();
    let mut main_span = None;
    let mut bad: Vec<Diag> = Vec::new();
    for item in &ast.items {
        if let ItemKind::Fn(def) = &item.kind {
            let name = interner.get(def.name).to_string();
            if name == "main" {
                main_span = Some(def.name_span);
            }
            fn_names.push(name);
        }
    }
    let mut mods: Vec<(Vec<String>, usize)> = Vec::new();
    find_tests(&ast.items, &[], &src, &ast, &interner, &mut tests, &mut mods, &mut bad);
    if !bad.is_empty() {
        return fail_build(diag::render(&mut bad, &map, &src, opts.json, opts.max_errors), 0);
    }
    let selected: Vec<TestCase> = tests.iter().filter(|t| opts.selects(&t.name)).cloned().collect();
    let filtered_out = tests.len() - selected.len();
    if opts.list {
        if opts.json {
            let names: Vec<String> = selected.iter().map(|t| diag::json_str(&t.name)).collect();
            println!(
                "{{\"schema\":{},\"kind\":\"list\",\"file\":{},\"source_hash\":{},\"tests\":[{}],\"filtered_out\":{}}}",
                diag::SCHEMA,
                diag::json_str(&path),
                diag::json_str(&hash),
                names.join(","),
                filtered_out
            );
        } else {
            for t in &selected {
                println!("{}: test", t.name);
            }
            println!("\n{} tests", selected.len());
        }
        return 0;
    }

    // Check the user file as written first, so diagnostics name the real file and hash.
    // One session per crate root: the user file as a test crate, then the
    // generated harness file as its own bin crate (driver sessions are keyed
    // by crate, so the harness build below gets a fresh session).
    let dir = std::env::temp_dir().join(format!("lust-test-{}", std::process::id()));
    let mut session = driver::Session::new(dir.join("obj"), false, SessionKey::synthetic(&file, true));
    session.caches.leak_at_exit = true;
    // Both requests are test crates: the harness build must keep the
    // `#[test]` fns it calls (a normal build removes them).
    let req = |cmd: Cmd, file: PathBuf, out: PathBuf| Request {
        cmd,
        session: SessionKey::synthetic(&file, true),
        file,
        out,
        json: opts.json,
        timings: false,
        debug: false,
        emit_c: None,
        max_errors: opts.max_errors,
        run_args: None,
        // The check below runs on the user file before the generated `main` is added.
        harness: cmd == Cmd::Check, cc: false,
        client: Default::default(),
    };
    let check = driver::compile(&req(Cmd::Check, file.clone(), dir.join("testbin")), &mut session);
    if check.code != 0 {
        let _ = std::fs::remove_dir_all(&dir);
        // In JSON mode the driver puts diagnostics on stdout already; keep its split.
        print!("{}", check.stdout);
        eprint!("{}", check.stderr);
        if opts.json {
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        }
        return 101;
    }

    // Build the harness: user source (with `main` renamed) plus a generated dispatching `main`.
    let mut harness = src.clone();
    if let Some(span) = main_span {
        let replacement = ["zain", "yain", "xain", "wain", "vain", "qain"]
            .iter()
            .find(|c| !fn_names.iter().any(|n| n == *c))
            .expect("no free name for the user main");
        harness.replace_range(span.lo as usize..span.hi as usize, replacement);
    }
    for (at, text) in harness_shims(&selected, &mods) {
        harness.insert_str(at, &text);
    }
    harness.push_str("\nfn main() {\n    let n = std::env::args().count();\n    if n == 1 {\n");
    for (i, t) in selected.iter().enumerate().filter(|(_, t)| !t.ignored) {
        harness.push_str(&format!("        {}();\n", harness_call(i, t)));
    }
    for (i, t) in selected.iter().enumerate() {
        harness.push_str(&format!("    }} else if n == {} {{\n        {}();\n", i + 2, harness_call(i, t)));
    }
    harness.push_str("    }\n}\n");
    if let Err(e) = std::fs::create_dir_all(&dir).and_then(|_| std::fs::write(dir.join("harness.rs"), &harness)) {
        eprintln!("error: cannot write the test harness: {e}");
        let _ = std::fs::remove_dir_all(&dir);
        return 101;
    }
    let harness_path = abs(&dir.join("harness.rs"));
    let bin = dir.join("testbin");
    let mut session = driver::Session::new(dir.join("obj-harness"), false, SessionKey::synthetic(&harness_path, true));
    session.caches.leak_at_exit = true;
    let build = driver::compile(&req(Cmd::Build, harness_path.clone(), bin.clone()), &mut session);
    if build.code != 0 {
        // Spans match the user file byte for byte; only the file name differs.
        let fix = |s: &str| s.replace(&harness_path.to_string_lossy().into_owned(), &path);
        let _ = std::fs::remove_dir_all(session.obj_dir());
        print!("{}", fix(&build.stdout));
        eprint!("{}", fix(&build.stderr));
        if opts.json {
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        }
        let _ = std::fs::remove_dir_all(&dir);
        return 101;
    }

    let cases: Vec<(usize, TestCase)> = selected.iter().cloned().enumerate().collect();
    let harness_name = harness_path.to_string_lossy().into_owned();
    let run = Run { bin: &bin, path: &path, hash: &hash, cwd: None, env: &[], rename: Some(&harness_name) };
    let code = run_cases(&run, &cases, &opts, filtered_out, start);
    let _ = std::fs::remove_dir_all(session.obj_dir());
    let _ = std::fs::remove_dir_all(&dir);
    code
}

/// What `run_cases` runs: the test binary, the names it reports under, and
/// the process setup. `rename` is a harness file path that panic text names,
/// shown as the user's file instead.
struct Run<'a> {
    bin: &'a PathBuf,
    path: &'a str,
    hash: &'a str,
    cwd: Option<&'a std::path::Path>,
    env: &'a [(String, String)],
    rename: Option<&'a str>,
}

/// Runs each case (harness index, test) in its own child process and
/// reports it; returns the exit code (0 when every case passes, else 101).
fn run_cases(run: &Run, cases: &[(usize, TestCase)], opts: &Opts, filtered_out: usize, start: Instant) -> i32 {
    if !opts.json {
        println!("running {} tests", cases.len());
    }
    let mut outcomes: Vec<Outcome> = Vec::new();
    for (i, t) in cases {
        // An ignored test is reported, never run, as in rustc.
        let mut o = if t.ignored {
            Outcome {
                name: t.name.clone(),
                status: "ignored",
                duration_ms: 0.0,
                exit_code: None,
                stdout: String::new(),
                stderr: String::new(),
            }
        } else {
            run_one(run, *i, &t.name, opts.timeout)
        };
        // Panic messages name the harness file; its lines match the user file, so rename it back.
        if let Some(h) = run.rename {
            o.stderr = o.stderr.replace(h, run.path);
            o.stdout = o.stdout.replace(h, run.path);
        }
        // A `should_panic` test passes only when it panics, and its
        // output must hold the expected text when one is written.
        // A timeout stays a timeout.
        if let Some(expected) = &t.should_panic
            && o.status != "timeout"
            && o.status != "ignored"
        {
            let text_hit = expected.as_ref().is_none_or(|want| o.stdout.contains(want.as_str()) || o.stderr.contains(want.as_str()));
            o.status = if o.exit_code != Some(0) && text_hit { "pass" } else { "fail" };
        }
        if opts.json {
            println!(
                "{{\"schema\":{},\"kind\":\"test\",\"name\":{},\"status\":\"{}\",\"duration_ms\":{:.3},\"exit_code\":{},\"stdout\":{},\"stderr\":{}}}",
                diag::SCHEMA,
                diag::json_str(&o.name),
                o.status,
                o.duration_ms,
                o.exit_code.map_or("null".into(), |c| c.to_string()),
                diag::json_str(&o.stdout),
                diag::json_str(&o.stderr)
            );
        } else {
            let word = match o.status {
                "pass" => "ok",
                "timeout" => "TIMEOUT",
                "ignored" => "ignored",
                _ => "FAILED",
            };
            // As cargo test names a `should_panic` test.
            let mark = if t.should_panic.is_some() { " - should panic" } else { "" };
            println!("test {}{mark} ... {} ({:.1}ms)", o.name, word, o.duration_ms);
        }
        outcomes.push(o);
    }
    let failed = outcomes.iter().filter(|o| matches!(o.status, "fail" | "timeout")).count();
    if opts.json {
        println!("{}", summary_json(run.path, run.hash, "ok", &outcomes, filtered_out, start));
    } else {
        if failed > 0 {
            println!("\nfailures:");
            for o in outcomes.iter().filter(|o| matches!(o.status, "fail" | "timeout")) {
                println!("---- {} ({}) ----", o.name, o.status);
                if !o.stdout.is_empty() {
                    println!("stdout:\n{}", o.stdout);
                }
                if !o.stderr.is_empty() {
                    println!("stderr:\n{}", o.stderr);
                }
            }
        }
        let passed = outcomes.iter().filter(|o| o.status == "pass").count();
        let timed_out = outcomes.iter().filter(|o| o.status == "timeout").count();
        let ignored = outcomes.iter().filter(|o| o.status == "ignored").count();
        println!(
            "\ntest result: {}. {} passed; {} failed; {} timed out; {} ignored; {} filtered out",
            if failed == 0 { "ok" } else { "FAILED" },
            passed,
            failed - timed_out,
            timed_out,
            ignored,
            filtered_out
        );
    }
    if failed == 0 { 0 } else { 101 }
}
