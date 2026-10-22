// `lust test <root.rs> --manifest-path <Cargo.toml> --lib | --test <name>`: the tests of a
// Cargo target.
//
// A Cargo target's tests live in many files, so the harness cannot be one copied file. The
// crate builds from its own files through the driver's source overlay
// (`driver::set_source_overlay`): each module that holds a test, in a file or inline, gets the
// same `__lust_test_{i}` shims as a one-file test (`harness_shims`), and the crate root gets the
// dispatching `main`. Every added item is `#[cfg(test)]`, so the same files compiled as a
// dependency (the lib of an integration test, or of a dev-dependency) read as written. Each shim
// also carries the `cfg` predicates of its test and of the modules below it, so a test that is
// configured out (`#[cfg(feature = "x")]`) is no build error: the binary lists the tests it
// holds (`LUST_TEST_LIST`), and only those count, as `cargo test` lists only compiled tests.
// The binary runs in the package dir with Cargo's runtime env (`CARGO_MANIFEST_DIR`, ...), as
// under `cargo test`, and as libtest runs one: all the tests in one process, on worker threads
// (`--test-threads`, else `RUST_TEST_THREADS`, else the core count), sorted by name, each on a
// thread named by the test whose panic fails that test only (`RUNNER`). So tests share process
// state as they do under `cargo test`. Shims go before a closing `}` or at the end of a file,
// with no newline before the end, so lines (and panic locations) still match the files.
use super::{Opts, Outcome, TestCase, USAGE, attr_str, harness_attrs, summary_json};
use crate::ast::{Ast, Attr, Item, ItemKind, TyExpr};
use crate::diag::{self, Diag, FileId, SourceMap};
use crate::driver::{self, Cmd};
use crate::intern::{Interner, Known};
use crate::lexer::Tok;
use crate::{lexer, parser};
use std::collections::{HashMap, HashSet};
use std::os::fd::AsFd;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// One test of a Cargo target, found by following the module tree.
struct CrateTest {
    case: TestCase,
    /// The `cfg` predicates of each module on the path (index = depth - 1:
    /// the module's `mod` item and its inner attributes).
    mod_cfgs: Vec<Vec<String>>,
    /// The test fn's own `cfg` predicates.
    fn_cfgs: Vec<String>,
    /// True when the fn returns a value (`Result<(), E>`): `Err` fails the test.
    returns: bool,
}

/// Where a module's shims go: the file and the byte offset (its inline
/// closing `}`, or the end of its file).
struct ShimSite {
    path: Vec<String>,
    file: PathBuf,
    at: usize,
}

/// Splits the crate flags (`--manifest-path`, `--lib`, `--test`, features,
/// ...) out of `lust test` arguments. None when there are none: a one-file test.
pub(super) fn split_args(args: &[String]) -> Option<(Vec<String>, Vec<String>)> {
    const WITH_VALUE: &[&str] = &["--manifest-path", "--package", "-p", "--test", "--features", "--target"];
    const FLAGS: &[&str] = &["--lib", "--no-default-features", "--all-features", "--offline", "--locked", "--frozen"];
    let (mut rest, mut crate_args) = (Vec::new(), Vec::new());
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let key = a.split('=').next().unwrap_or(a);
        if WITH_VALUE.contains(&key) {
            crate_args.push(a.clone());
            if !a.contains('=') {
                crate_args.push(it.next()?.clone());
            }
        } else if FLAGS.contains(&a.as_str()) {
            crate_args.push(a.clone());
        } else {
            rest.push(a.clone());
        }
    }
    (!crate_args.is_empty()).then_some((rest, crate_args))
}

/// The predicate inside each `#[cfg(..)]` or `#![cfg(..)]` of `attrs`, as written.
fn cfg_preds(attrs: &[Attr], src: &str, interner: &Interner) -> Vec<String> {
    attrs
        .iter()
        .filter(|a| a.path.len() == 1 && interner.get(a.path[0].name) == "cfg")
        .filter_map(|a| {
            let text = src.get(a.span.lo as usize..a.span.hi as usize)?;
            let open = text.find("cfg")? + 3;
            let open = open + text[open..].find('(')?;
            let close = text.rfind(')')?;
            (close > open).then(|| text[open + 1..close].trim().to_string())
        })
        .collect()
}

/// The env rustc sees for the test crate (`CARGO_MANIFEST_DIR`, `CARGO_PKG_*`),
/// from the Cargo graph as the driver reads it, so an `env!` in a test file
/// expands for test discovery too. Empty when the graph cannot load (the
/// build then reports why).
fn unit_cargo_env(key: &crate::protocol::SessionKey) -> Vec<(String, String)> {
    use crate::resolve::cargo;
    let Some(manifest) = &key.krate.manifest_path else { return Vec::new() };
    let greq = cargo::GraphRequest {
        manifest_path: manifest.clone(),
        package: None,
        features: key.features.clone(),
        default_features: key.default_features,
        all_features: key.all_features,
        target_triple: key.target_triple.clone(),
        cargo_net: key.cargo_net,
        env: None,
    };
    let Ok(graph) = cargo::load_graph(&greq) else { return Vec::new() };
    let interner = Interner::default();
    let env = crate::resolve::cfg::CfgEnv::new(&key.target_triple, &key.features, true, key.profile);
    cargo::select_unit(&graph, &greq, &key.krate.target_kind, &key.krate.target_name, &env, &interner, true).map(|u| u.cargo_env).unwrap_or_default()
}

/// Parses one crate file to find its tests: expanded when that works on
/// the file alone (a module file's macros may live elsewhere), else as written.
fn parse_file(path: &Path, src: &str, interner: &Interner, known: &Known, cargo_env: &[(String, String)]) -> Result<Ast, Diag> {
    let lexed = lexer::lex(src, FileId(0), 0, interner)?;
    let mut ctx = crate::expand::ExpandCtx::for_file(interner, known, path, src, true);
    ctx.cargo_env = cargo_env.to_vec();
    match crate::expand::expand_lexed(lexed.clone(), &ctx) {
        Ok(l) => parser::parse(&l, interner, known).or_else(|_| parser::parse(&lexed, interner, known)),
        Err(_) => parser::parse(&lexed, interner, known),
    }
}

/// The module tree walk: every test, every shim site, every file read.
struct Discovery<'a> {
    interner: &'a Interner,
    known: &'a Known,
    cargo_env: Vec<(String, String)>,
    tests: Vec<CrateTest>,
    sites: Vec<ShimSite>,
    texts: Vec<(PathBuf, String)>,
    bad: Vec<(PathBuf, String, Diag)>,
}

impl Discovery<'_> {
    /// Walks one file's module. `module` is its path from the crate root,
    /// `cfgs` the predicates of each module on that path.
    fn file(&mut self, path: &Path, owns_dir: bool, module: &[String], cfgs: &[Vec<String>]) {
        if self.texts.iter().any(|(p, _)| p == path) {
            return;
        }
        let src = match driver::read_source(path) {
            Ok(s) => s,
            Err(e) => {
                let d = Diag::new("L0503", diag::Span::default(), format!("cannot read {}: {e}", path.display()), "Check that the file exists.");
                self.bad.push((path.to_path_buf(), String::new(), d));
                return;
            }
        };
        let ast = match parse_file(path, &src, self.interner, self.known, &self.cargo_env) {
            Ok(a) => a,
            // A file whose macros live in another file (`err!` from the
            // crate root) neither expands nor parses alone: its tests are
            // found from its tokens. The build reports a real error.
            Err(d) => match lexer::lex(&src, FileId(0), 0, self.interner) {
                Ok(lexed) => {
                    let before = self.tests.len();
                    let mut cfgs = cfgs.to_vec();
                    let toks = &lexed.tokens;
                    let end = toks.iter().position(|t| t.tok == Tok::Eof).unwrap_or(toks.len());
                    let s = Scan { toks, strings: &lexed.strings, src: &src };
                    self.scan_items(&s, 0, end, path, owns_dir, module, &[], &mut cfgs);
                    if self.tests.len() > before && !module.is_empty() {
                        self.sites.push(ShimSite { path: module.to_vec(), file: path.to_path_buf(), at: src.len() });
                    }
                    self.texts.push((path.to_path_buf(), src));
                    return;
                }
                Err(_) => {
                    self.bad.push((path.to_path_buf(), src, d));
                    return;
                }
            },
        };
        let mut cfgs = cfgs.to_vec();
        if let Some(last) = cfgs.last_mut() {
            last.extend(cfg_preds(&ast.inner_attrs, &src, self.interner));
        }
        let before = self.tests.len();
        self.items(&ast.items, path, owns_dir, module, &[], &cfgs, &src, &ast);
        if self.tests.len() > before && !module.is_empty() {
            self.sites.push(ShimSite { path: module.to_vec(), file: path.to_path_buf(), at: src.len() });
        }
        self.texts.push((path.to_path_buf(), src));
    }

    #[allow(clippy::too_many_arguments)]
    fn items(&mut self, items: &[Item], file: &Path, owns_dir: bool, module: &[String], inline: &[String], cfgs: &[Vec<String>], src: &str, ast: &Ast) {
        for item in items {
            match &item.kind {
                ItemKind::Fn(def) if def.is_test => {
                    let fn_name = self.interner.get(def.name).to_string();
                    if def.self_param.is_some() || !def.params.is_empty() {
                        let d = Diag::new(
                            "L0110",
                            def.name_span,
                            format!("test function `{fn_name}` must take no arguments"),
                            format!("Change the signature to `fn {fn_name}() {{ ... }}`."),
                        );
                        self.bad.push((file.to_path_buf(), src.to_string(), d));
                        continue;
                    }
                    let returns = !def.ret.is_none_or(|t| matches!(ast.ty(t), TyExpr::Unit));
                    let (ignored, should_panic) = harness_attrs(&item.attrs, ast, self.interner);
                    let name = module.iter().chain([&fn_name]).cloned().collect::<Vec<_>>().join("::");
                    self.tests.push(CrateTest {
                        case: TestCase { name, module: module.to_vec(), fn_name, ignored, should_panic },
                        mod_cfgs: cfgs.to_vec(),
                        fn_cfgs: cfg_preds(&item.attrs, src, self.interner),
                        returns,
                    });
                }
                ItemKind::Impl(imp) => {
                    for def in imp.fns.iter().filter(|d| d.is_test) {
                        self.bad.push((file.to_path_buf(), src.to_string(), diag::unsupported(def.name_span, "#[test] functions inside impl blocks")));
                    }
                }
                ItemKind::Mod(m) => {
                    let name = self.interner.get(m.name).to_string();
                    let mut path = module.to_vec();
                    path.push(name.clone());
                    let mut cfgs = cfgs.to_vec();
                    cfgs.push(cfg_preds(&item.attrs, src, self.interner));
                    match &m.body {
                        Some(body) => {
                            cfgs.last_mut().expect("pushed above").extend(cfg_preds(&m.inner_attrs, src, self.interner));
                            let mut inl = inline.to_vec();
                            inl.push(name.clone());
                            let before = self.tests.len();
                            self.items(body, file, owns_dir, &path, &inl, &cfgs, src, ast);
                            if self.tests.len() > before {
                                let close = (m.span.hi as usize).checked_sub(1).filter(|&c| src.as_bytes().get(c) == Some(&b'}'));
                                match close {
                                    Some(c) if src.get(m.name_span.lo as usize..m.name_span.hi as usize) == Some(name.as_str()) => {
                                        self.sites.push(ShimSite { path, file: file.to_path_buf(), at: c })
                                    }
                                    _ => self.bad.push((
                                        file.to_path_buf(),
                                        src.to_string(),
                                        diag::unsupported(m.name_span, "#[test] fns in a module that a macro writes, in `lust test`"),
                                    )),
                                }
                            }
                        }
                        None => {
                            let path_attr = item
                                .attrs
                                .iter()
                                .find(|a| a.path.len() == 1 && self.interner.get(a.path[0].name) == "path")
                                .and_then(|a| attr_str(&a.input, ast));
                            // A configured-out `mod x;` need not exist: the build says when it must.
                            if let Ok(f) = crate::resolve::modules::module_file(file, owns_dir, inline, &name, path_attr.as_deref(), m.name_span) {
                                self.file(&f, path_attr.is_some(), &path, &cfgs);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// One file's tokens, for the token-level test walk (`Discovery::scan_items`).
struct Scan<'a> {
    toks: &'a [lexer::Token],
    strings: &'a [String],
    src: &'a str,
}

impl Scan<'_> {
    fn tok(&self, i: usize) -> Tok {
        self.toks.get(i).map_or(Tok::Eof, |t| t.tok)
    }
    /// The index of the closer of the opener at `i`.
    fn close_of(&self, i: usize) -> usize {
        let mut depth = 0usize;
        for j in i..self.toks.len() {
            match self.tok(j) {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return j;
                    }
                }
                _ => {}
            }
        }
        self.toks.len()
    }
    fn text(&self, lo: usize, hi: usize) -> &str {
        self.src.get(self.toks[lo].span.lo as usize..self.toks[hi].span.hi as usize).unwrap_or("")
    }
}

/// One outer attribute as the token walk keeps it: its name, its text, and
/// its first string literal (`should_panic(expected = "..")`, `path = ".."`).
struct ScanAttr {
    name: String,
    text: String,
    string: Option<String>,
}

/// The predicate of a `cfg` attribute text, as `cfg_preds` reads it.
fn cfg_pred_of(text: &str) -> Option<String> {
    let open = text.find("cfg")? + 3;
    let open = open + text[open..].find('(')?;
    let close = text.rfind(')')?;
    (close > open).then(|| text[open + 1..close].trim().to_string())
}

impl Discovery<'_> {
    /// The token-level walk over the items in `s.toks[i..end]`: modules (in
    /// files and inline), `#[test]` fns, and every other item skipped by its
    /// delimiters. For a file `parse_file` cannot read alone.
    #[allow(clippy::too_many_arguments)]
    fn scan_items(&mut self, s: &Scan, mut i: usize, end: usize, file: &Path, owns_dir: bool, module: &[String], inline: &[String], cfgs: &mut Vec<Vec<String>>) {
        let mut attrs: Vec<ScanAttr> = Vec::new();
        while i < end {
            match s.tok(i) {
                Tok::Pound if s.tok(i + 1) == Tok::Bang && s.tok(i + 2) == Tok::LBracket => {
                    // An inner attribute: a `cfg` scopes the whole module.
                    let close = s.close_of(i + 2);
                    if let (Tok::Ident(n), Some(last)) = (s.tok(i + 3), cfgs.last_mut())
                        && self.interner.get(n) == "cfg"
                        && let Some(p) = cfg_pred_of(s.text(i, close))
                    {
                        last.push(p);
                    }
                    i = close + 1;
                    continue;
                }
                Tok::Pound if s.tok(i + 1) == Tok::LBracket => {
                    let close = s.close_of(i + 1);
                    let name = match s.tok(i + 2) {
                        Tok::Ident(n) => self.interner.get(n).to_string(),
                        _ => String::new(),
                    };
                    let string = (i..close).find_map(|j| match s.tok(j) {
                        Tok::Str(k, _) => s.strings.get(k as usize).cloned(),
                        _ => None,
                    });
                    attrs.push(ScanAttr { name, text: s.text(i, close).to_string(), string });
                    i = close + 1;
                    continue;
                }
                Tok::Pub => {
                    i += 1;
                    if s.tok(i) == Tok::LParen {
                        i = s.close_of(i) + 1;
                    }
                    continue;
                }
                Tok::Const | Tok::Async | Tok::Unsafe if matches!(s.tok(i + 1), Tok::Fn | Tok::Unsafe | Tok::Extern | Tok::Async) => {
                    i += 1;
                    continue;
                }
                Tok::Mod if matches!(s.tok(i + 1), Tok::Ident(_)) => {
                    let Tok::Ident(n) = s.tok(i + 1) else { unreachable!() };
                    let name = self.interner.get(n).to_string();
                    let mut path = module.to_vec();
                    path.push(name.clone());
                    let mut sub = cfgs.clone();
                    sub.push(attrs.iter().filter(|a| a.name == "cfg").filter_map(|a| cfg_pred_of(&a.text)).collect());
                    if s.tok(i + 2) == Tok::LBrace {
                        let close = s.close_of(i + 2);
                        let mut inl = inline.to_vec();
                        inl.push(name);
                        let before = self.tests.len();
                        self.scan_items(s, i + 3, close, file, owns_dir, &path, &inl, &mut sub);
                        if self.tests.len() > before {
                            self.sites.push(ShimSite { path, file: file.to_path_buf(), at: s.toks[close].span.lo as usize });
                        }
                        i = close + 1;
                    } else {
                        let path_attr = attrs.iter().find(|a| a.name == "path").and_then(|a| a.string.clone());
                        if let Ok(f) = crate::resolve::modules::module_file(file, owns_dir, inline, &name, path_attr.as_deref(), s.toks[i].span) {
                            self.file(&f, path_attr.is_some(), &path, &sub);
                        }
                        i += 3;
                    }
                }
                Tok::Fn if matches!(s.tok(i + 1), Tok::Ident(_)) => {
                    let Tok::Ident(n) = s.tok(i + 1) else { unreachable!() };
                    let fn_name = self.interner.get(n).to_string();
                    let mut j = i + 2;
                    if s.tok(j) == Tok::Lt {
                        // Generics: a test fn has none, but skip them.
                        while j < end && s.tok(j) != Tok::LParen {
                            j += 1;
                        }
                    }
                    let params_close = if s.tok(j) == Tok::LParen { s.close_of(j) } else { j };
                    let no_params = params_close == j + 1;
                    let returns = s.tok(params_close + 1) == Tok::Arrow && !(s.tok(params_close + 2) == Tok::LParen && s.tok(params_close + 3) == Tok::RParen);
                    let mut k = params_close + 1;
                    while k < end && !matches!(s.tok(k), Tok::LBrace | Tok::Semi) {
                        k += 1;
                    }
                    let body_end = if s.tok(k) == Tok::LBrace { s.close_of(k) } else { k };
                    if attrs.iter().any(|a| a.name == "test") {
                        if no_params {
                            let ignored = attrs.iter().any(|a| a.name == "ignore");
                            let should_panic = attrs.iter().find(|a| a.name == "should_panic").map(|a| a.string.clone());
                            let name = module.iter().chain([&fn_name]).cloned().collect::<Vec<_>>().join("::");
                            self.tests.push(CrateTest {
                                case: TestCase { name, module: module.to_vec(), fn_name, ignored, should_panic },
                                mod_cfgs: cfgs.clone(),
                                fn_cfgs: attrs.iter().filter(|a| a.name == "cfg").filter_map(|a| cfg_pred_of(&a.text)).collect(),
                                returns,
                            });
                        } else {
                            let d = Diag::new("L0110", s.toks[i + 1].span, format!("test function `{fn_name}` must take no arguments"), format!("Change the signature to `fn {fn_name}() {{ ... }}`."));
                            self.bad.push((file.to_path_buf(), s.src.to_string(), d));
                        }
                    }
                    i = body_end + 1;
                }
                _ => {
                    // Any other item: to its `;` or its closing brace at this level.
                    let mut j = i;
                    while j < end {
                        match s.tok(j) {
                            Tok::Semi => break,
                            Tok::LBrace => {
                                j = s.close_of(j);
                                if s.tok(j + 1) != Tok::Semi {
                                    break;
                                }
                            }
                            Tok::LParen | Tok::LBracket => j = s.close_of(j),
                            _ => {}
                        }
                        j += 1;
                    }
                    i = j + 1;
                }
            }
            attrs.clear();
        }
    }
}

/// `all(..)` of cfg predicates (`all()` is true).
fn cfg_all(preds: &[String]) -> String {
    format!("all({})", preds.join(", "))
}

/// The call that runs a test fn in its own module: a `Result` test fails on `Err`, as rustc's
/// harness reports it (`Error: <Debug>`). The `Err` ends the test's thread as a panic does,
/// with the report as the payload and no panic hook.
fn direct_call(t: &CrateTest) -> String {
    if t.returns {
        format!("if let Err(e) = self::{}() {{ std::panic::resume_unwind(Box::new(format!(\"Error: {{e:?}}\"))) }}", t.case.fn_name)
    } else {
        format!("self::{}()", t.case.fn_name)
    }
}

/// The test binary's runner, as libtest runs a test binary: one process, and the main thread
/// starts the tests `LUST_TEST_RUN` lists, in that order, keeping `LUST_TEST_THREADS` of them
/// running. Each test runs on a thread of its own named by the test, under `catch_unwind`, so
/// its panic fails that test only, and sends its end back. The main thread appends one line
/// per event to `LUST_TEST_RESULTS`, flushed as it happens, so the parent knows which tests
/// started and ended even when the process dies: `S i` when test `i` starts, then `P i`,
/// `F i s <message>` (a string payload, `\` and newlines escaped), or `F i n` (another
/// payload). A test thread's stack is `RUST_MIN_STACK` bytes, else 8 MiB: the main thread's
/// size, as lust's C frames are larger than rustc's, not std's 2 MiB thread default.
const RUNNER: &str = r#"#[cfg(test)] fn __lust_harness_run() {
    use std::io::Write as _;
    let run: Vec<usize> = std::env::var("LUST_TEST_RUN").unwrap_or_default().split(',').filter_map(|s| s.parse().ok()).collect();
    let threads: usize = std::env::var("LUST_TEST_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(1).max(1);
    let stack: usize = std::env::var("RUST_MIN_STACK").ok().and_then(|s| s.parse().ok()).unwrap_or(8 << 20);
    let path = std::env::var("LUST_TEST_RESULTS").unwrap_or_default();
    let mut out = std::fs::OpenOptions::new().append(true).create(true).open(path).expect("lust test: the results file");
    let (tx, rx) = std::sync::mpsc::channel::<String>();
    let (mut next, mut running) = (0, 0);
    loop {
        while running < threads && next < run.len() {
            let i = run[next];
            next += 1;
            let _ = writeln!(out, "S {i}");
            let _ = out.flush();
            let tx = tx.clone();
            let spawned = std::thread::Builder::new().name(__lust_name(i).to_string()).stack_size(stack).spawn(move || {
                let line = match std::panic::catch_unwind(|| __lust_dispatch(i)) {
                    Ok(()) => format!("P {i}"),
                    Err(p) => {
                        if let Some(s) = p.downcast_ref::<&str>() {
                            format!("F {i} s {}", s.replace('\\', "\\\\").replace('\n', "\\n"))
                        } else if let Some(s) = p.downcast_ref::<String>() {
                            format!("F {i} s {}", s.replace('\\', "\\\\").replace('\n', "\\n"))
                        } else {
                            format!("F {i} n")
                        }
                    }
                };
                let _ = tx.send(line);
            });
            match spawned {
                Ok(_) => running += 1,
                Err(e) => {
                    let _ = writeln!(out, "F {i} s cannot start the test thread: {e}");
                    let _ = out.flush();
                }
            }
        }
        if running == 0 {
            break;
        }
        let Ok(line) = rx.recv() else { break };
        running -= 1;
        let _ = writeln!(out, "{line}");
        let _ = out.flush();
    }
}
"#;

/// The overlay texts: each file with its shims, the root with the dispatcher.
fn overlay(d: &Discovery, root: &Path) -> HashMap<String, String> {
    let mut adds: Vec<(PathBuf, usize, String)> = Vec::new();
    for site in &d.sites {
        let depth = site.path.len();
        let text: String = d
            .tests
            .iter()
            .enumerate()
            .filter(|(_, t)| t.case.module.starts_with(&site.path))
            .map(|(i, t)| {
                let preds: Vec<String> = t.mod_cfgs[depth..].iter().flatten().chain(&t.fn_cfgs).cloned().collect();
                let body = match t.case.module.get(depth) {
                    Some(child) => format!("self::{child}::__lust_test_{i}()"),
                    None => direct_call(t),
                };
                format!(" #[cfg(test)] #[cfg({})] #[allow(dead_code)] pub(crate) fn __lust_test_{i}() {{ {body} }}", cfg_all(&preds))
            })
            .collect();
        if !text.is_empty() {
            adds.push((site.file.clone(), site.at, text));
        }
    }
    // The root: one run fn and one flag per test, then `main`.
    let mut text = String::from("\n");
    for (i, t) in d.tests.iter().enumerate() {
        let preds: Vec<String> = t.mod_cfgs.iter().flatten().chain(&t.fn_cfgs).cloned().collect();
        let on = cfg_all(&preds);
        let call = match t.case.module.first() {
            Some(top) => format!("self::{top}::__lust_test_{i}()"),
            None => direct_call(t),
        };
        text.push_str(&format!(
            "#[cfg(test)] #[cfg({on})] fn __lust_run_{i}() {{ {call} }}\n#[cfg(test)] #[cfg(not({on}))] fn __lust_run_{i}() {{}}\n\
             #[cfg(test)] #[cfg({on})] const __LUST_ON_{i}: bool = true;\n#[cfg(test)] #[cfg(not({on}))] const __LUST_ON_{i}: bool = false;\n"
        ));
    }
    let flags: Vec<String> = (0..d.tests.len()).map(|i| format!("__LUST_ON_{i}")).collect();
    text.push_str("#[cfg(test)] fn __lust_dispatch(i: usize) {\n    match i {\n");
    for i in 0..d.tests.len() {
        text.push_str(&format!("        {i} => __lust_run_{i}(),\n"));
    }
    text.push_str("        _ => {}\n    }\n}\n#[cfg(test)] fn __lust_name(i: usize) -> &'static str {\n    match i {\n");
    for (i, t) in d.tests.iter().enumerate() {
        text.push_str(&format!("        {i} => {:?},\n", t.case.name));
    }
    text.push_str("        _ => \"\",\n    }\n}\n");
    text.push_str(&format!(
        "#[cfg(test)] fn main() {{\n    if std::env::var_os(\"LUST_TEST_LIST\").is_some() {{\n        let on: [bool; {}] = [{}];\n        \
         for (i, b) in on.iter().enumerate() {{\n            if *b {{\n                println!(\"{{i}}\");\n            }}\n        }}\n        \
         return;\n    }}\n    __lust_harness_run();\n}}\n",
        flags.len(),
        flags.join(", ")
    ));
    text.push_str(RUNNER);
    adds.push((root.to_path_buf(), usize::MAX, text));
    let mut out = HashMap::new();
    for (file, src) in &d.texts {
        let mut src = src.clone();
        let mut here: Vec<&(PathBuf, usize, String)> = adds.iter().filter(|(f, _, _)| f == file).collect();
        here.sort_by(|a, b| b.1.cmp(&a.1));
        for (_, at, add) in here {
            let at = (*at).min(src.len());
            src.insert_str(at, add);
        }
        out.insert(crate::resolve::modules::canonical_string(file), src);
    }
    out
}

/// Removes the build dir, unless `LUST_TEST_KEEP` is set: it then keeps the
/// generated C and the binary for a look at a build or runtime bug.
fn remove_dir(dir: &Path) {
    if std::env::var_os("LUST_TEST_KEEP").is_some() {
        eprintln!("lust test: kept {}", dir.display());
    } else {
        let _ = std::fs::remove_dir_all(dir);
    }
}

/// The env `cargo test` gives a test process: the runtime half of what
/// rustc saw at build time.
fn cargo_test_env(manifest: &Path) -> Vec<(String, String)> {
    let dir = manifest.parent().unwrap_or(Path::new(".")).to_string_lossy().into_owned();
    let text = std::fs::read_to_string(manifest).unwrap_or_default();
    let (name, version, _) = crate::protocol::parse_manifest(&text);
    let mut env = vec![("CARGO_MANIFEST_DIR".to_string(), dir), ("CARGO_MANIFEST_PATH".to_string(), manifest.to_string_lossy().into_owned())];
    if let Some(n) = name {
        env.push(("CARGO_CRATE_NAME".into(), n.replace('-', "_")));
        env.push(("CARGO_PKG_NAME".into(), n));
    }
    if let Some(v) = version {
        env.push(("CARGO_PKG_VERSION".into(), v));
    }
    env
}

/// `lust test` of a Cargo target. `crate_args` are the crate flags, passed
/// to `protocol::parse_args` as `lust check` and `lust build` take them.
pub(super) fn run(o: &Opts, crate_args: &[String]) -> i32 {
    let start = Instant::now();
    let mut args = vec!["test".to_string(), o.file.to_string_lossy().into_owned()];
    args.extend(crate_args.iter().cloned());
    let Some(crate::protocol::Invocation::Compile { mut req, .. }) = crate::protocol::parse_test_args(&args) else {
        eprintln!("{USAGE}");
        return 2;
    };
    let root = req.file.clone();
    let path = root.to_string_lossy().into_owned();
    let Some(manifest) = req.session.krate.manifest_path.clone() else {
        eprintln!("error: `lust test` of a Cargo target needs `--manifest-path`");
        return 2;
    };
    req.session.krate.test = true;
    req.harness = true;
    req.json = o.json;
    req.max_errors = o.max_errors;
    let fail = |text: &str| -> i32 {
        if o.json {
            print!("{text}");
            println!("{}", summary_json(&path, "", "failed", &[], 0, start));
        } else {
            eprint!("{text}");
        }
        101
    };
    let interner = Interner::default();
    let known = Known::new(&interner);
    let cargo_env = unit_cargo_env(&req.session);
    let mut d = Discovery { interner: &interner, known: &known, cargo_env, tests: Vec::new(), sites: Vec::new(), texts: Vec::new(), bad: Vec::new() };
    d.file(&root, true, &[], &[]);
    if !d.bad.is_empty() {
        let mut text = String::new();
        for (file, src, diag) in std::mem::take(&mut d.bad) {
            let mut map = SourceMap::default();
            map.add_file(&file.to_string_lossy(), &src);
            text.push_str(&diag::render(&mut [diag], &map, &src, o.json, o.max_errors));
        }
        return fail(&text);
    }
    driver::set_source_overlay(overlay(&d, &root));
    let dir = std::env::temp_dir().join(format!("lust-test-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let bin = dir.join("testbin");
    req.out = bin.clone();
    req.cmd = Cmd::Build;
    let mut session = driver::Session::new(dir.join("obj"), false, req.session.clone());
    session.caches.leak_at_exit = true;
    let build = driver::compile(&req, &mut session);
    if build.code != 0 {
        print!("{}", build.stdout);
        eprint!("{}", build.stderr);
        if o.json {
            println!("{}", summary_json(&path, "", "failed", &[], 0, start));
        }
        remove_dir(&dir);
        return 101;
    }
    let env = cargo_test_env(&manifest);
    let cwd = manifest.parent().map(Path::to_path_buf).unwrap_or_default();
    // The tests the binary holds: a configured-out test is no test.
    let listed = Command::new(&bin).env("LUST_TEST_LIST", "1").envs(env.iter().cloned()).current_dir(&cwd).output();
    let on: HashSet<usize> = match listed {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout).lines().filter_map(|l| l.trim().parse().ok()).collect(),
        _ => {
            remove_dir(&dir);
            return fail("error: the test binary did not list its tests\n");
        }
    };
    // libtest's selection: the filters, then `--ignored` (only the ignored tests, which then
    // run) or `--include-ignored` (all run), then the tests sorted by name.
    let compiled: Vec<(usize, &CrateTest)> = d.tests.iter().enumerate().filter(|(i, _)| on.contains(i)).collect();
    let mut cases: Vec<(usize, TestCase)> = compiled
        .iter()
        .filter(|(_, t)| o.selects(&t.case.name) && (!o.ignored || t.case.ignored))
        .map(|(i, t)| {
            let mut c = t.case.clone();
            c.ignored &= !(o.ignored || o.include_ignored);
            (*i, c)
        })
        .collect();
    cases.sort_by(|a, b| a.1.name.cmp(&b.1.name));
    let filtered_out = compiled.len() - cases.len();
    if o.list {
        for (_, t) in &cases {
            println!("{}: test", t.name);
        }
        println!("\n{} tests", cases.len());
        remove_dir(&dir);
        return 0;
    }
    let threads = o
        .threads
        .or_else(|| std::env::var("RUST_TEST_THREADS").ok().and_then(|v| v.parse().ok()).filter(|&n: &usize| n > 0))
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()));
    let run = InProcess { bin: &bin, dir: &dir, cwd: &cwd, env: &env, threads, timeout: o.timeout };
    let code = report(&run, &cases, o, &path, filtered_out, start);
    remove_dir(&dir);
    code
}

/// One test binary run the libtest way (`RUNNER`).
struct InProcess<'a> {
    bin: &'a Path,
    dir: &'a Path,
    cwd: &'a Path,
    env: &'a [(String, String)],
    threads: usize,
    timeout: Duration,
}

/// How one test ended, as the runner reports it.
enum End {
    Pass,
    /// A panic (or an `Err`) with a string payload, or `None` for another payload.
    Panic(Option<String>),
    /// No end line: the process died or was stopped while the test ran.
    Died(String),
    Timeout,
}

impl InProcess<'_> {
    /// Runs `order` (test indices) and returns each test's end, in finishing order. A test
    /// running past the timeout stops the process: it times out, and the tests not yet done
    /// run again in a new process. When the process dies, the tests it was running fail and
    /// the rest run in a new one, so one crash fails one test (or the few beside it) as a
    /// libtest crash would fail them all.
    fn run(&self, order: &[usize], mut on_end: impl FnMut(usize, End, f64)) {
        let mut left: Vec<usize> = order.to_vec();
        // The tests a dying process was running beside others: each runs again alone, so the
        // one that ends the process fails and the others get their own result.
        let mut solo: Vec<usize> = Vec::new();
        let mut round = 0;
        while !left.is_empty() || !solo.is_empty() {
            round += 1;
            let results = self.dir.join(format!("results-{round}"));
            let _ = std::fs::remove_file(&results);
            let (batch, threads, alone) = match solo.is_empty() {
                true => (left.clone(), self.threads, false),
                false => (vec![solo.remove(0)], 1, true),
            };
            let list: Vec<String> = batch.iter().map(|i| i.to_string()).collect();
            // The tests' own output is not captured: it goes to stderr, as under
            // `--nocapture`, and stdout keeps libtest's report.
            let err = || std::io::stderr().as_fd().try_clone_to_owned().map(Stdio::from).unwrap_or_else(|_| Stdio::null());
            let mut cmd = Command::new(self.bin);
            cmd.current_dir(self.cwd).envs(self.env.iter().cloned()).stdin(Stdio::null()).stdout(err()).stderr(err());
            cmd.env("LUST_TEST_RUN", list.join(",")).env("LUST_TEST_THREADS", threads.to_string()).env("LUST_TEST_RESULTS", &results);
            let mut child = match cmd.spawn() {
                Ok(c) => c,
                Err(e) => {
                    for i in left.drain(..).chain(solo.drain(..)).chain(alone.then_some(batch[0])) {
                        on_end(i, End::Died(format!("cannot run the test binary: {e}")), 0.0);
                    }
                    return;
                }
            };
            let (mut read, mut pending, mut moved) = (0usize, String::new(), false);
            let mut started: Vec<(usize, Instant)> = Vec::new();
            let mut done: HashSet<usize> = HashSet::new();
            let feed = |pending: &mut String, read: &mut usize, started: &mut Vec<(usize, Instant)>, done: &mut HashSet<usize>, on_end: &mut dyn FnMut(usize, End, f64)| {
                let Ok(text) = std::fs::read(&results) else { return };
                if text.len() <= *read {
                    return;
                }
                pending.push_str(&String::from_utf8_lossy(&text[*read..]));
                *read = text.len();
                while let Some(nl) = pending.find('\n') {
                    let line: String = pending.drain(..=nl).collect();
                    let mut parts = line.trim_end_matches('\n').splitn(4, ' ');
                    let (Some(kind), Some(Ok(i))) = (parts.next(), parts.next().map(str::parse::<usize>)) else { continue };
                    if kind == "S" {
                        started.push((i, Instant::now()));
                        continue;
                    }
                    let ms = started.iter().find(|(s, _)| *s == i).map_or(0.0, |(_, t)| super::millis(*t));
                    started.retain(|(s, _)| *s != i);
                    done.insert(i);
                    let end = match (kind, parts.next(), parts.next()) {
                        ("P", _, _) => End::Pass,
                        (_, Some("s"), m) => End::Panic(Some(unescape(m.unwrap_or("")))),
                        _ => End::Panic(None),
                    };
                    on_end(i, end, ms);
                }
            };
            let status = loop {
                feed(&mut pending, &mut read, &mut started, &mut done, &mut on_end);
                if let Some(&(late, t)) = started.iter().find(|(_, t)| t.elapsed() > self.timeout) {
                    let _ = child.kill();
                    let _ = child.wait();
                    on_end(late, End::Timeout, super::millis(t));
                    done.insert(late);
                    // The others running beside it were stopped, not failed: they run again.
                    break None;
                }
                match child.try_wait() {
                    Ok(Some(s)) => break Some(s),
                    Ok(None) => std::thread::sleep(Duration::from_millis(2)),
                    Err(_) => break child.wait().ok(),
                }
            };
            if let Some(s) = status {
                feed(&mut pending, &mut read, &mut started, &mut done, &mut on_end);
                let why = match s.code() {
                    Some(c) => format!("the test process exited with code {c} while this test ran"),
                    None => format!("the test process was killed ({s}) while this test ran"),
                };
                if alone || started.len() == 1 {
                    for (i, t) in started.drain(..) {
                        on_end(i, End::Died(why.clone()), super::millis(t));
                        done.insert(i);
                    }
                } else {
                    moved = true;
                    solo.extend(started.drain(..).map(|(i, _)| i));
                }
            }
            let progressed = !done.is_empty() || moved;
            left.retain(|i| !done.contains(i) && !solo.contains(i));
            if !progressed {
                // A process that ends before it starts a test would end so again.
                let never = if alone { batch } else { std::mem::take(&mut left) };
                for i in never {
                    on_end(i, End::Died("the test process ended before this test started".into()), 0.0);
                }
            }
        }
    }
}

/// Undoes the runner's escapes (`\\` and `\n`).
fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        match (c, c == '\\') {
            (_, true) => match chars.next() {
                Some('n') => out.push('\n'),
                Some(other) => out.push(other),
                None => out.push('\\'),
            },
            _ => out.push(c),
        }
    }
    out
}

/// Runs `cases` (sorted by name) and prints libtest's report: `running N tests`, one
/// `test <name> ... ok|FAILED|ignored` line per test as it ends, the failures, and the
/// `test result:` line. Returns 0, or 101 when a test failed.
fn report(run: &InProcess, cases: &[(usize, TestCase)], o: &Opts, path: &str, filtered_out: usize, start: Instant) -> i32 {
    if !o.json {
        println!("\nrunning {} test{}", cases.len(), if cases.len() == 1 { "" } else { "s" });
    }
    let mut outcomes: Vec<Outcome> = Vec::new();
    let mut failures: Vec<(String, String)> = Vec::new();
    let print = |o: &Opts, case: &TestCase, out: &Outcome| {
        if o.json {
            println!(
                "{{\"schema\":{},\"kind\":\"test\",\"name\":{},\"status\":\"{}\",\"duration_ms\":{:.3},\"exit_code\":null,\"stdout\":\"\",\"stderr\":{}}}",
                diag::SCHEMA,
                diag::json_str(&out.name),
                out.status,
                out.duration_ms,
                diag::json_str(&out.stderr)
            );
        } else {
            let word = match out.status {
                "pass" => "ok",
                "ignored" => "ignored",
                _ => "FAILED",
            };
            let mark = if case.should_panic.is_some() { " - should panic" } else { "" };
            println!("test {}{mark} ... {word}", out.name);
        }
    };
    for (_, c) in cases.iter().filter(|(_, c)| c.ignored) {
        let out = Outcome { name: c.name.clone(), status: "ignored", duration_ms: 0.0, exit_code: None, stdout: String::new(), stderr: String::new() };
        print(o, c, &out);
        outcomes.push(out);
    }
    let order: Vec<usize> = cases.iter().filter(|(_, c)| !c.ignored).map(|(i, _)| *i).collect();
    run.run(&order, |i, end, ms| {
        let Some((_, c)) = cases.iter().find(|(j, _)| *j == i) else { return };
        // libtest's verdict, with its notes for a `should_panic` miss.
        let (status, detail) = match (&c.should_panic, end) {
            (_, End::Timeout) => ("timeout", format!("the test ran past the {:?} timeout (`--timeout`)", run.timeout)),
            (_, End::Died(why)) => ("fail", why),
            (None, End::Pass) => ("pass", String::new()),
            (None, End::Panic(m)) => ("fail", m.unwrap_or_else(|| "Box<dyn Any>".into())),
            (Some(_), End::Pass) => ("fail", "note: test did not panic as expected".into()),
            (Some(None), End::Panic(_)) => ("pass", String::new()),
            (Some(Some(want)), End::Panic(Some(m))) if m.contains(want.as_str()) => ("pass", String::new()),
            (Some(Some(want)), End::Panic(Some(m))) => {
                ("fail", format!("note: panic did not contain expected string\n      panic message: {m:?}\n expected substring: {want:?}"))
            }
            (Some(Some(want)), End::Panic(None)) => {
                ("fail", format!("note: expected panic with string value,\n found non-string value\n     expected substring: {want:?}"))
            }
        };
        let out = Outcome { name: c.name.clone(), status, duration_ms: ms, exit_code: None, stdout: String::new(), stderr: detail.clone() };
        print(o, c, &out);
        if status != "pass" {
            failures.push((c.name.clone(), detail));
        }
        outcomes.push(out);
    });
    let failed = outcomes.iter().filter(|x| matches!(x.status, "fail" | "timeout")).count();
    if o.json {
        println!("{}", summary_json(path, "", "ok", &outcomes, filtered_out, start));
    } else {
        if !failures.is_empty() {
            failures.sort();
            println!("\nfailures:\n");
            for (name, detail) in &failures {
                println!("---- {name} stdout ----\n{detail}\n");
            }
            println!("\nfailures:");
            for (name, _) in &failures {
                println!("    {name}");
            }
        }
        let count = |s: &str| outcomes.iter().filter(|x| x.status == s).count();
        println!(
            "\ntest result: {}. {} passed; {} failed; {} ignored; 0 measured; {} filtered out; finished in {:.2}s\n",
            if failed == 0 { "ok" } else { "FAILED" },
            count("pass"),
            failed,
            count("ignored"),
            filtered_out,
            start.elapsed().as_secs_f64()
        );
    }
    if failed == 0 { 0 } else { 101 }
}
