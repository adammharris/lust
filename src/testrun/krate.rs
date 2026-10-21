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
// Each test runs in the package dir with Cargo's runtime env (`CARGO_MANIFEST_DIR`, ...), as
// under `cargo test`. Shims go before a closing `}` or at the end of a file, with no newline
// before the end, so lines (and panic locations) still match the files.
use super::{Opts, TestCase, USAGE, attr_str, harness_attrs, summary_json};
use crate::ast::{Ast, Attr, Item, ItemKind, TyExpr};
use crate::diag::{self, Diag, FileId, SourceMap};
use crate::driver::{self, Cmd};
use crate::intern::{Interner, Known};
use crate::{lexer, parser};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

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
            Err(d) => {
                self.bad.push((path.to_path_buf(), src, d));
                return;
            }
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

/// `all(..)` of cfg predicates (`all()` is true).
fn cfg_all(preds: &[String]) -> String {
    format!("all({})", preds.join(", "))
}

/// The call that runs a test fn in its own module: a `Result` test fails on `Err`, as rustc's
/// harness reports it (`Error: <Debug>`).
fn direct_call(t: &CrateTest) -> String {
    if t.returns {
        format!("if let Err(e) = self::{}() {{ eprintln!(\"Error: {{e:?}}\"); std::process::exit(101) }}", t.case.fn_name)
    } else {
        format!("self::{}()", t.case.fn_name)
    }
}

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
    text.push_str(&format!(
        "#[cfg(test)] fn main() {{\n    if std::env::var_os(\"LUST_TEST_LIST\").is_some() {{\n        let on: [bool; {}] = [{}];\n        \
         for (i, b) in on.iter().enumerate() {{\n            if *b {{\n                println!(\"{{i}}\");\n            }}\n        }}\n        \
         return;\n    }}\n    let n = std::env::args().count();\n    if n == 1 {{\n",
        flags.len(),
        flags.join(", ")
    ));
    for (i, _) in d.tests.iter().enumerate().filter(|(_, t)| !t.case.ignored) {
        text.push_str(&format!("        __lust_run_{i}();\n"));
    }
    for i in 0..d.tests.len() {
        text.push_str(&format!("    }} else if n == {} {{\n        __lust_run_{i}();\n", i + 2));
    }
    text.push_str("    }\n}\n");
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
    let compiled: Vec<(usize, &CrateTest)> = d.tests.iter().enumerate().filter(|(i, _)| on.contains(i)).collect();
    let selected: Vec<(usize, &CrateTest)> =
        compiled.iter().copied().filter(|(_, t)| o.filter.as_ref().is_none_or(|f| t.case.name.contains(f.as_str()))).collect();
    let filtered_out = compiled.len() - selected.len();
    if o.list {
        for (_, t) in &selected {
            println!("{}: test", t.case.name);
        }
        println!("\n{} tests", selected.len());
        remove_dir(&dir);
        return 0;
    }
    let cases: Vec<(usize, TestCase)> = selected.iter().map(|(i, t)| (*i, t.case.clone())).collect();
    let run = super::Run { bin: &bin, path: &path, hash: "", cwd: Some(&cwd), env: &env, rename: None };
    let code = super::run_cases(&run, &cases, o, filtered_out, start);
    remove_dir(&dir);
    code
}
