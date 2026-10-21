// Command-line parsing and the daemon wire protocol. Shared by the thin `lust` client and the
// `lust-core` compiler, so the client stays small and starts fast.
//
// Wire format. Request: a header line with no user data in it,
//   cmd json timings debug max_errors test default_features all_features
//   panic_abort overflow_checks debug_assertions feature_count env_count offline locked build
// followed by length-prefixed fields, each as "<byte len>\n<bytes>": file, out,
// emit_c, then the crate selector (package id, manifest path, target kind,
// target name, crate root, target triple), then one field per feature,
// then the client's view (see `Client`): the shown root path (len 0 for None),
// and when the header's env count is not "-", that many name and value fields.
// Length prefixes carry any byte a path can hold, including tabs and newlines; emit_c
// and the manifest path use len 0 for None. Run arguments never cross the wire
// (see `Request::run_args`). The default socket name holds the build hash, but an
// explicit `LUST_DAEMON_SOCKET` can name a daemon of another build, so both directions
// carry `build_id`: a daemon that reads another build's request answers and exits
// (`ReadError::OtherBuild`), and a client drops an answer from another build or from a
// daemon that predates the field (`request`). A stale compiler never answers warm.
// Response: "<code> <stdout len> <stderr len> <build>\n" followed by the two byte strings.
// Both binaries include this module and each uses only part of it.
#![allow(dead_code)]

use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Cmd {
    Check,
    Build,
}

/// One crate: one target of one package (docs/ARCH.md section 1.1). A crate is
/// the unit of daemon sessions. `root` is the crate root file; today it is the
/// file the user named, because a crate is one file until W-RESOLVE loads
/// modules. `package_id` is the identity string the stable crate hash covers
/// (section 1.7): a synthetic `file:<path>` for a single-file program, or a
/// Cargo-shaped stand-in until W-RESOLVE reads real package ids from Cargo
/// metadata. `test` marks the same target built as a test crate (`lust test`):
/// test and non-test defs never share identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CrateKey {
    pub package_id: String,
    pub manifest_path: Option<PathBuf>,
    pub target_kind: String,
    pub target_name: String,
    pub root: PathBuf,
    pub test: bool,
}

/// The profile values that can change program output (section 1.1). They enter
/// every session and cache key, so a profile change never reuses a session or
/// a disk entry built under other flags. A single-file compile uses `DEV_UNWIND`
/// (plain `rustc file.rs`: panics unwind); a Cargo package (`--manifest-path`
/// and the other crate flags) uses the dev profile Cargo would apply
/// (`dev_profile`, also unwinding unless it says `panic = "abort"`), with
/// `-C panic=` on top.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProfileFlags {
    pub panic_abort: bool,
    pub overflow_checks: bool,
    pub debug_assertions: bool,
}

impl ProfileFlags {
    /// The dev flags with `-C panic=abort`.
    pub const DEV: ProfileFlags = ProfileFlags { panic_abort: true, overflow_checks: true, debug_assertions: true };
    /// rustc's and Cargo's dev defaults (panics unwind): a single-file compile
    /// and a Cargo dev profile that does not set `panic`.
    pub const DEV_UNWIND: ProfileFlags = ProfileFlags { panic_abort: false, ..ProfileFlags::DEV };
}

/// Daemon routing key (section 1.8): the crate plus the resolver inputs that
/// select how it is built (features with the default-feature policy, target
/// triple, profile flags). Two feature selections or two targets of one crate
/// get two sessions. The Cargo graph key and adapter versions join this key
/// with W-RESOLVE; `features` is sorted and deduped at construction.
/// `target_triple` empty means the host.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SessionKey {
    pub krate: CrateKey,
    pub features: Vec<String>,
    pub default_features: bool,
    pub all_features: bool,
    pub target_triple: String,
    pub profile: ProfileFlags,
    pub cargo_net: CargoNet,
}

/// How the Cargo runs lust starts may use the network: `--offline` and
/// `--locked` (`--frozen` is both), as Cargo takes them. The client fills it
/// from its own flags and `CARGO_NET_OFFLINE`, so a daemon started from
/// another environment still runs Cargo the way the caller asked. Cargo
/// reads `net.offline` from its config files itself.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct CargoNet {
    pub offline: bool,
    pub locked: bool,
}

impl CargoNet {
    /// The Cargo flags for this mode.
    pub fn args(self) -> impl Iterator<Item = &'static str> {
        [(self.offline, "--offline"), (self.locked, "--locked")].into_iter().filter_map(|(on, flag)| on.then_some(flag))
    }
}

impl SessionKey {
    /// The synthetic one-crate package for a single-file program: the file
    /// path is the package identity, the target is a `bin` named by the file
    /// stem, and `test` marks a `lust test` harness build. This keeps
    /// `lust check file.rs` unchanged for users (section 9.2, S6).
    pub fn synthetic(file: &Path, test: bool) -> SessionKey {
        let path = file.to_string_lossy();
        let stem = path.rsplit('/').next().unwrap_or(&path);
        let stem = stem.strip_suffix(".rs").unwrap_or(stem);
        SessionKey {
            krate: CrateKey {
                package_id: format!("file:{path}"),
                manifest_path: None,
                target_kind: "bin".into(),
                target_name: stem.into(),
                root: file.to_path_buf(),
                test,
            },
            features: Vec::new(),
            default_features: true,
            all_features: false,
            target_triple: String::new(),
            profile: ProfileFlags::DEV_UNWIND,
            cargo_net: CargoNet::default(),
        }
    }

    /// One-line form naming every field. Daemon logs and the cold disk cache
    /// key both use it, so a field that is not in this text is not in either.
    pub fn describe(&self) -> String {
        let b = |x: bool| if x { "1" } else { "0" };
        let manifest = self.krate.manifest_path.as_ref().map_or_else(|| "-".to_string(), |p| p.to_string_lossy().into_owned());
        format!(
            "pkg={} manifest={} {}:{} root={} test={} features=[{}] default_features={} all_features={} target={} panic_abort={} overflow_checks={} debug_assertions={} offline={} locked={}",
            self.krate.package_id,
            manifest,
            self.krate.target_kind,
            self.krate.target_name,
            self.krate.root.display(),
            b(self.krate.test),
            self.features.join(","),
            b(self.default_features),
            b(self.all_features),
            if self.target_triple.is_empty() { "host" } else { &self.target_triple },
            b(self.profile.panic_abort),
            b(self.profile.overflow_checks),
            b(self.profile.debug_assertions),
            b(self.cargo_net.offline),
            b(self.cargo_net.locked),
        )
    }
}

/// Sorts and dedupes a feature list, so `--features b,a` and `--features a,b`
/// select the same session. Used wherever a `SessionKey` is built from flags.
fn sort_features(features: &mut Vec<String>) {
    features.sort();
    features.dedup();
}

/// A small self-contained string hash for graph keys. This module is also
/// compiled into the thin client, which has no other hash helper.
fn hash_bytes(seed: u64, parts: &[&[u8]]) -> u64 {
    let mut h = seed ^ 0x51_7C_C1_B7_27_22_0A_95;
    for part in parts {
        h = (h.rotate_left(5) ^ part.len() as u64).wrapping_mul(0x51_7C_C1_B7_27_22_0A_95);
        for &b in *part {
            h = (h.rotate_left(5) ^ b as u64).wrapping_mul(0x51_7C_C1_B7_27_22_0A_95);
        }
    }
    h ^= h >> 29;
    h
}

/// The Cargo graph key for one session selection (docs/ARCH.md section
/// 1.1): the full resolver input, not only file hashes. Covers the
/// manifest bytes (the session's manifest, or the nearest one above the
/// crate root), the nearest `Cargo.lock` at or above the manifest, the
/// `.cargo/config.toml` (and legacy `.cargo/config`) chain from the
/// manifest dir to the filesystem root, and the whole session selection
/// (requested package and target, features with the default-feature
/// policy, target triple, profile flags) through `describe`. Hashing
/// every workspace `Cargo.toml` joins when W-RESOLVE reads real graph
/// data from Cargo; until then the lock file covers workspace member
/// and version edits in practice. Daemon routing compares this key per
/// request: an edit to any covered file routes the crate to a fresh
/// session instead of reusing state resolved under the old graph. The
/// cold disk cache mixes it into the whole-request key for the same
/// reason.
/// The manifest directory of a session selection: its named manifest's
/// directory, or the nearest manifest above the crate root. Build
/// script lookup and graph keys both anchor here, so every routing
/// layer agrees on which package a session belongs to. A synthetic
/// single-file crate (`file:` package id, no manifest named) has no
/// manifest anchor: a file that merely sits inside some other package
/// (a test fixture under a repo root, say) must not inherit that
/// package's graph or build script.
pub fn manifest_dir(session: &SessionKey) -> Option<PathBuf> {
    match &session.krate.manifest_path {
        Some(p) => p.parent().map(Path::to_path_buf),
        None if session.krate.package_id.starts_with("file:") => None,
        None => find_manifest(&session.krate.root).map(|m| m.dir),
    }
}

pub fn graph_key(session: &SessionKey) -> u64 {
    let mut h = hash_bytes(1, &[session.describe().as_bytes()]);
    for (label, path) in graph_files(session) {
        if let Ok(bytes) = std::fs::read(&path) {
            h = hash_bytes(h, &[label.as_bytes(), &bytes]);
        }
    }
    h
}

/// The files `graph_key` covers, each with the label it hashes under, in
/// hash order: the manifest, then per directory up to the root its
/// `.cargo/config.toml`, `.cargo/config` and `.lust.toml`, and the nearest
/// `Cargo.lock`. Only files that exist. The daemon's guard counts them as
/// compile inputs too.
pub fn graph_files(session: &SessionKey) -> Vec<(&'static str, PathBuf)> {
    let manifest_path = match &session.krate.manifest_path {
        Some(p) => Some(p.clone()),
        // Same synthetic-crate rule as `manifest_dir`.
        None if session.krate.package_id.starts_with("file:") => None,
        None => find_manifest(&session.krate.root).map(|m| m.path),
    };
    let mut files = Vec::new();
    let Some(manifest) = manifest_path else { return files };
    if manifest.is_file() {
        files.push(("manifest", manifest.clone()));
    }
    let mut dir = manifest.parent();
    let mut lock_found = false;
    while let Some(d) = dir {
        for name in [".cargo/config.toml", ".cargo/config", ".lust.toml"] {
            if d.join(name).is_file() {
                files.push((name, d.join(name)));
            }
        }
        if !lock_found && d.join("Cargo.lock").is_file() {
            files.push(("lock", d.join("Cargo.lock")));
            lock_found = true;
        }
        dir = d.parent();
    }
    files
}

/// The host target triple, for the tier-1 hosts lust runs on. Empty when the
/// host is not in the table (an explicit `--target` then never matches it).
pub fn host_triple() -> &'static str {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
        ("aarch64", "linux") => "aarch64-unknown-linux-gnu",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("aarch64", "macos") => "aarch64-apple-darwin",
        _ => "",
    }
}

#[derive(Clone)]
pub struct Request {
    pub cmd: Cmd,
    /// The crate this request names and the session it routes to. `file` is
    /// the file the user named; today it is also `session.krate.root`.
    pub session: SessionKey,
    pub file: PathBuf,
    pub out: PathBuf,
    pub json: bool,
    pub timings: bool,
    pub debug: bool,
    pub emit_c: Option<PathBuf>,
    /// Cap on shown diagnostics (0 means no cap). See `diag::render`.
    pub max_errors: usize,
    /// For `lust run`: the program's arguments (without argv[0]), so a one-shot compile can
    /// run a small program in memory instead of building a file. The daemon wire format does
    /// not carry this (read_request sets None): a daemon build still writes the executable and
    /// the client runs it.
    pub run_args: Option<Vec<String>>,
    /// For `lust test`: the file gets a generated `main`, so a missing user `main` is not
    /// an error. The daemon wire format does not carry this (decode sets false): `lust
    /// test` compiles in its own process.
    pub harness: bool,
    /// Build with the external C compiler backend (src/cc.rs) for
    /// `session.target_triple` instead of tcc, the release driver form.
    /// The daemon wire format does not carry this (decode sets false):
    /// release builds always compile cold, in the client-spawned
    /// `lust-core`, never warm.
    pub cc: bool,
    pub client: Client,
}

/// What a compile reads from the process that asked for it, not from the compiler process:
/// the environment `env!` sees and the root file path as the user typed it (`file!`, `dbg!`,
/// panic locations show paths as rustc shows the path it was given). A daemon serves many
/// clients, so each request carries its own. Default (None, None) reads this process's
/// environment and shows absolute paths: internal requests and tests.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct Client {
    pub env: Option<Vec<(String, String)>>,
    pub shown: Option<PathBuf>,
}

impl Client {
    /// The calling process's view: its environment (UTF-8 entries only, as `env!` reads
    /// them) and `typed`, the root file path as written on the command line.
    pub fn current(typed: &Path) -> Client {
        let env = std::env::vars_os().filter_map(|(k, v)| Some((k.into_string().ok()?, v.into_string().ok()?))).collect();
        Client { env: Some(env), shown: Some(typed.to_path_buf()) }
    }
}

#[derive(Clone, Default)]
pub struct Response {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
    /// The program already ran in memory; `code` is its exit code. Do not run `out` again.
    pub ran: bool,
}

pub enum Invocation {
    Daemon,
    /// `run` is a build, then the client runs the program with `args`.
    Compile {
        req: Request,
        run: bool,
        args: Vec<String>,
    },
    /// `lust build --release --target <triple>...`: the lust release driver.
    /// One cold request per target (each `cc: true`, its own session and
    /// output path); `lust-core` runs them in order and never hands them
    /// to the daemon. Err: the named profile cannot be read (undefined, or
    /// an `inherits` cycle), the error to print.
    ReleaseCc {
        reqs: Result<Vec<Request>, String>,
    },
    /// `lust build --release` / `--profile <name>`: hand the file to Cargo or rustc.
    /// Handled in the client process; never sent to the daemon.
    Release {
        file: PathBuf,
        out: Option<PathBuf>,
        profile: Option<String>,
        debug: bool,
        net: CargoNet,
    },
    /// `lust check --rustc`: run the real rustc as an oracle. Never sent to the daemon.
    RustcCheck {
        file: PathBuf,
    },
}

pub const USAGE: &str = "usage: lust <check|build|run> <file.rs> [--json] [--max-errors N] [--timings] [-o out] [-g] [--emit-c prefix] [-- args]\n       lust <check|build|run> <file.rs> [--manifest-path <Cargo.toml>] [--package <name>] [--bin <name> | --lib] [--features <a,b>] [--no-default-features] [--all-features] [--target <triple>] [-C panic=unwind|abort] [-C overflow-checks=on|off] [-C debug-assertions=on|off] [--offline] [--locked] [--frozen]\n       lust build <file.rs> --release | --profile <name> [-o out] [--offline] [--locked] [--frozen]\n       lust build <file.rs> --release | --profile <name> --target <triple> [--target <triple>...] [crate flags] [-o out-or-dir] (lust release driver: zig cc)\n       lust check <file.rs> --rustc\n       lust test <file.rs> [filter] [--json] [--timeout SECONDS] [--max-errors N]\n       lust explain <L####>\n       lust expand <file.rs>\n       lust capabilities [--json]\n       lust daemon\n       lust --version";

/// Crate-selection flags from the command line, before defaults are filled in.
#[derive(Clone, Default)]
struct CrateFlags {
    manifest_path: Option<PathBuf>,
    package: Option<String>,
    bin: Option<String>,
    lib: bool,
    features: Vec<String>,
    no_default_features: bool,
    all_features: bool,
    target_triple: Option<String>,
}

impl CrateFlags {
    /// True when any crate-selection flag was given. Release and rustc-oracle
    /// invocations reject these instead of silently ignoring them.
    fn any(&self) -> bool {
        self.manifest_path.is_some()
            || self.package.is_some()
            || self.bin.is_some()
            || self.lib
            || !self.features.is_empty()
            || self.no_default_features
            || self.all_features
            || self.target_triple.is_some()
    }
}

/// Project dev feature config (docs/dev-features.md). `dev-features` is the
/// exact feature list for lust dev builds. `dev-exclude-features` names
/// entries to remove from the package `default` list. Release builds via
/// Cargo never read this config.
#[derive(Clone, Debug, Default)]
struct LustConfig {
    dev_features: Option<Vec<String>>,
    dev_exclude_features: Option<Vec<String>>,
}

impl LustConfig {
    fn any(&self) -> bool {
        self.dev_features.is_some() || self.dev_exclude_features.is_some()
    }
}

/// Quoted strings in one TOML array value. The value may span lines up to
/// the closing `]`. Comments have no quotes in the configs we read.
fn toml_str_array(value: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = value.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' || c == '\'' {
            let mut s = String::new();
            for d in chars.by_ref() {
                if d == c {
                    break;
                }
                s.push(d);
            }
            out.push(s);
        }
        if c == ']' {
            break;
        }
    }
    out
}

/// One array key under one TOML section (`""` means top level, for
/// `.lust.toml`). Section-gated like `parse_manifest`.
fn toml_array_in(text: &str, section: &str, key: &str) -> Option<Vec<String>> {
    let mut cur = "";
    let mut lines = text.lines().peekable();
    while let Some(raw) = lines.next() {
        let line = raw.trim();
        if line.starts_with('[') {
            cur = line.trim_matches(|c| c == '[' || c == ']');
            continue;
        }
        if cur != section || line.split('=').next().is_none_or(|k| k.trim() != key) {
            continue;
        }
        let mut value = line.split_once('=').map_or("", |(_, v)| v).to_string();
        while !value.contains(']') {
            match lines.next() {
                Some(next) => {
                    value.push(' ');
                    value.push_str(next.trim());
                }
                None => break,
            }
        }
        return Some(toml_str_array(&value));
    }
    None
}

/// The lust config in one TOML text: `package.metadata.lust`, then
/// `workspace.metadata.lust`, then top-level keys (a `.lust.toml` file).
fn lust_config_in(text: &str) -> LustConfig {
    for section in ["package.metadata.lust", "workspace.metadata.lust", ""] {
        let cfg = LustConfig {
            dev_features: toml_array_in(text, section, "dev-features"),
            dev_exclude_features: toml_array_in(text, section, "dev-exclude-features"),
        };
        if cfg.any() {
            return cfg;
        }
    }
    LustConfig::default()
}

/// Finds the project lust config for one crate: the crate manifest, then
/// ancestor manifests (a workspace root holds `workspace.metadata.lust`),
/// then the nearest `.lust.toml` at or above the manifest directory (or
/// the file directory when no manifest names the crate). Returns the
/// config and the manifest text that owns the `[features]` table, when
/// one was read.
fn find_lust_config(file: &Path, key: &SessionKey) -> (LustConfig, Option<String>) {
    let manifest = key.krate.manifest_path.clone().or_else(|| find_manifest(file).map(|m| m.path));
    let mut own_text = None;
    if let Some(mp) = &manifest {
        if let Ok(text) = std::fs::read_to_string(mp) {
            own_text = Some(text.clone());
            let cfg = lust_config_in(&text);
            if cfg.any() {
                return (cfg, own_text);
            }
        }
        for anc in ancestor_manifests(mp) {
            if let Ok(text) = std::fs::read_to_string(&anc) {
                let cfg = lust_config_in(&text);
                if cfg.any() {
                    return (cfg, own_text);
                }
            }
        }
    }
    let start = manifest.as_deref().and_then(|p| p.parent()).or_else(|| file.parent());
    let mut dir = start;
    while let Some(d) = dir {
        if let Ok(text) = std::fs::read_to_string(d.join(".lust.toml")) {
            let cfg = lust_config_in(&text);
            if cfg.any() {
                return (cfg, own_text);
            }
        }
        dir = d.parent();
    }
    (LustConfig::default(), own_text)
}

/// Cargo.toml files above `manifest` (not including it), nearest first.
fn ancestor_manifests(manifest: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut dir = manifest.parent().and_then(|d| d.parent());
    while let Some(d) = dir {
        let cand = d.join("Cargo.toml");
        if cand.exists() {
            out.push(cand);
        }
        dir = d.parent();
    }
    out
}

/// Applies the project dev config to a session key. Skipped when the
/// command line named a feature selection: flags always win. The result
/// is stored as the effective selection itself (`features` plus
/// `default_features = false`), so the daemon session key, `describe`,
/// and every cache key carry the effective features.
fn apply_dev_config(key: &mut SessionKey, file: &Path) {
    let (cfg, manifest_text) = find_lust_config(file, key);
    if let Some(list) = cfg.dev_features {
        key.features = list;
    } else if let Some(exclude) = cfg.dev_exclude_features {
        let defaults = manifest_text.as_deref().and_then(|t| toml_array_in(t, "features", "default")).unwrap_or_default();
        key.features = defaults.into_iter().filter(|f| !exclude.contains(f)).collect();
    } else {
        return;
    }
    sort_features(&mut key.features);
    key.default_features = false;
    key.all_features = false;
}

/// Builds the session key for a dev request from the crate flags. With no
/// manifest or package flag the crate is synthetic (one file). With one, the
/// package identity comes from the manifest text (`find_manifest` below)
/// until W-RESOLVE reads real package ids from Cargo metadata. The file is
/// still the crate root: `lust check file.rs` keeps its meaning.
fn session_key_for(file: &Path, flags: CrateFlags, net: CargoNet) -> SessionKey {
    let mut key = SessionKey::synthetic(file, false);
    let mut features = flags.features;
    sort_features(&mut features);
    key.features = features;
    key.default_features = !flags.no_default_features;
    key.all_features = flags.all_features;
    key.target_triple = flags.target_triple.unwrap_or_default();
    // Project dev config fills the feature selection only when the
    // command line named none of its own.
    let had_feature_selection = !key.features.is_empty() || flags.no_default_features || flags.all_features;
    if flags.manifest_path.is_none() && flags.package.is_none() && flags.bin.is_none() && !flags.lib {
        if !had_feature_selection {
            apply_dev_config(&mut key, file);
        }
        return key;
    }
    // Only a crate session runs Cargo, so only it carries the network mode.
    key.cargo_net = net;
    // An explicit manifest path wins; else the nearest Cargo.toml above the file.
    let manifest = match &flags.manifest_path {
        Some(p) => std::fs::read_to_string(p).ok().map(|text| {
            let (package, version, bins) = parse_manifest(&text);
            Manifest { dir: p.parent().map_or_else(|| PathBuf::from("."), Path::to_path_buf), path: p.clone(), package, version, bins }
        }),
        None => find_manifest(file),
    };
    let package =
        flags.package.or_else(|| manifest.as_ref().and_then(|m| m.package.clone())).unwrap_or_else(|| key.krate.target_name.clone());
    let version = manifest.as_ref().and_then(|m| m.version.clone()).unwrap_or_else(|| "0.0.0".into());
    key.krate.package_id = match &manifest {
        Some(m) => format!("{package} {version} (path+file://{})", m.dir.display()),
        None => format!("pkg:{package} {version}"),
    };
    key.krate.manifest_path = manifest.as_ref().map(|m| m.path.clone()).or(flags.manifest_path);
    // A package compiles under the dev profile Cargo would use (it unwinds by default).
    key.profile = key.krate.manifest_path.as_deref().map_or(ProfileFlags::DEV_UNWIND, dev_profile);
    if flags.lib {
        key.krate.target_kind = "lib".into();
        key.krate.target_name = package;
    } else {
        key.krate.target_kind = "bin".into();
        key.krate.target_name = flags.bin.or_else(|| manifest.as_ref().and_then(|m| selected_bin(m, file))).unwrap_or(package);
    }
    if !had_feature_selection {
        apply_dev_config(&mut key, file);
    }
    key
}

/// `LUST_SOURCES_READY=<file>` (resolve/prefetch.rs): a build reads no workspace file before
/// <file> exists, as a CI job checks its sources out beside the front image restore.
pub const SOURCES_READY_ENV: &str = "LUST_SOURCES_READY";

/// True for a command that waits for its sources (`SOURCES_READY_ENV`): a build (check,
/// build or run) with the variable set. Other commands (a daemon) do not wait.
pub fn waits_for_sources(args: &[String]) -> bool {
    std::env::var_os(SOURCES_READY_ENV).is_some_and(|v| !v.is_empty()) && matches!(args.first().map(String::as_str), Some("check" | "build" | "run"))
}

/// Parses the command line (without the program name). Paths become absolute.
pub fn parse_args(args: &[String]) -> Option<Invocation> {
    let mut it = args.iter();
    let cmd = it.next()?;
    if cmd == "daemon" {
        return Some(Invocation::Daemon);
    }
    if !["check", "build", "run"].contains(&cmd.as_str()) {
        return None;
    }
    let mut file = PathBuf::new();
    let (mut out, mut json, mut timings, mut debug, mut emit_c, mut run_args) = (None, false, false, false, None, Vec::new());
    let (mut release, mut profile, mut rustc) = (false, None, false);
    let mut max_errors = 20usize;
    let mut crate_flags = CrateFlags::default();
    // Every --target named, in order. One builds a session; several are
    // the release driver's list and build one session each.
    let mut targets: Vec<String> = Vec::new();
    let mut net = CargoNet { offline: std::env::var("CARGO_NET_OFFLINE").is_ok_and(|v| v == "true"), locked: false };
    // `-C panic=unwind|abort`, `-C overflow-checks=on|off` and `-C debug-assertions=on|off`,
    // as rustc takes them. None keeps the default.
    let mut panic_abort: Option<bool> = None;
    let (mut overflow_checks, mut debug_assertions): (Option<bool>, Option<bool>) = (None, None);
    // A rustc boolean option value.
    fn rustc_bool(v: &str) -> Option<bool> {
        match v {
            "y" | "yes" | "on" | "true" => Some(true),
            "n" | "no" | "off" | "false" => Some(false),
            _ => None,
        }
    }
    // Splits one `--features` value (comma- or space-separated, as Cargo takes).
    fn push_features(into: &mut Vec<String>, value: &str) -> Option<()> {
        let names: Vec<&str> = value.split(|c: char| c == ',' || c.is_whitespace()).filter(|s| !s.is_empty()).collect();
        if names.is_empty() {
            return None;
        }
        into.extend(names.iter().map(|s| s.to_string()));
        Some(())
    }
    while let Some(a) = it.next() {
        match a.as_str() {
            "--json" => json = true,
            "--timings" => timings = true,
            "-g" => debug = true,
            "-o" => out = Some(PathBuf::from(it.next()?)),
            "--emit-c" => emit_c = Some(PathBuf::from(it.next()?)),
            "--release" => release = true,
            "--profile" => profile = Some(it.next()?.clone()),
            "--rustc" => rustc = true,
            "--max-errors" => max_errors = it.next()?.parse().ok()?,
            _ if a.starts_with("--max-errors=") => max_errors = a["--max-errors=".len()..].parse().ok()?,
            "--manifest-path" => crate_flags.manifest_path = Some(PathBuf::from(it.next()?)),
            _ if a.starts_with("--manifest-path=") => crate_flags.manifest_path = Some(PathBuf::from(&a["--manifest-path=".len()..])),
            "--package" | "-p" => crate_flags.package = Some(it.next()?.clone()),
            _ if a.starts_with("--package=") => crate_flags.package = Some(a["--package=".len()..].to_string()),
            "--bin" => crate_flags.bin = Some(it.next()?.clone()),
            _ if a.starts_with("--bin=") => crate_flags.bin = Some(a["--bin=".len()..].to_string()),
            "--lib" => crate_flags.lib = true,
            "--features" => push_features(&mut crate_flags.features, it.next()?)?,
            _ if a.starts_with("--features=") => push_features(&mut crate_flags.features, &a["--features=".len()..])?,
            "--no-default-features" => crate_flags.no_default_features = true,
            "--all-features" => crate_flags.all_features = true,
            "--offline" => net.offline = true,
            "--locked" => net.locked = true,
            "--frozen" => net = CargoNet { offline: true, locked: true },
            "-C" => match it.next()?.as_str() {
                "panic=unwind" => panic_abort = Some(false),
                "panic=abort" => panic_abort = Some(true),
                c if c.starts_with("overflow-checks=") => overflow_checks = Some(rustc_bool(&c["overflow-checks=".len()..])?),
                c if c.starts_with("debug-assertions=") => debug_assertions = Some(rustc_bool(&c["debug-assertions=".len()..])?),
                _ => return None,
            },
            "--target" => targets.push(it.next()?.clone()),
            _ if a.starts_with("--target=") => targets.push(a["--target=".len()..].to_string()),
            "--" => run_args = it.by_ref().cloned().collect(),
            _ if file.as_os_str().is_empty() => file = a.into(),
            _ => return None,
        }
    }
    if crate_flags.lib && crate_flags.bin.is_some() {
        return None;
    }
    if file.as_os_str().is_empty() {
        return None;
    }
    let abs = |p: &Path| std::path::absolute(p).unwrap_or_else(|_| p.to_path_buf());
    // A manifest names its package by path: canonical, as Cargo's are
    // (`absolute` keeps a `..`).
    let manifest_abs = |p: &Path| p.canonicalize().unwrap_or_else(|_| abs(p));
    // Release and the rustc oracle are build/check-only, with no extra lust flags.
    // Crate-selection flags are lust dev flags today: reject them there rather
    // than build a different crate selection than the user named.
    if rustc {
        if cmd != "check" || release || profile.is_some() || !run_args.is_empty() || crate_flags.any() || !targets.is_empty() || panic_abort.is_some() || overflow_checks.is_some() || debug_assertions.is_some() {
            return None;
        }
        return Some(Invocation::RustcCheck { file: abs(&file) });
    }
    if (release || profile.is_some()) && !targets.is_empty() {
        // The lust release driver: one cold cc request per named target.
        // Crate flags are its inputs, unlike the Cargo release below.
        if cmd != "build" || !run_args.is_empty() || crate_flags.lib {
            return None;
        }
        let typed = file.clone();
        let file = abs(&file);
        if let Some(p) = crate_flags.manifest_path.take() {
            crate_flags.manifest_path = Some(manifest_abs(&p));
        }
        let profile_name = profile.as_deref().unwrap_or("release");
        let manifest = crate_flags.manifest_path.clone().or_else(|| find_manifest(&file).map(|m| m.path));
        let named = match cargo_profile(manifest.as_deref(), profile_name) {
            Ok(p) => p.flags,
            Err(e) => return Some(Invocation::ReleaseCc { reqs: Err(e) }),
        };
        let multi = targets.len() > 1;
        let mut reqs = Vec::new();
        for triple in &targets {
            let mut flags = crate_flags.clone();
            flags.target_triple = Some(triple.clone());
            let mut session = session_key_for(&file, flags, net);
            session.profile = named;
            if let Some(abort) = panic_abort {
                session.profile.panic_abort = abort;
            }
            let bin = format!("{}{}", session.krate.target_name, if triple.contains("windows") { ".exe" } else { "" });
            let out = match &out {
                Some(o) if multi => abs(&o.join(triple).join(&bin)),
                Some(o) => abs(o),
                None if multi => abs(&PathBuf::from(triple).join(&bin)),
                None => abs(&PathBuf::from(bin)),
            };
            reqs.push(Request {
                cmd: Cmd::Build,
                session,
                file: file.clone(),
                out,
                json,
                timings,
                debug,
                emit_c: emit_c.as_ref().map(|p| {
                    let p = abs(p);
                    if multi { PathBuf::from(format!("{}-{}", p.display(), triple)) } else { p }
                }),
                max_errors,
                run_args: None,
                harness: false,
                cc: true,
                client: Client::current(&typed),
            });
        }
        return Some(Invocation::ReleaseCc { reqs: Ok(reqs) });
    }
    if release || profile.is_some() {
        if cmd != "build" || !run_args.is_empty() || emit_c.is_some() || crate_flags.any() || panic_abort.is_some() || overflow_checks.is_some() || debug_assertions.is_some() {
            return None;
        }
        if release && profile.is_none() {
            profile = Some("release".into());
        }
        return Some(Invocation::Release { file: abs(&file), out: out.map(|p| abs(&p)), profile, debug, net });
    }
    if targets.len() > 1 {
        return None;
    }
    crate_flags.target_triple = targets.into_iter().next();
    let out = out.unwrap_or_else(|| PathBuf::from(file.file_stem().unwrap_or_default()));
    let run = cmd == "run";
    let typed = file.clone();
    let file = abs(&file);
    if let Some(p) = crate_flags.manifest_path.take() {
        crate_flags.manifest_path = Some(manifest_abs(&p));
    }
    let mut session = session_key_for(&file, crate_flags, net);
    if let Some(abort) = panic_abort {
        session.profile.panic_abort = abort;
    }
    if let Some(on) = overflow_checks {
        session.profile.overflow_checks = on;
    }
    if let Some(on) = debug_assertions {
        session.profile.debug_assertions = on;
    }
    let req = Request {
        cmd: if cmd == "check" { Cmd::Check } else { Cmd::Build },
        session,
        file,
        out: abs(&out),
        json,
        timings,
        debug,
        emit_c: emit_c.map(|p| abs(&p)),
        max_errors,
        run_args: if run { Some(run_args.clone()) } else { None },
        harness: false, cc: false,
        client: Client::current(&typed),
    };
    Some(Invocation::Compile { req, run, args: run_args })
}

/// The daemon socket for the current directory. The name holds the compiler build hash, so a rebuilt
/// `lust` never talks to a daemon from an older build (that daemon exits on its idle timeout).
pub fn socket_path() -> PathBuf {
    std::env::var_os("LUST_DAEMON_SOCKET")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(format!(".lust-daemon-{}.sock", &env!("LUST_BUILD_HASH")[..8])))
}

/// Appends one length-prefixed field: "<byte len>\n<bytes>".
fn put_field(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(bytes.len().to_string().as_bytes());
    out.push(b'\n');
    out.extend_from_slice(bytes);
}

/// Reads one length-prefixed field written by `put_field`.
fn get_field(r: &mut impl BufRead) -> Option<Vec<u8>> {
    let mut head = String::new();
    if r.read_line(&mut head).ok()? == 0 {
        return None;
    }
    let len: usize = head.trim().parse().ok()?;
    // A length this large is a bad request, not an allocation to attempt.
    if len > (1 << 28) {
        return None;
    }
    let mut bytes = vec![0u8; len];
    r.read_exact(&mut bytes).ok()?;
    Some(bytes)
}

/// The source override set in this process's env, if any (`LUST_STD_SRC`,
/// `LUST_LIBRARY`; ARCH 3.8): std or adapter source read from a tree the
/// user edits. A daemon session loads std once and the disk cache keys on
/// the compiler build, so neither can see those edits: under an override
/// the client never uses a daemon, a daemon does not start, and the disk
/// cache is off. Every compile is then cold, so it reads the tree as it is.
pub fn source_override() -> Option<&'static str> {
    ["LUST_STD_SRC", "LUST_LIBRARY"].into_iter().find(|v| std::env::var_os(v).is_some_and(|d| !d.is_empty()))
}

/// This build's identity on the daemon wire: the build hash (compiler and
/// shipped library sources, tcc; see build.rs) and the file identity of the
/// `lust-core` binary (device, inode, size, mtime), so a rebuild or a binary
/// replaced at the same path differs even when its sources hash the same.
/// The client names its sibling `lust-core`; `lust-core` names itself. A
/// daemon computes it once, so it keeps the identity of the binary it runs.
pub fn build_id() -> &'static str {
    static ID: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    ID.get_or_init(|| {
        use std::os::unix::fs::MetadataExt;
        let core = std::env::current_exe()
            .map(|e| if e.file_name().is_some_and(|n| n == "lust-core") { e } else { e.with_file_name("lust-core") });
        let file = core.and_then(std::fs::metadata).map_or_else(
            |_| "-".to_string(),
            |m| format!("{:x}.{:x}.{:x}.{:x}.{:x}", m.dev(), m.ino(), m.size(), m.mtime(), m.mtime_nsec()),
        );
        format!("{}.{file}", env!("LUST_BUILD_HASH"))
    })
}

/// Why `read_request` gives no request.
#[derive(Debug, PartialEq, Eq)]
pub enum ReadError {
    /// EOF, a bad header, or a short read.
    Bad,
    /// A client of another lust build (or one that predates the build field).
    OtherBuild,
}

pub fn encode(r: &Request) -> Vec<u8> {
    let b = |x: bool| if x { "1" } else { "0" };
    let cmd = if r.cmd == Cmd::Check { "check" } else { "build" };
    let s = &r.session;
    let env_count = r.client.env.as_ref().map_or_else(|| "-".to_string(), |e| e.len().to_string());
    let mut out = format!(
        "{cmd} {} {} {} {} {} {} {} {} {} {} {} {env_count} {} {} {}\n",
        b(r.json),
        b(r.timings),
        b(r.debug),
        r.max_errors,
        b(s.krate.test),
        b(s.default_features),
        b(s.all_features),
        b(s.profile.panic_abort),
        b(s.profile.overflow_checks),
        b(s.profile.debug_assertions),
        s.features.len(),
        b(s.cargo_net.offline),
        b(s.cargo_net.locked),
        build_id()
    )
    .into_bytes();
    let path_field = |out: &mut Vec<u8>, p: Option<&Path>| put_field(out, p.map_or(&[][..], |p| p.as_os_str().as_encoded_bytes()));
    path_field(&mut out, Some(&r.file));
    path_field(&mut out, Some(&r.out));
    path_field(&mut out, r.emit_c.as_deref());
    put_field(&mut out, s.krate.package_id.as_bytes());
    path_field(&mut out, s.krate.manifest_path.as_deref());
    put_field(&mut out, s.krate.target_kind.as_bytes());
    put_field(&mut out, s.krate.target_name.as_bytes());
    path_field(&mut out, Some(&s.krate.root));
    put_field(&mut out, s.target_triple.as_bytes());
    for f in &s.features {
        put_field(&mut out, f.as_bytes());
    }
    path_field(&mut out, r.client.shown.as_deref());
    for (k, v) in r.client.env.iter().flatten() {
        put_field(&mut out, k.as_bytes());
        put_field(&mut out, v.as_bytes());
    }
    out
}

/// Reads one request. A header of another build is `OtherBuild` before any
/// field is read: its fields may mean something else.
pub fn read_request(r: &mut impl BufRead) -> Result<Request, ReadError> {
    let mut head = String::new();
    if r.read_line(&mut head).map_err(|_| ReadError::Bad)? == 0 {
        return Err(ReadError::Bad);
    }
    let f: Vec<&str> = head.split_whitespace().collect();
    if f.len() != 16 || f[15] != build_id() {
        // The first word is always a command, so a short header of a known
        // command is a client from before this field.
        return Err(if matches!(f.first(), Some(&"check" | &"build")) { ReadError::OtherBuild } else { ReadError::Bad });
    }
    read_fields(r, &f).ok_or(ReadError::Bad)
}

/// The length-prefixed fields after a request header `f`.
fn read_fields(r: &mut impl BufRead, f: &[&str]) -> Option<Request> {
    #[allow(unused_imports)]
    use std::os::unix::ffi::OsStringExt as _;
    let path = |bytes: Vec<u8>| PathBuf::from(std::ffi::OsString::from_vec(bytes));
    let text = |bytes: Vec<u8>| String::from_utf8(bytes).ok();
    let file = path(get_field(r)?);
    let out = path(get_field(r)?);
    let emit = get_field(r)?;
    let package_id = text(get_field(r)?)?;
    let manifest = get_field(r)?;
    let target_kind = text(get_field(r)?)?;
    let target_name = text(get_field(r)?)?;
    let root = path(get_field(r)?);
    let target_triple = text(get_field(r)?)?;
    // A feature count this large is a bad request, not a loop to run.
    let n_features: usize = f[11].parse().ok()?;
    if n_features > 4096 {
        return None;
    }
    let mut features = Vec::with_capacity(n_features);
    for _ in 0..n_features {
        features.push(text(get_field(r)?)?);
    }
    sort_features(&mut features);
    let shown = get_field(r)?;
    let env = match f[12] {
        "-" => None,
        n => {
            // Same bound as the feature count: a bad request, not a loop to run.
            let n: usize = n.parse().ok()?;
            if n > 1 << 16 {
                return None;
            }
            let mut env = Vec::with_capacity(n);
            for _ in 0..n {
                env.push((text(get_field(r)?)?, text(get_field(r)?)?));
            }
            Some(env)
        }
    };
    Some(Request {
        cmd: if f[0] == "check" { Cmd::Check } else { Cmd::Build },
        session: SessionKey {
            krate: CrateKey {
                package_id,
                manifest_path: if manifest.is_empty() { None } else { Some(path(manifest)) },
                target_kind,
                target_name,
                root,
                test: f[5] == "1",
            },
            features,
            default_features: f[6] == "1",
            all_features: f[7] == "1",
            target_triple,
            profile: ProfileFlags { panic_abort: f[8] == "1", overflow_checks: f[9] == "1", debug_assertions: f[10] == "1" },
            cargo_net: CargoNet { offline: f[13] == "1", locked: f[14] == "1" },
        },
        file,
        out,
        json: f[1] == "1",
        timings: f[2] == "1",
        debug: f[3] == "1",
        emit_c: if emit.is_empty() { None } else { Some(path(emit)) },
        max_errors: f[4].parse().ok()?,
        run_args: None,
        harness: false, cc: false,
        client: Client { env, shown: if shown.is_empty() { None } else { Some(path(shown)) } },
    })
}

pub fn write_response(w: &mut impl Write, r: &Response) -> std::io::Result<()> {
    write!(w, "{} {} {} {}\n{}{}", r.code, r.stdout.len(), r.stderr.len(), build_id(), r.stdout, r.stderr)
}

/// The whole answer to a request of another build: a head no client takes
/// for a response (older clients need three numbers), then the daemon exits.
pub fn write_other_build(w: &mut impl Write) -> std::io::Result<()> {
    write!(w, "- - - {}\n", build_id())
}

/// Sends a request to a running daemon. None if no daemon answers, or if the
/// one that answers is another lust build: that answer is dropped and the
/// caller compiles cold. A daemon of another build that knows the build
/// field exits by itself; an older one is stopped by removing its socket
/// (its stop request), so the next command starts a daemon of this build.
pub fn request(sock: &Path, req: &Request) -> Option<Response> {
    let mut conn = UnixStream::connect(sock).ok()?;
    conn.write_all(&encode(req)).ok()?;
    let mut reader = BufReader::new(conn);
    let mut head = String::new();
    reader.read_line(&mut head).ok()?;
    let words: Vec<&str> = head.split_whitespace().collect();
    let nums: Vec<usize> = words.iter().take(3).filter_map(|x| x.parse().ok()).collect();
    if nums.len() == 3 && words.len() == 3 {
        // A daemon from before the build field: stop it.
        let _ = std::fs::remove_file(sock);
        return None;
    }
    if nums.len() != 3 || words.len() != 4 || words[3] != build_id() {
        return None;
    }
    let mut out = vec![0; nums[1]];
    let mut err = vec![0; nums[2]];
    reader.read_exact(&mut out).ok()?;
    reader.read_exact(&mut err).ok()?;
    Some(Response {
        code: nums[0] as i32,
        stdout: String::from_utf8_lossy(&out).into_owned(),
        stderr: String::from_utf8_lossy(&err).into_owned(),
        ran: false,
    })
}

/// Prints a response. For `run`, runs the program after a successful build. Never returns.
pub fn finish(resp: Response, run: bool, out: &Path, args: &[String]) -> ! {
    print!("{}", resp.stdout);
    eprint!("{}", resp.stderr);
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    if resp.ran || resp.code != 0 || !run {
        std::process::exit(resp.code);
    }
    let status = std::process::Command::new(out).args(args).status().expect("cannot run the program");
    std::process::exit(status.code().unwrap_or(134));
}

// ---------------------------------------------------------------------------
// Release builds and the rustc oracle. lust owns the dev loop; Cargo or rustc
// builds the shipped binary from the same source (rule zero). Output streams
// through this process. These paths never use the daemon or the disk cache.

/// Runs a child with this process's stdin/stdout/stderr. Exits with its code.
fn run_streamed(tool: &str, cmd: &mut std::process::Command) -> std::process::ExitStatus {
    match cmd.status() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot run {tool}: {e}");
            std::process::exit(2);
        }
    }
}

/// Exits with a child status: its code, or 1 when a signal killed it.
fn exit_with(status: std::process::ExitStatus) -> ! {
    std::process::exit(status.code().unwrap_or(1));
}

/// The bits of a Cargo.toml that bin selection and crate identity need.
struct Manifest {
    dir: PathBuf,
    path: PathBuf,
    package: Option<String>,
    version: Option<String>,
    /// (bin name, path as written) per `[[bin]]` table.
    bins: Vec<(String, Option<String>)>,
}

/// A TOML string value after `key =`: quoted text (up to the closing quote, so a
/// trailing comment is dropped), else the bare token.
fn toml_value(line: &str) -> Option<String> {
    let v = line.split_once('=')?.1.trim();
    if let Some(rest) = v.strip_prefix(['"', '\'']) {
        let quote = v.as_bytes()[0] as char;
        return Some(rest.split(quote).next()?.to_string());
    }
    Some(v.trim_end_matches(|c: char| c == ',' || c.is_whitespace()).to_string())
}

/// One TOML line without its comment (a `#` outside quotes).
fn toml_strip_comment(line: &str) -> &str {
    let mut quote = None;
    for (i, c) in line.char_indices() {
        match (quote, c) {
            (None, '"' | '\'') => quote = Some(c),
            (Some(q), _) if c == q => quote = None,
            (None, '#') => return &line[..i],
            _ => {}
        }
    }
    line
}

/// A dotted TOML key or table name in plain form: `profile . "dev"` is `profile.dev`.
fn toml_dotted(key: &str) -> String {
    key.split('.').map(|s| s.trim().trim_matches(|c| c == '"' || c == '\'')).collect::<Vec<_>>().join(".")
}

/// The value of the dotted key `path` (for example `profile.dev.panic`) in
/// TOML text, in any form Cargo reads: under its table header, as a dotted
/// key under a parent table or at top level, or inside a one-line inline
/// table (`[profile] dev = { panic = "abort" }`). Strings and bare values
/// (bools) only, which is what profile settings are.
fn toml_lookup(text: &str, path: &str) -> Option<String> {
    let mut section = String::new();
    for raw in text.lines() {
        let line = toml_strip_comment(raw).trim();
        if line.starts_with("[[") {
            section = "[[array]]".into();
            continue;
        }
        if let Some(head) = line.strip_prefix('[') {
            section = toml_dotted(head.trim_end_matches(']'));
            continue;
        }
        let Some((k, v)) = line.split_once('=') else { continue };
        let key = if section.is_empty() { toml_dotted(k) } else { format!("{section}.{}", toml_dotted(k)) };
        if key == path {
            return toml_value(line);
        }
        // An inline table whose key is a prefix of `path`.
        if let (Some(rest), Some(body)) = (path.strip_prefix(&format!("{key}.")), v.trim().strip_prefix('{')) {
            let body = body.trim_end().trim_end_matches('}');
            return body.split(',').find(|kv| kv.split_once('=').is_some_and(|(ik, _)| toml_dotted(ik) == rest)).and_then(toml_value);
        }
    }
    None
}

/// The dev profile Cargo applies to the package at `manifest` (`cargo_profile`), with
/// Cargo's dev defaults when it cannot be read.
fn dev_profile(manifest: &Path) -> ProfileFlags {
    cargo_profile(Some(manifest), "dev").map_or(ProfileFlags::DEV_UNWIND, |p| p.flags)
}

/// The texts Cargo merges for profiles of the package at `manifest`, highest first:
/// the `.cargo/config.toml` (or legacy `.cargo/config`) chain from the manifest dir up
/// (nearer wins; lust runs Cargo there), then `$CARGO_HOME/config.toml`, then the
/// workspace root manifest (Cargo reads profiles from the root only: the manifest itself
/// when it has `[workspace]`, else the nearest manifest above it that has one).
fn profile_sources(manifest: &Path) -> Vec<String> {
    let is_root = |t: &str| t.lines().any(|l| toml_strip_comment(l).trim().strip_prefix('[').is_some_and(|h| toml_dotted(h.trim_end_matches(']')) == "workspace"));
    let own = std::fs::read_to_string(manifest).unwrap_or_default();
    let root = if is_root(&own) {
        own
    } else {
        let above = manifest.parent().into_iter().flat_map(|d| d.ancestors().skip(1));
        above.filter_map(|d| std::fs::read_to_string(d.join("Cargo.toml")).ok()).find(|t| is_root(t)).unwrap_or(own)
    };
    let mut texts = Vec::new();
    for d in manifest.parent().into_iter().flat_map(Path::ancestors) {
        // Cargo reads the legacy name when both files exist.
        if let Some(t) = [".cargo/config", ".cargo/config.toml"].iter().find_map(|n| std::fs::read_to_string(d.join(n)).ok()) {
            texts.push(t);
        }
    }
    let home = std::env::var_os("CARGO_HOME").map(PathBuf::from).or_else(|| std::env::var_os("HOME").map(|h| Path::new(&h).join(".cargo")));
    if let Some(t) = home.and_then(|h| ["config", "config.toml"].iter().find_map(|n| std::fs::read_to_string(h.join(n)).ok())) {
        texts.push(t);
    }
    texts.push(root);
    texts
}

/// The settings of one Cargo profile that lust's builds use: the flags that change program
/// output, and `opt-level` ("0" to "3", "s", "z") for the C compiler of a release build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CargoProfile {
    pub flags: ProfileFlags,
    pub opt_level: String,
}

/// The profile `name` (`dev`, `release`, `test`, `bench`, or a custom profile with
/// `inherits`) that Cargo applies to the package at `manifest` (None: a file with no
/// manifest), read from `CARGO_PROFILE_<NAME>_<KEY>` env vars, then `profile_sources`. A
/// key the profile leaves unset comes from the profile it inherits (`test` inherits `dev`,
/// `bench` inherits `release`), and at the end from Cargo's defaults: dev checks overflow
/// and debug assertions at opt-level 0, release checks neither at opt-level 3; both
/// unwind. Per-package overrides are not read.
pub fn cargo_profile(manifest: Option<&Path>, name: &str) -> Result<CargoProfile, String> {
    let texts = manifest.map(profile_sources).unwrap_or_default();
    let get = |profile: &str, key: &str| {
        let up = |s: &str| s.to_uppercase().replace('-', "_");
        let env = format!("CARGO_PROFILE_{}_{}", up(profile), up(key));
        std::env::var(env).ok().or_else(|| texts.iter().find_map(|t| toml_lookup(t, &format!("profile.{profile}.{key}"))))
    };
    // The inherits chain from `name` down to `dev` or `release`.
    let mut chain = vec![name.to_string()];
    loop {
        let cur = chain.last().cloned().unwrap_or_default();
        let parent = match cur.as_str() {
            "dev" | "release" => break,
            "test" => "dev".to_string(),
            "bench" => "release".to_string(),
            _ => get(&cur, "inherits").ok_or_else(|| format!("profile `{cur}` is not defined or has no `inherits`"))?,
        };
        if chain.contains(&parent) {
            return Err(format!("profile `{name}` inherits in a cycle: {} -> {parent}", chain.join(" -> ")));
        }
        chain.push(parent);
    }
    let release = chain.last().is_some_and(|p| p == "release");
    let lookup = |key: &str| chain.iter().find_map(|p| get(p, key));
    Ok(CargoProfile {
        flags: ProfileFlags {
            panic_abort: lookup("panic").map_or(false, |v| v == "abort"),
            overflow_checks: lookup("overflow-checks").map_or(!release, |v| v == "true"),
            debug_assertions: lookup("debug-assertions").map_or(!release, |v| v == "true"),
        },
        opt_level: lookup("opt-level").unwrap_or_else(|| if release { "3" } else { "0" }.into()),
    })
}

/// Reads package name, package version, and `[[bin]]` tables from manifest
/// text. Section-gated on purpose: a `name` in `[dependencies]` or a profile
/// table must never match.
fn parse_manifest(text: &str) -> (Option<String>, Option<String>, Vec<(String, Option<String>)>) {
    let mut package = None;
    let mut version = None;
    let mut bins: Vec<(String, Option<String>)> = Vec::new();
    let mut section = "";
    for raw in text.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            section = line.trim_matches(|c| c == '[' || c == ']');
            if section == "bin" && line.starts_with("[[") {
                bins.push((String::new(), None));
            }
            continue;
        }
        let key = line.split('=').next().unwrap_or("").trim();
        match (section, key) {
            ("package", "name") if package.is_none() => package = toml_value(line),
            ("package", "version") if version.is_none() => version = toml_value(line),
            ("bin", "name") => {
                if let (Some(last), Some(v)) = (bins.last_mut(), toml_value(line)) {
                    last.0 = v;
                }
            }
            ("bin", "path") => {
                if let (Some(last), Some(v)) = (bins.last_mut(), toml_value(line)) {
                    last.1 = Some(v);
                }
            }
            _ => {}
        }
    }
    (package, version, bins)
}

/// The nearest Cargo.toml at or above the file's directory, if one exists.
fn find_manifest(file: &Path) -> Option<Manifest> {
    let mut dir = file.parent();
    while let Some(d) = dir {
        let path = d.join("Cargo.toml");
        if let Ok(text) = std::fs::read_to_string(&path) {
            let (package, version, bins) = parse_manifest(&text);
            return Some(Manifest { dir: d.to_path_buf(), path, package, version, bins });
        }
        dir = d.parent();
    }
    None
}

/// Which `--bin` a file selects inside its package. Cargo conventions first
/// (`src/bin/<name>.rs`, `src/bin/<name>/main.rs`), then `[[bin]] path`, then
/// `src/main.rs` as the package bin. A library or module file selects no bin:
/// the whole package builds.
fn selected_bin(m: &Manifest, file: &Path) -> Option<String> {
    let rel = file.strip_prefix(&m.dir).ok()?;
    let parts: Vec<String> = rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect();
    if parts.len() == 3 && parts[0] == "src" && parts[1] == "bin" {
        return parts[2].strip_suffix(".rs").map(str::to_string);
    }
    if parts.len() == 4 && parts[0] == "src" && parts[1] == "bin" && parts[3] == "main.rs" {
        return Some(parts[2].clone());
    }
    let rel_str = rel.to_string_lossy().replace('\\', "/");
    if let Some((name, _)) = m.bins.iter().find(|(_, p)| p.as_deref() == Some(rel_str.as_str())) {
        return Some(name.clone());
    }
    if rel_str == "src/main.rs" {
        // An explicit [[bin]] for it won above. Else it is the package bin.
        return m.package.clone();
    }
    None
}

/// The target directory a manifest builds into, from `cargo metadata`.
/// Only used after a successful build when `-o` needs the artifact path.
fn cargo_target_dir(manifest: &Path) -> Option<PathBuf> {
    let out = std::process::Command::new("cargo")
        .args(["metadata", "--format-version", "1", "--no-deps", "--manifest-path"])
        .arg(manifest)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let at = text.find("\"target_directory\":\"")? + "\"target_directory\":\"".len();
    let end = text[at..].find('"')? + at;
    Some(PathBuf::from(text[at..end].replace("\\\\", "\\")))
}

/// `lust build --release` / `--profile <name>`. With a Cargo.toml above the file, Cargo
/// builds it with the file's package and bin selection. Without one, rustc builds the
/// single file with the release oracle flags from DESIGN.md. Never returns.
pub fn run_release(file: &Path, out: Option<&Path>, profile: Option<&str>, debug: bool, net: CargoNet) -> ! {
    let profile = profile.unwrap_or("release");
    let dev = profile == "dev";
    if let Some(m) = find_manifest(file) {
        let bin = selected_bin(&m, file);
        let mut args: Vec<std::ffi::OsString> = vec!["build".into(), "--manifest-path".into(), m.path.clone().into_os_string()];
        match profile {
            "release" => args.push("--release".into()),
            "dev" => {}
            name => args.extend(["--profile".into(), name.into()]),
        }
        if let Some(pkg) = &m.package {
            args.extend(["-p".into(), pkg.into()]);
        }
        if let Some(bin) = &bin {
            args.extend(["--bin".into(), bin.into()]);
        }
        args.extend(net.args().map(Into::into));
        eprintln!("lust: release build via cargo: cargo {}", args.iter().map(|a| a.to_string_lossy()).collect::<Vec<_>>().join(" "));
        let status = run_streamed("cargo", std::process::Command::new("cargo").args(&args));
        if !status.success() {
            exit_with(status);
        }
        // Cargo has no stable -o. Copy the artifact when the caller asked for one.
        if let Some(out) = out {
            let name = bin.as_ref().or(m.package.as_ref());
            let artifact = name.and_then(|n| cargo_target_dir(&m.path).map(|t| t.join(if dev { "debug" } else { profile }).join(n)));
            match artifact {
                Some(a) if a.exists() => {
                    if let Err(e) = std::fs::copy(&a, out) {
                        eprintln!("error: cannot copy {} to {}: {e}", a.display(), out.display());
                        std::process::exit(2);
                    }
                    eprintln!("lust: built with cargo: {} (copied to {})", a.display(), out.display());
                }
                _ => {
                    eprintln!("error: cargo built the package, but no binary artifact was found to copy to {}", out.display());
                    std::process::exit(2);
                }
            }
        } else {
            eprintln!("lust: built with cargo (profile {profile})");
        }
        std::process::exit(0);
    }
    // No Cargo.toml: rustc on the single file, with DESIGN.md's release oracle flags at
    // rustc's default lint levels and its default panic strategy (unwind), so deny-by-default lints (unconditional_panic,
    // arithmetic_overflow) reject as they do for any rustc user; a source `#[allow]` still works.
    let fallback = PathBuf::from(file.file_stem().unwrap_or_default());
    let out: &Path = out.unwrap_or(&fallback);
    let mut cmd = std::process::Command::new("rustc");
    cmd.args(["--edition", "2024"]);
    if dev {
        cmd.args(["-C", "overflow-checks=on"]);
    } else {
        cmd.args(["-O", "-C", "overflow-checks=off"]);
    }
    if debug {
        cmd.arg("-g");
    }
    cmd.arg("-o").arg(out).arg(file);
    eprintln!(
        "lust: release build via rustc: rustc --edition 2024 {} -o {} {}",
        if dev { "(dev flags)" } else { "-O" },
        out.display(),
        file.display()
    );
    let status = run_streamed("rustc", &mut cmd);
    if status.success() {
        eprintln!("lust: built with rustc: {}", out.display());
    }
    exit_with(status);
}

/// `lust check --rustc`: the real rustc verdict with the dev oracle flags from DESIGN.md at
/// rustc's default lint levels. A second opinion for agents. It emits an object file (no link),
/// not metadata: `--emit=metadata` stops before the MIR passes, so it misses deny-by-default
/// lints (unconditional_panic, arithmetic_overflow) and post-monomorphization const errors that
/// `rustc` and `cargo build` reject. On a 950-line file the object takes 190 ms against 160 ms
/// for metadata and 250 ms for a linked binary. Never returns.
pub fn run_rustc_check(file: &Path) -> ! {
    let obj = std::env::temp_dir().join(format!("lust-rustc-check-{}.o", std::process::id()));
    eprintln!("lust: checking with rustc (oracle): rustc --edition 2024 --emit=obj {}", file.display());
    let status = run_streamed(
        "rustc",
        std::process::Command::new("rustc")
            .args(["--edition", "2024", "-C", "overflow-checks=on", "--emit=obj", "-o"])
            .arg(&obj)
            .arg(file),
    );
    let _ = std::fs::remove_file(&obj);
    exit_with(status);
}

// ---------------------------------------------------------------------------
// Daemon startup shared by the client (autostart) and the daemon (single
// instance, idle exit). The lock file sits next to the socket and holds the
// daemon's pid. The daemon holds an flock on it for its whole life.

/// The lock file for a daemon socket: `<socket>.lock`.
pub fn daemon_lock_path(sock: &Path) -> PathBuf {
    let mut s = sock.as_os_str().to_owned();
    s.push(".lock");
    PathBuf::from(s)
}

/// How long a daemon may sit idle before it exits. `LUST_DAEMON_IDLE` is seconds,
/// or seconds with an `s`, `m`, or `h` suffix. Default 30 minutes. 0 means never.
pub fn daemon_idle() -> Option<std::time::Duration> {
    let raw = std::env::var("LUST_DAEMON_IDLE").unwrap_or_else(|_| "1800".into());
    let (num, mul) = match raw.chars().last() {
        Some('m') => (&raw[..raw.len() - 1], 60),
        Some('h') => (&raw[..raw.len() - 1], 3600),
        Some('s') => (&raw[..raw.len() - 1], 1),
        _ => (raw.as_str(), 1),
    };
    match num.trim().parse::<u64>() {
        Ok(0) => None,
        Ok(n) => Some(std::time::Duration::from_secs(n * mul)),
        Err(_) => Some(std::time::Duration::from_secs(1800)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    fn compile_req(list: &[&str]) -> Request {
        match parse_args(&args(list)) {
            Some(Invocation::Compile { req, .. }) => req,
            _ => panic!("not a compile invocation: {list:?}"),
        }
    }

    /// The synthetic crate for one file: path identity, `bin` target named by
    /// the stem, and the test flag as the only variant (section 1.7: test and
    /// non-test defs never share identity).
    #[test]
    fn synthetic_key_shape() {
        let k = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false);
        assert_eq!(k.krate.package_id, "file:/tmp/x/main.rs");
        assert_eq!((k.krate.target_kind.as_str(), k.krate.target_name.as_str()), ("bin", "main"));
        assert_eq!(k.krate.root, PathBuf::from("/tmp/x/main.rs"));
        assert!(k.krate.manifest_path.is_none() && k.features.is_empty() && k.default_features && !k.all_features);
        assert_ne!(k, SessionKey::synthetic(Path::new("/tmp/x/main.rs"), true), "test target differs");
        assert_ne!(k, SessionKey::synthetic(Path::new("/tmp/x/other.rs"), false), "file differs");
    }

    /// Two feature selections of one file are two session keys (the S6
    /// routing rule), and flag order or repetition does not make a third.
    #[test]
    fn feature_selections_are_distinct_keys() {
        let a = compile_req(&["check", "/tmp/x/main.rs", "--features", "alpha"]);
        let b = compile_req(&["check", "/tmp/x/main.rs", "--features", "beta"]);
        let both = compile_req(&["check", "/tmp/x/main.rs", "--features", "beta,alpha", "--features=alpha"]);
        assert_ne!(a.session, b.session);
        assert_eq!(a.session.features, ["alpha"]);
        assert_eq!(both.session.features, ["alpha", "beta"]);
        let plain = compile_req(&["check", "/tmp/x/main.rs"]);
        assert_eq!(plain.session, SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false), "no flags stays synthetic");
        // Every resolver input separates keys on its own.
        let t = compile_req(&["check", "/tmp/x/main.rs", "--target", "x86_64-unknown-linux-gnu"]);
        assert_ne!(plain.session, t.session, "target triple");
        assert_ne!(
            plain.session.describe(),
            compile_req(&["check", "/tmp/x/main.rs", "--no-default-features"]).session.describe(),
            "default policy"
        );
        assert_ne!(
            plain.session.describe(),
            compile_req(&["check", "/tmp/x/main.rs", "--all-features"]).session.describe(),
            "all features"
        );
    }

    /// The graph key (1.1) covers every resolver input on disk: manifest
    /// bytes, lock bytes, the cargo config chain, and the selection. An
    /// edit to any one must move it, or the daemon would route the crate
    /// to a session resolved under the old graph.
    #[test]
    fn graph_key_covers_resolver_inputs() {
        let dir = std::env::temp_dir().join(format!("lust-graphkey-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"g\"\nversion = \"0.1.0\"\n").unwrap();
        std::fs::write(dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        let mut key = SessionKey::synthetic(&dir.join("src/main.rs"), false);
        key.krate.manifest_path = Some(dir.join("Cargo.toml"));
        let base = graph_key(&key);
        assert_eq!(graph_key(&key), base, "stable with no edit");
        std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"g\"\nversion = \"0.2.0\"\n").unwrap();
        let after_manifest = graph_key(&key);
        assert_ne!(after_manifest, base, "manifest edit");
        std::fs::write(dir.join("Cargo.lock"), "version = 4\n").unwrap();
        assert_ne!(graph_key(&key), after_manifest, "lock appears");
        std::fs::create_dir_all(dir.join(".cargo")).unwrap();
        std::fs::write(dir.join(".cargo/config.toml"), "[build]\njobs = 2\n").unwrap();
        let after_config = graph_key(&key);
        assert_ne!(after_config, after_manifest, "cargo config appears");
        let mut featured = key.clone();
        featured.features = vec!["alpha".into()];
        assert_ne!(graph_key(&featured), after_config, "feature selection");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Manifest and package flags name a real crate: package identity from
    /// the manifest text, `src/main.rs` selecting the package bin.
    #[test]
    fn manifest_flags_name_the_crate() {
        let dir = std::env::temp_dir().join(format!("lust-key-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let manifest = "[package]\nname = \"widget\"\nversion = \"1.2.3\"\nedition = \"2024\"\n\n[workspace]\n";
        std::fs::write(dir.join("Cargo.toml"), manifest).unwrap();
        std::fs::write(dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        let main_rs = dir.join("src/main.rs");
        let req = compile_req(&[
            "check",
            main_rs.to_str().unwrap(),
            "--manifest-path",
            dir.join("Cargo.toml").to_str().unwrap(),
            "--features",
            "zest",
        ]);
        assert_eq!(req.session.krate.package_id, format!("widget 1.2.3 (path+file://{})", dir.display()));
        assert_eq!((req.session.krate.target_kind.as_str(), req.session.krate.target_name.as_str()), ("bin", "widget"));
        assert_eq!(req.session.krate.manifest_path.as_deref(), Some(dir.join("Cargo.toml").as_path()));
        let lib = compile_req(&["check", main_rs.to_str().unwrap(), "--package", "widget", "--lib"]);
        assert_eq!((lib.session.krate.target_kind.as_str(), lib.session.krate.target_name.as_str()), ("lib", "widget"));
        let _ = std::fs::remove_dir_all(&dir);
        // Contradictory or misplaced crate flags are usage errors, not guesses.
        assert!(parse_args(&args(&["check", "/tmp/x/main.rs", "--lib", "--bin", "x"])).is_none());
        assert!(parse_args(&args(&["build", "/tmp/x/main.rs", "--release", "--features", "a"])).is_none());
        assert!(parse_args(&args(&["check", "/tmp/x/main.rs", "--rustc", "--target", "t"])).is_none());
    }

    /// `--release --target` is the release driver: one cc request per
    /// target, crate flags as inputs, output per target under `-o`.
    /// Without a target `--release` stays the Cargo form, and several
    /// targets without `--release` are a usage error.
    #[test]
    fn release_with_targets_is_the_cc_driver() {
        let inv = parse_args(&args(&[
            "build",
            "/tmp/x/main.rs",
            "--release",
            "--target",
            "x86_64-unknown-linux-musl",
            "--target=aarch64-unknown-linux-musl",
            "--features",
            "noembed",
            "-o",
            "/tmp/x/dist",
        ]));
        match inv {
            Some(Invocation::ReleaseCc { reqs: Ok(reqs) }) => {
                assert_eq!(reqs.len(), 2);
                assert!(reqs.iter().all(|r| r.cc && matches!(r.cmd, Cmd::Build)));
                assert_eq!(reqs[0].session.target_triple, "x86_64-unknown-linux-musl");
                assert_eq!(reqs[0].session.features, ["noembed"]);
                assert_eq!(reqs[1].out, PathBuf::from("/tmp/x/dist/aarch64-unknown-linux-musl/main"));
                assert!(!reqs[0].session.profile.overflow_checks, "the release base turns overflow checks off");
                assert!(!reqs[0].session.profile.debug_assertions, "release profile");
            }
            _ => panic!("not a release-cc invocation"),
        }
        assert!(matches!(
            parse_args(&args(&["build", "/tmp/x/main.rs", "--release"])),
            Some(Invocation::Release { .. })
        ));
        assert!(parse_args(&args(&[
            "build",
            "/tmp/x/main.rs",
            "--target",
            "x86_64-unknown-linux-musl",
            "--target",
            "aarch64-unknown-linux-musl",
        ]))
        .is_none());
    }

    /// The wire carries the full session key: encode, then read back, every
    /// field equal (features sorted on both sides).
    #[test]
    fn wire_round_trips_the_session_key() {
        let mut req = compile_req(&[
            "build",
            "/tmp/x/main.rs",
            "-o",
            "/tmp/x/out",
            "--features",
            "beta,alpha",
            "--no-default-features",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--package",
            "widget",
            "--bin",
            "wbin",
            "--frozen",
        ]);
        assert_eq!(req.session.cargo_net, CargoNet { offline: true, locked: true });
        req.session.krate.test = true;
        let bytes = encode(&req);
        let back = read_request(&mut std::io::Cursor::new(bytes)).unwrap();
        assert_eq!(back.session, req.session);
        assert_eq!((back.file.as_path(), back.out.as_path()), (req.file.as_path(), req.out.as_path()));
        assert!(matches!(back.cmd, Cmd::Build) && !back.harness && back.run_args.is_none());
        // The client's env and typed root path ride along (env! and file! read them).
        assert!(req.client.env.is_some() && req.client.shown.is_some());
        assert_eq!(back.client, req.client);
        // A truncated wire form never reads as a request.
        let bytes = encode(&req);
        assert_eq!(read_request(&mut std::io::Cursor::new(&bytes[..bytes.len() - 3])).err(), Some(ReadError::Bad));
        // Another build's header (here: one from before the build field) is
        // refused before its fields are read.
        let text = String::from_utf8(encode(&req)).unwrap();
        let old = text.replacen(&format!(" {}\n", build_id()), "\n", 1);
        assert_eq!(read_request(&mut std::io::Cursor::new(old.as_bytes())).err(), Some(ReadError::OtherBuild));
        let other = text.replacen(&format!(" {}\n", build_id()), " 0123.other\n", 1);
        assert_eq!(read_request(&mut std::io::Cursor::new(other.as_bytes())).err(), Some(ReadError::OtherBuild));
    }

    /// Project dev config: `dev-exclude-features` turns the package
    /// default list into the effective selection in the session key, CLI
    /// flags win over the config, and `.lust.toml` at the workspace root
    /// works when the manifest carries no lust table.
    #[test]
    fn dev_config_sets_effective_features() {
        let dir = std::env::temp_dir().join(format!("lust-devfeat-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("crate/src")).unwrap();
        std::fs::write(
            dir.join("crate/Cargo.toml"),
            "[package]\nname = \"widget\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[package.metadata.lust]\ndev-exclude-features = [\n  \"jemalloc\",\n]\n\n[features]\ndefault = [\"jemalloc\", \"fast\"]\njemalloc = []\nfast = []\n",
        )
        .unwrap();
        std::fs::write(dir.join("crate/src/lib.rs"), "").unwrap();
        let lib = dir.join("crate/src/lib.rs");
        let mp = dir.join("crate/Cargo.toml");
        let req = compile_req(&["check", lib.to_str().unwrap(), "--manifest-path", mp.to_str().unwrap(), "--lib"]);
        assert_eq!(req.session.features, ["fast"], "default minus jemalloc");
        assert!(!req.session.default_features && !req.session.all_features);
        assert!(req.session.describe().contains("features=[fast] default_features=0"), "{}", req.session.describe());
        let plain = compile_req(&["check", lib.to_str().unwrap()]);
        assert_eq!(plain.session.features, ["fast"], "synthetic file check uses the same config");
        // CLI selection wins over config.
        let cli =
            compile_req(&["check", lib.to_str().unwrap(), "--manifest-path", mp.to_str().unwrap(), "--lib", "--features", "jemalloc"]);
        assert_eq!(cli.session.features, ["jemalloc"]);
        assert!(cli.session.default_features);
        // `.lust.toml` with an exact list, in a crate whose manifest has none.
        std::fs::write(dir.join("crate/Cargo.toml"), "[package]\nname = \"widget\"\nversion = \"0.1.0\"\nedition = \"2024\"\n").unwrap();
        std::fs::write(dir.join(".lust.toml"), "dev-features = [\"noembed\"]\n").unwrap();
        let req = compile_req(&["check", lib.to_str().unwrap(), "--manifest-path", mp.to_str().unwrap(), "--lib"]);
        assert_eq!(req.session.features, ["noembed"]);
        assert!(!req.session.default_features);
        // No config at all keeps the old default selection.
        std::fs::remove_file(dir.join(".lust.toml")).unwrap();
        let req = compile_req(&["check", lib.to_str().unwrap(), "--manifest-path", mp.to_str().unwrap(), "--lib"]);
        assert!(req.session.features.is_empty() && req.session.default_features);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Every TOML form Cargo reads for a dev profile key.
    #[test]
    fn toml_lookup_profile_forms() {
        let get = |t: &str| toml_lookup(t, "profile.dev.panic");
        assert_eq!(get("[profile.dev]\npanic = \"abort\" # x\n").as_deref(), Some("abort"));
        assert_eq!(get("[ profile . \"dev\" ]\npanic='abort'\n").as_deref(), Some("abort"));
        assert_eq!(get("[profile]\ndev.panic = \"abort\"\n").as_deref(), Some("abort"));
        assert_eq!(get("profile.dev.panic = \"abort\"\n[package]\n").as_deref(), Some("abort"));
        assert_eq!(get("[profile]\ndev = { opt-level = 1, panic = \"abort\" }\n").as_deref(), Some("abort"));
        assert_eq!(get("[profile.release]\npanic = \"abort\"\n[profile.dev.package.x]\npanic = \"abort\"\n"), None);
        assert_eq!(get("[[bin]]\npanic = \"abort\"\n# [profile.dev]\n"), None);
        assert_eq!(toml_lookup("[profile.dev]\ndebug-assertions = false\n", "profile.dev.debug-assertions").as_deref(), Some("false"));
    }

    /// Cargo's precedence: a `.cargo/config.toml` beats the workspace root
    /// manifest, a member manifest's profile is ignored, and a package
    /// with no setting unwinds.
    #[test]
    fn dev_profile_follows_cargo_precedence() {
        let dir = std::env::temp_dir().join(format!("lust-devprofile-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("m/src")).unwrap();
        let member = dir.join("m/Cargo.toml");
        std::fs::write(&member, "[package]\nname = \"m\"\n\n[profile.dev]\npanic = \"abort\"\n").unwrap();
        std::fs::write(dir.join("Cargo.toml"), "[workspace] # root\nmembers = [\"m\"]\n").unwrap();
        assert_eq!(dev_profile(&member), ProfileFlags::DEV_UNWIND, "member profiles are ignored");
        std::fs::write(dir.join("Cargo.toml"), "[workspace]\n\n[profile.dev]\npanic = \"abort\"\noverflow-checks = false\n").unwrap();
        let p = dev_profile(&member);
        assert!(p.panic_abort && !p.overflow_checks && p.debug_assertions);
        std::fs::create_dir_all(dir.join("m/.cargo")).unwrap();
        std::fs::write(dir.join("m/.cargo/config.toml"), "[profile.dev]\npanic = \"unwind\"\n").unwrap();
        assert!(!dev_profile(&member).panic_abort, "config beats the manifest");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Release defaults, a custom profile's inherits chain, env over config over manifest,
    /// and the errors for an undefined profile and an inherits cycle.
    #[test]
    fn cargo_profile_reads_any_profile() {
        let dir = std::env::temp_dir().join(format!("lust-cargoprofile-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let m = dir.join("Cargo.toml");
        std::fs::write(&m, "[package]\nname = \"p\"\n\n[profile.goport]\ninherits = \"release\"\nlto = \"fat\"\n\n[profile.chk]\ninherits = \"goport\"\noverflow-checks = true\n\n[profile.a]\ninherits = \"b\"\n[profile.b]\ninherits = \"a\"\n").unwrap();
        let rel = cargo_profile(Some(&m), "release").unwrap();
        assert_eq!(rel.flags, ProfileFlags { panic_abort: false, overflow_checks: false, debug_assertions: false });
        assert_eq!(rel.opt_level, "3");
        assert_eq!(cargo_profile(Some(&m), "goport").unwrap(), rel, "goport inherits release");
        let chk = cargo_profile(Some(&m), "chk").unwrap();
        assert!(chk.flags.overflow_checks && !chk.flags.debug_assertions, "a child key beats the inherited one");
        let dev = cargo_profile(Some(&m), "dev").unwrap();
        assert_eq!((dev.flags, dev.opt_level.as_str()), (ProfileFlags::DEV_UNWIND, "0"));
        assert_eq!(cargo_profile(Some(&m), "test").unwrap(), dev, "test inherits dev");
        assert!(cargo_profile(Some(&m), "nope").unwrap_err().contains("not defined"));
        assert!(cargo_profile(Some(&m), "a").unwrap_err().contains("cycle"));
        std::fs::create_dir_all(dir.join(".cargo")).unwrap();
        std::fs::write(dir.join(".cargo/config.toml"), "[profile.release]\nopt-level = 2\npanic = \"abort\"\n").unwrap();
        let g = cargo_profile(Some(&m), "goport").unwrap();
        assert!(g.flags.panic_abort && g.opt_level == "2", "config of the inherited profile applies");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// `-C overflow-checks` and `-C debug-assertions` set the session profile; a bad value
    /// or a release build with them is a usage error.
    #[test]
    fn rustc_profile_flags() {
        let p = compile_req(&["build", "x.rs", "-C", "overflow-checks=off", "-C", "debug-assertions=no"]).session.profile;
        assert!(!p.overflow_checks && !p.debug_assertions);
        let p = compile_req(&["build", "x.rs", "-C", "overflow-checks=on"]).session.profile;
        assert!(p.overflow_checks && p.debug_assertions);
        assert!(parse_args(&args(&["build", "x.rs", "-C", "overflow-checks=maybe"])).is_none());
        assert!(parse_args(&args(&["build", "x.rs", "--release", "-C", "overflow-checks=off"])).is_none());
    }
}
