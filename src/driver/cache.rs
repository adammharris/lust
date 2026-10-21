// Disk cache, three layers in one directory:
//   - Whole-request entries for cold (no-daemon) `lust check` and `lust build` runs.
//     An unchanged file with the same flags replays the stored response in a few
//     milliseconds: about 4 ms for check and 8 ms for build on the dev box.
//   - Per-C-unit objects (`unit-*`): a unit's compiled object keyed by compiler id,
//     debug flag, and the unit's full C text. The object is a function of those three
//     alone, so a hit is exactly as sound as running tcc. (An earlier key on IR
//     fingerprints and used slots missed slots that cgen prints by other routes, such
//     as a closure an adapter instance calls, and served stale objects after an edit
//     renumbered slots: fx-unitcache.) A restarted daemon or a cold build reuses the
//     object of every unit whose C did not change; only changed units go through tcc.
//   - The slot manifest per final bin (`slots-*`): DiskDefId to slot, so a restarted
//     daemon recovers the same slot assignment in any crate load order (8.4).
//
// Location: `.lust-cache/` next to the source file. `LUST_CACHE_DIR` overrides it.
// `LUST_NO_CACHE=1` turns it off. Size cap: `LUST_CACHE_MAX_BYTES` (default 512 MiB).
// The least recently stored or used entries are deleted first when the cap is passed, but
// never the unit objects the running build stored or took: the next build of the same
// source needs them all (a tsgo release C build holds about 1 GB of objects).
//
// Trust rule: the cache is trusted like ccache's local cache. A stored build result is copied
// out and can run. Never commit `.lust-cache/` and never use a cache from an untrusted source
// (see README).
//
// Entry key = compiler id + source bytes + source path + command and flags + target.
// Compiler id = build hash compiled into the binary (compiler sources and the tcc tree at
// build time; see build.rs) mixed with a run-time hash of the tcc binary and its runtime
// files, so an in-place tcc upgrade misses too. `LUST_CACHE_COMPILER_ID` mixes an extra
// string into the id (tests use it to stand in for a rebuilt compiler).
use crate::def::DiskDefId;
use crate::intern::FxMap;
use crate::protocol::{Cmd, Request, Response, SessionKey};

/// True when the root source routes through the resolver (modules, cfg,
/// imports): its answer depends on files outside `src`.
fn src_needs_resolve(src: &[u8]) -> bool {
    match std::str::from_utf8(src) {
        Ok(text) => {
            let interner = crate::intern::Interner::default();
            crate::resolve::worklist::needs_resolve(text, &interner)
        }
        Err(_) => true,
    }
}
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;

const DEFAULT_MAX_BYTES: u64 = 512 * 1024 * 1024;

/// Two-lane multiply-xor hash over 8-byte chunks. One multiply per chunk per lane,
/// so hashing the source plus the tcc runtime (about 2 MB) stays under a millisecond.
/// The cache is local and trusted, so 128 bits of a fast hash is the right tool.
/// Also used to content-name base libraries (driver::compile).
pub(crate) fn hash128(parts: &[&[u8]], seed: u64) -> (u64, u64) {
    let (mut a, mut b) = (seed ^ 0x243F_6A88_85A3_08D3, seed ^ 0x1319_8A2E_0370_7344);
    let mut total: u64 = 0;
    let step = |h: u64, x: u64, rot: u32, prime: u64| (h.rotate_left(rot) ^ x).wrapping_mul(prime);
    for part in parts {
        total = total.wrapping_add(part.len() as u64);
        // Length prefix, so ["ab", "c"] and ["a", "bc"] differ.
        a = step(a, part.len() as u64, 5, 0x517C_C1B7_2722_0A95);
        b = step(b, part.len() as u64, 11, 0x9E37_79B9_7F4A_7C15);
        let mut chunks = part.chunks_exact(8);
        for c in &mut chunks {
            let x = u64::from_le_bytes(c.try_into().unwrap());
            a = step(a, x, 5, 0x517C_C1B7_2722_0A95);
            b = step(b, x.rotate_left(32), 11, 0x9E37_79B9_7F4A_7C15);
        }
        let rem = chunks.remainder();
        if !rem.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rem.len()].copy_from_slice(rem);
            let x = u64::from_le_bytes(buf);
            a = step(a, x, 5, 0x517C_C1B7_2722_0A95);
            b = step(b, x.rotate_left(17), 11, 0x9E37_79B9_7F4A_7C15);
        }
    }
    (mix(a ^ total), mix(b ^ total.rotate_left(29)))
}

/// One splitmix-style finalizer step.
fn mix(mut x: u64) -> u64 {
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

/// The cache directory for a source file: `$LUST_CACHE_DIR`, else `<source dir>/.lust-cache`.
pub fn cache_dir(src_file: &Path) -> PathBuf {
    match std::env::var_os("LUST_CACHE_DIR") {
        Some(d) if !d.is_empty() => PathBuf::from(d),
        _ => src_file.parent().map_or_else(|| PathBuf::from("."), Path::to_path_buf).join(".lust-cache"),
    }
}

/// True when an env flag is set to a value other than "" or "0".
fn env_on(name: &str) -> bool {
    matches!(std::env::var(name), Ok(v) if !v.is_empty() && v != "0")
}

/// Hashes the tcc binary and every file under its runtime dir (names and bytes, sorted).
/// About 1 MB on this setup, so well under a millisecond at hash128 speed.
fn tcc_hash() -> (u64, u64) {
    let (lib, bin) = crate::tcc::tcc_paths();
    let mut files = vec![bin];
    let mut stack = vec![lib];
    while let Some(d) = stack.pop() {
        if let Ok(rd) = std::fs::read_dir(&d) {
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else {
                    files.push(p);
                }
            }
        }
    }
    files.sort();
    // Fold file by file so we never hold more than one file in memory next to the source.
    let (mut lo, mut hi) = hash128(&[b"tcc"], 0);
    for f in &files {
        let bytes = std::fs::read(f).unwrap_or_default();
        let (a, b) = hash128(&[f.to_string_lossy().as_bytes(), &bytes], lo ^ hi);
        lo = a;
        hi = b;
    }
    (lo, hi)
}

/// The compiler id for cache keys. See the module docs.
fn compiler_id() -> (u64, u64) {
    let tcc = tcc_hash();
    let extra = std::env::var("LUST_CACHE_COMPILER_ID").unwrap_or_default();
    hash128(&[env!("LUST_BUILD_HASH").as_bytes(), &tcc.0.to_le_bytes(), &tcc.1.to_le_bytes(), extra.as_bytes()], 7)
}

/// The `LUST_*` settings among `vars` that can change a build's answer, sorted, one
/// `name=value` line each: all but those that only steer the process (daemon, cache
/// location, threads, logs). A setting not listed here is keyed, so a new one costs a miss,
/// never a wrong hit (rel-opt: a `LUST_UNWIND_TABLES=1 LUST_RELEASE_C=1` build's binary
/// was replayed to a plain build of the same file).
fn env_key(vars: impl Iterator<Item = (String, String)>) -> String {
    const STEERING: &[&str] = &[
        "LUST_NO_DAEMON",
        "LUST_DAEMON_SOCKET",
        "LUST_DAEMON_IDLE",
        "LUST_CACHE_DIR",
        "LUST_CACHE_MAX_BYTES",
        "LUST_CACHE_COMPILER_ID",
        "LUST_THREADS",
        "LUST_STATS",
        "LUST_VISITS_LOG",
        "LUST_TCC_HOME",
        "LUST_SOURCES_READY",
    ];
    let mut set: Vec<(String, String)> = vars.filter(|(k, _)| k.starts_with("LUST_") && !STEERING.contains(&k.as_str())).collect();
    set.sort();
    set.iter().map(|(k, v)| format!("{k}={v}\n")).collect()
}

/// The whole-request key for `req` over `src` bytes: compiler id, target, path, flags,
/// the `LUST_*` settings (`env_key`), source.
/// The session key text (`SessionKey::describe`, which names every field) is in
/// the key, so two crate selections of one file never replay each other's
/// stored answer. `--timings` is not in the key: stored responses keep no timing
/// text, and a hit makes its own timing line. `out` is not in the key: the built
/// bytes do not depend on the out name.
fn request_key(id: (u64, u64), req: &Request, src: &[u8]) -> String {
    let target = format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS);
    let cmd: &[u8] = if req.cmd == Cmd::Check { b"check" } else { b"build" };
    let flags = [req.json as u8, req.debug as u8];
    let session = req.session.describe();
    // The graph key and the build script output hash (section 1.1):
    // editing Cargo.toml, Cargo.lock, a cargo config, or a build script
    // input must miss a stored whole-request answer instead of
    // replaying one resolved under the old graph. The build script
    // check only hashes recorded inputs while they hold; a stale
    // record re-runs the script through Cargo here.
    // Build script first, graph after: a stale re-run can create
    // Cargo.lock, and the key must describe the post-run graph.
    let build_script = match crate::protocol::manifest_dir(&req.session) {
        Some(dir) => crate::driver::buildscript::refresh(&dir, &cache_dir(&req.file), req.client.env.as_deref()).hash(),
        None => 0,
    };
    let graph = crate::protocol::graph_key(&req.session);
    // The root path as typed: `file!`, `dbg!`, and panic locations show it.
    let shown = req.client.shown.as_deref().map_or(&[][..], |p| p.as_os_str().as_encoded_bytes());
    let env = env_key(std::env::vars());
    let (a, b) = hash128(
        &[
            &id.0.to_le_bytes(),
            &id.1.to_le_bytes(),
            target.as_bytes(),
            cmd,
            &flags,
            &req.max_errors.to_le_bytes(),
            req.file.to_string_lossy().as_bytes(),
            shown,
            session.as_bytes(),
            &graph.to_le_bytes(),
            &build_script.to_le_bytes(),
            env.as_bytes(),
            src,
        ],
        13,
    );
    format!("{a:016x}{b:016x}")
}

/// One open cache: its directory and the key prefix for every entry this process writes.
pub struct Cache {
    dir: PathBuf,
    id: (u64, u64),
}

/// Per cache dir, the unit object files the running build stored or took: `evict` keeps
/// them. Per process, as a build can store through two `Cache`s (the session's and the
/// whole-request one); per dir, so a build that starts on one dir (`begin_build`) leaves
/// other dirs' builds alone (a daemon's sessions, parallel tests).
type Used = std::collections::HashMap<PathBuf, std::collections::HashSet<String>>;
static USED: std::sync::Mutex<Option<Used>> = std::sync::Mutex::new(None);

/// Starts a build of `src_file`: the unit objects earlier builds of this process (a
/// daemon) used in its cache dir may be evicted again.
pub fn begin_build(src_file: &Path) {
    forget_used(&cache_dir(src_file));
}

fn forget_used(dir: &Path) {
    if let Some(u) = USED.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
        u.remove(dir);
    }
}

/// True when the source mentions a macro whose result depends on data
/// outside the source bytes (`env!`, `option_env!`, the `include!`
/// family): such a request never enters this cache, since its key
/// cannot see env vars or included files (added for W-MACRO).
fn src_reads_outside(src: &[u8]) -> bool {
    const NEEDLES: &[&[u8]] = &[b"env!", b"option_env!", b"include!", b"include_str!", b"include_bytes!"];
    NEEDLES.iter().any(|n| src.windows(n.len()).any(|w| w == *n))
}

impl Cache {
    /// Opens the cache for `src_file`. None when turned off or the dir cannot be made.
    pub fn open(src_file: &Path) -> Option<Cache> {
        // A std or adapter source override: the compiler id does not cover that tree.
        if env_on("LUST_NO_CACHE") || crate::protocol::source_override().is_some() || crate::driver::has_source_overlay() {
            return None;
        }
        let dir = cache_dir(src_file);
        std::fs::create_dir_all(&dir).ok()?;
        Some(Cache { dir, id: compiler_id() })
    }

    fn entry_path(&self, key: &str, ext: &str) -> PathBuf {
        self.dir.join(format!("req-{key}{ext}"))
    }

    /// A cache in `dir` (tests).
    #[cfg(test)]
    pub(crate) fn at(dir: &Path) -> Cache {
        std::fs::create_dir_all(dir).unwrap();
        Cache { dir: dir.to_path_buf(), id: (1, 2) }
    }

    /// The disk key of one C unit's object: compiler id, debug flag, and
    /// the unit's C text. See the module docs.
    pub fn unit_key(&self, c_text: &str, debug: bool) -> String {
        let (a, b) = hash128(&[&self.id.0.to_le_bytes(), &self.id.1.to_le_bytes(), &[debug as u8], b"unit-v3", c_text.as_bytes()], 29);
        format!("{a:016x}{b:016x}")
    }

    /// Puts the cached unit object under `key` (see `unit_key`) at `dest`: a hard link
    /// (a warm tsgo release takes ~500 MB of hits; a link moves no bytes), or a copy
    /// across file systems. Whoever writes `dest` later removes it first: a compiler
    /// that wrote its output in place would change the entry (gcc's as, tcc and clang
    /// replace the file; the removal covers any other `LUST_CC`).
    /// False on a miss (no entry, or neither worked): the caller compiles the unit. A
    /// hit makes the entry the most recently used.
    pub fn unit_object(&self, key: &str, dest: &Path) -> bool {
        let name = format!("unit-{key}.o");
        let path = self.dir.join(&name);
        let _ = std::fs::remove_file(dest);
        if std::fs::hard_link(&path, dest).is_err() && std::fs::copy(&path, dest).is_err() {
            return false;
        }
        let _ = std::fs::File::options().write(true).open(&path).and_then(|f| f.set_modified(std::time::SystemTime::now()));
        self.note_used(name);
        true
    }

    /// Whether the cache holds a unit object under `key` (`cc::build` asks before it takes
    /// a unit's key from the memo instead of its text).
    pub fn has_unit_object(&self, key: &str) -> bool {
        self.unit_object_path(key).is_file()
    }

    /// Where the cache keeps the unit object of `key`.
    pub fn unit_object_path(&self, key: &str) -> PathBuf {
        self.dir.join(format!("unit-{key}.o"))
    }

    /// Stores a freshly compiled unit object under `key`. The build evicts once
    /// after its last store (`evict_objects`).
    pub fn store_unit_object(&self, key: &str, obj: &Path) {
        let name = format!("unit-{key}.o");
        self.copy_in(obj, &self.dir.join(&name));
        self.note_used(name);
    }

    fn note_used(&self, name: String) {
        USED.lock().unwrap_or_else(|e| e.into_inner()).get_or_insert_with(Default::default).entry(self.dir.clone()).or_default().insert(name);
    }

    /// The size-cap eviction of a build that stored unit objects, run once after them.
    pub fn evict_objects(&self) {
        self.evict("");
    }

    /// The manifest file for one session selection. The session text
    /// (`describe`) names every routing field, so two selections of one
    /// bin never share a manifest.
    fn slot_manifest_path(&self, session: &SessionKey) -> PathBuf {
        let (a, _) = hash128(&[session.describe().as_bytes()], 31);
        self.dir.join(format!("slots-{a:016x}.bin"))
    }

    /// The stored slot manifest for `session`, if a previous daemon or
    /// build left a valid one. A sparse map (a slot above the entry
    /// count) is rejected here even though the codec allows it as
    /// bytes: slot assignment appends at the entry count and would
    /// collide with the sparse slot later.
    pub fn load_slot_manifest(&self, session: &SessionKey) -> Option<(FxMap<DiskDefId, u32>, u32)> {
        let bytes = std::fs::read(self.slot_manifest_path(session)).ok()?;
        let (map, unit_bytes) = super::session::decode_slot_manifest(&bytes)?;
        if map.values().copied().max().is_some_and(|m| m as usize >= map.len()) {
            return None;
        }
        Some((map, unit_bytes))
    }

    /// The def-order file for one session selection, next to its
    /// slot manifest under the same session hash.
    fn def_order_path(&self, session: &SessionKey) -> PathBuf {
        let (a, _) = hash128(&[session.describe().as_bytes()], 31);
        self.dir.join(format!("defs-{a:016x}.bin"))
    }

    /// The stored def order for `session`, if a previous daemon or
    /// build left a valid one for this crate identity (`stable`).
    /// A missing, bad, or foreign-crate file is `None`; the caller
    /// then numbers defs fresh.
    pub fn load_def_order(&self, session: &SessionKey, stable: crate::def::StableCrateHash) -> Option<crate::check::collect::DefOrder> {
        let bytes = std::fs::read(self.def_order_path(session)).ok()?;
        super::session::decode_def_order(&bytes, stable)
    }

    /// Stores the def order for `session` (atomic, as every write here).
    pub fn store_def_order(&self, session: &SessionKey, order: &crate::check::collect::DefOrder, stable: crate::def::StableCrateHash) {
        let bytes = super::session::encode_def_order(order, stable);
        self.write(&self.def_order_path(session), &bytes);
    }

    /// Stores the slot manifest for `session` (atomic, as every write here).
    pub fn store_slot_manifest(&self, session: &SessionKey, slot_of: &FxMap<DiskDefId, u32>, unit_bytes: u32) {
        let bytes = super::session::encode_slot_manifest(slot_of, unit_bytes);
        self.write(&self.slot_manifest_path(session), &bytes);
    }

    /// Looks up `req`. On a build hit, copies the stored executable to `req.out`.
    /// The caller gives the source bytes it read, so the file is read once per process.
    /// A stored `--timings` text never exists; a hit with timings gets one fresh line.
    pub fn lookup(&self, req: &Request, src: &[u8], start: Instant) -> Option<Response> {
        // A multi-file crate (or a manifest-selected one) is not keyed by
        // the root file's bytes alone: module files and Cargo inputs are
        // outside this key, so those requests skip the cache entirely
        // until the per-node disk cache of section 8.4 exists.
        if src_reads_outside(src) || req.session.krate.manifest_path.is_some() || src_needs_resolve(src) {
            return None;
        }
        let key = request_key(self.id, req, src);
        let bytes = std::fs::read(self.entry_path(&key, "")).ok()?;
        let mut resp = decode_response(&bytes)?;
        if req.cmd == Cmd::Build && resp.code == 0 {
            std::fs::copy(self.entry_path(&key, ".exe"), &req.out).ok()?;
        }
        if req.timings && resp.code == 0 {
            let cmd = if req.cmd == Cmd::Check { "check" } else { "build" };
            let ms = start.elapsed().as_secs_f64() * 1e3;
            let _ =
                writeln!(resp.stderr, "lust {cmd} {}: ok (whole-request cache hit)\n  {:<24} {ms:>9.2} ms", req.file.display(), "total");
        }
        Some(resp)
    }

    /// Stores `resp` for `req`. Code 3 (internal or tcc failure) is never stored.
    /// A successful response keeps no stderr: its only stderr text is `--timings` output,
    /// which must not replay. After the write, oldest entries are evicted past the cap.
    pub fn store(&self, req: &Request, src: &[u8], resp: &Response) {
        if resp.code == 3 || src_reads_outside(src) {
            return;
        }
        if req.session.krate.manifest_path.is_some() || src_needs_resolve(src) {
            return;
        }
        let key = request_key(self.id, req, src);
        if req.cmd == Cmd::Build && resp.code == 0 {
            self.copy_in(&req.out, &self.entry_path(&key, ".exe"));
        }
        let clean = Response {
            stdout: resp.stdout.clone(),
            stderr: if resp.code == 0 { String::new() } else { resp.stderr.clone() },
            code: resp.code,
            ran: false,
        };
        self.write(&self.entry_path(&key, ""), &encode_response(&clean));
        self.evict(&format!("req-{key}"));
    }

    /// Deletes the least recently stored or used entries until the cache fits the size
    /// cap. The entry file named `keep` and the unit objects the running build stored or
    /// took are never deleted.
    /// Whole-request entries (`req-*`, plus their `.exe`) and unit objects
    /// (`unit-*.o`, one file each) are evictable; slot manifests are small
    /// and pinned (deleting one only costs a renumber, but the cap is about
    /// object bulk, not manifests).
    fn evict(&self, keep: &str) {
        let cap = std::env::var("LUST_CACHE_MAX_BYTES").ok().and_then(|v| v.parse::<u64>().ok()).unwrap_or(DEFAULT_MAX_BYTES);
        self.evict_to(cap, keep);
    }

    /// `evict` with the cap given.
    fn evict_to(&self, cap: u64, keep: &str) {
        let Ok(rd) = std::fs::read_dir(&self.dir) else { return };
        // (mtime, path, len) for every entry file; a `req-<key>` file is one entry.
        let mut entries: Vec<(std::time::SystemTime, PathBuf, u64)> = Vec::new();
        let mut total: u64 = 0;
        for e in rd.flatten() {
            let Ok(meta) = e.metadata() else { continue };
            if !meta.is_file() {
                continue;
            }
            total += meta.len();
            let name = e.file_name().to_string_lossy().into_owned();
            if name.starts_with("unit-") && name.ends_with(".o") {
                entries.push((meta.modified().unwrap_or(std::time::UNIX_EPOCH), e.path(), meta.len()));
            } else if name.starts_with("req-") && !name.ends_with(".exe") {
                let mut size = meta.len();
                if let Ok(exe) = std::fs::metadata(self.dir.join(format!("{name}.exe"))) {
                    size += exe.len();
                }
                entries.push((meta.modified().unwrap_or(std::time::UNIX_EPOCH), e.path(), size));
            }
        }
        if total <= cap {
            return;
        }
        entries.sort();
        let used = USED.lock().unwrap_or_else(|e| e.into_inner());
        let used = |n: &str| used.as_ref().and_then(|u| u.get(&self.dir)).is_some_and(|u| u.contains(n));
        for (_, path, size) in entries {
            if total <= cap {
                break;
            }
            if path.file_name().is_some_and(|n| n.to_string_lossy() == keep || used(&n.to_string_lossy())) {
                continue;
            }
            let mut exe = path.as_os_str().to_owned();
            exe.push(".exe");
            let _ = std::fs::remove_file(PathBuf::from(exe));
            let _ = std::fs::remove_file(&path);
            total = total.saturating_sub(size);
        }
    }

    /// Writes atomically (temp file, then rename), so a reader never sees half a file.
    fn write(&self, p: &Path, bytes: &[u8]) {
        let tmp = self.tmp_for(p);
        if std::fs::write(&tmp, bytes).is_ok() && std::fs::rename(&tmp, p).is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }

    /// Copies a file into the cache atomically. See `write`.
    fn copy_in(&self, from: &Path, p: &Path) {
        let tmp = self.tmp_for(p);
        if std::fs::copy(from, &tmp).is_ok() && std::fs::rename(&tmp, p).is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }

    fn tmp_for(&self, p: &Path) -> PathBuf {
        let mut s = p.as_os_str().to_owned();
        s.push(format!(".tmp{}", std::process::id()));
        PathBuf::from(s)
    }
}

/// Stores a response as: code (4 bytes LE), stdout len (8 bytes LE), stdout, stderr.
fn encode_response(r: &Response) -> Vec<u8> {
    let mut out = Vec::with_capacity(12 + r.stdout.len() + r.stderr.len());
    out.extend_from_slice(&r.code.to_le_bytes());
    out.extend_from_slice(&(r.stdout.len() as u64).to_le_bytes());
    out.extend_from_slice(r.stdout.as_bytes());
    out.extend_from_slice(r.stderr.as_bytes());
    out
}

/// Reads a response stored by `encode_response`. None on any shape error (a miss, in effect).
fn decode_response(b: &[u8]) -> Option<Response> {
    let code = i32::from_le_bytes(b.get(0..4)?.try_into().ok()?);
    let n = u64::from_le_bytes(b.get(4..12)?.try_into().ok()?) as usize;
    let stdout = String::from_utf8(b.get(12..12 + n)?.to_vec()).ok()?;
    let stderr = String::from_utf8(b.get(12 + n..)?.to_vec()).ok()?;
    Some(Response { stdout, stderr, code, ran: false })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::SessionKey;

    fn req(cmd: Cmd, json: bool, debug: bool) -> Request {
        Request {
            cmd,
            session: SessionKey::synthetic(std::path::Path::new("/tmp/x/main.rs"), false),
            file: "/tmp/x/main.rs".into(),
            out: "/tmp/x/main".into(),
            json,
            timings: false,
            debug,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false, cc: false,
            client: Default::default(),
        }
    }

    /// Each key input named in the module docs must change the key on its own.
    #[test]
    fn key_inputs_change_the_key() {
        let id = (1, 2);
        let base = request_key(id, &req(Cmd::Check, false, false), b"fn main() {}");
        assert_ne!(base, request_key(id, &req(Cmd::Check, false, false), b"fn main() { }"), "source edit");
        assert_ne!(base, request_key(id, &req(Cmd::Build, false, false), b"fn main() {}"), "command");
        assert_ne!(base, request_key(id, &req(Cmd::Check, true, false), b"fn main() {}"), "json flag");
        assert_ne!(base, request_key(id, &req(Cmd::Check, false, true), b"fn main() {}"), "debug flag");
        assert_ne!(base, request_key((9, 2), &req(Cmd::Check, false, false), b"fn main() {}"), "compiler id");
        let mut other = req(Cmd::Check, false, false);
        other.max_errors = 3;
        assert_ne!(base, request_key(id, &other, b"fn main() {}"), "max errors");
        let mut other = req(Cmd::Check, false, false);
        other.file = "/tmp/y/main.rs".into();
        assert_ne!(base, request_key(id, &other, b"fn main() {}"), "source path");
        let mut other = req(Cmd::Check, false, false);
        other.client.shown = Some("main.rs".into());
        assert_ne!(base, request_key(id, &other, b"fn main() {}"), "typed root path");
        let mut other = req(Cmd::Check, false, false);
        other.session.features = vec!["alpha".into()];
        assert_ne!(base, request_key(id, &other, b"fn main() {}"), "feature selection");
        let mut other = req(Cmd::Check, false, false);
        other.session.target_triple = "x86_64-unknown-linux-gnu".into();
        assert_ne!(base, request_key(id, &other, b"fn main() {}"), "target triple");
        assert_eq!(base, request_key(id, &req(Cmd::Check, false, false), b"fn main() {}"), "stable");
    }

    /// Each unit-object key input must change the key on its own, and a
    /// stored unit object copies back out byte for byte.
    /// Every `LUST_*` setting but the process-steering ones goes into the request key,
    /// whatever its order in the environment.
    #[test]
    fn request_keys_hold_the_lust_settings() {
        let vars = |v: &[(&str, &str)]| v.iter().map(|(k, x)| (k.to_string(), x.to_string())).collect::<Vec<_>>().into_iter();
        let key = env_key(vars(&[("LUST_RELEASE_C", "1"), ("PATH", "/bin"), ("LUST_NO_DAEMON", "1"), ("LUST_UNWIND_TABLES", "1"), ("LUST_THREADS", "4")]));
        assert_eq!(key, "LUST_RELEASE_C=1\nLUST_UNWIND_TABLES=1\n");
        assert_eq!(key, env_key(vars(&[("LUST_UNWIND_TABLES", "1"), ("LUST_RELEASE_C", "1")])));
        assert_eq!(env_key(vars(&[("LUST_CACHE_DIR", "/c"), ("HOME", "/h")])), "");
    }

    #[test]
    fn unit_objects_round_trip_and_key_on_every_input() {
        let dir = std::env::temp_dir().join(format!("lust-unit-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let cache = Cache { dir: dir.clone(), id: (3, 4) };
        let base = cache.unit_key("int f(void);", false);
        // Any C change misses, even one only a slot number apart.
        assert_ne!(base, cache.unit_key("int g(void);", false), "C text");
        assert_ne!(base, cache.unit_key("int f(void);", true), "debug flag");
        assert_ne!(base, Cache { dir: dir.clone(), id: (5, 4) }.unit_key("int f(void);", false), "compiler id");
        let obj = dir.join("made.o");
        std::fs::write(&obj, b"fake-object").unwrap();
        let dest = dir.join("dest.o");
        assert!(!cache.unit_object(&base, &dest), "miss before store");
        cache.store_unit_object(&base, &obj);
        assert!(cache.unit_object(&base, &dest), "hit after store");
        assert_eq!(std::fs::read(&dest).unwrap(), b"fake-object");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A build keeps every unit object it stored or took, even past the size cap (a tsgo
    /// release stores about 1 GB, twice the default cap, and evicted its own objects); the
    /// next build's eviction deletes the least recently used objects first.
    #[test]
    fn eviction_keeps_the_running_builds_objects() {
        let dir = std::env::temp_dir().join(format!("lust-evict-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let obj = dir.join("made.o");
        std::fs::write(&obj, b"0123456789").unwrap();
        let present = |k: &str| dir.join(format!("unit-{k}.o")).exists();
        forget_used(&dir);
        let first = Cache { dir: dir.clone(), id: (3, 4) };
        for k in ["a", "b", "c"] {
            first.store_unit_object(k, &obj);
        }
        first.evict_to(15, "");
        assert!(["a", "b", "c"].iter().all(|k| present(k)), "the running build's objects stay past the cap");
        // The next build takes b and stores d: a and c, unused by it, go.
        forget_used(&dir);
        let next = Cache { dir: dir.clone(), id: (3, 4) };
        assert!(next.unit_object("b", &dir.join("dest.o")));
        next.store_unit_object("d", &obj);
        next.evict_to(15, "");
        assert_eq!(["a", "b", "c", "d"].map(present), [false, true, false, true]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A stored slot manifest loads back for the same session key and not
    /// for another selection; a sparse map is rejected at load.
    #[test]
    fn slot_manifest_round_trips_per_session() {
        use crate::def::{DefPathHash, StableCrateHash};
        let dir = std::env::temp_dir().join(format!("lust-slots-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let cache = Cache { dir: dir.clone(), id: (3, 4) };
        let key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false);
        let disk = |h: u64| DiskDefId { krate: StableCrateHash(1), hash: DefPathHash(h) };
        let mut slots = FxMap::default();
        slots.insert(disk(10), 0);
        slots.insert(disk(20), 1);
        assert_eq!(cache.load_slot_manifest(&key), None, "miss before store");
        cache.store_slot_manifest(&key, &slots, 18);
        assert_eq!(cache.load_slot_manifest(&key), Some((slots.clone(), 18)));
        let other = SessionKey::synthetic(Path::new("/tmp/x/other.rs"), false);
        assert_eq!(cache.load_slot_manifest(&other), None, "another selection has its own manifest");
        let mut sparse = FxMap::default();
        sparse.insert(disk(10), 5);
        cache.store_slot_manifest(&other, &sparse, 0);
        assert_eq!(cache.load_slot_manifest(&other), None, "sparse manifests are rejected");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn response_round_trips() {
        let r = Response { stdout: "{\"code\":\"L0301\"}\n".into(), stderr: "err\n".into(), code: 1, ran: false };
        let back = decode_response(&encode_response(&r)).unwrap();
        assert_eq!((back.stdout.as_str(), back.stderr.as_str(), back.code), (r.stdout.as_str(), r.stderr.as_str(), 1));
        assert!(decode_response(b"short").is_none());
    }
}
