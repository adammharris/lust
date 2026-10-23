// Links the pinned libtcc built by scripts/build-tcc.sh, and bakes in its runtime path.
// Also bakes in a build hash (compiler sources plus the tcc binary and runtime files at build
// time). The disk cache uses it as part of the compiler id, so a rebuilt compiler never reads
// entries made by an older one.
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

/// Appends `file` to `out` with each `#include` of a file next to it or in `dirs` replaced
/// by that file's text. Each file goes in once (`seen`): mimalloc's
/// headers have include guards, so later copies would be empty. False when a file cannot be
/// read.
fn inline_includes(file: &Path, dirs: &[PathBuf], seen: &mut Vec<PathBuf>, out: &mut String) -> bool {
    let Ok(text) = std::fs::read_to_string(file) else { return false };
    seen.push(file.to_path_buf());
    for line in text.lines() {
        // `#include "x"`, or `#include <x>` of a header in `dirs` (mimalloc.h names its own
        // mimalloc-stats.h that way); system headers stay.
        let t = line.trim_start();
        let name = t.strip_prefix("#include \"").and_then(|r| r.split('"').next()).or_else(|| t.strip_prefix("#include <").and_then(|r| r.split('>').next()));
        let found = name.and_then(|n| {
            let here = file.parent().map(|d| d.join(n));
            here.into_iter().chain(dirs.iter().map(|d| d.join(n))).find(|p| p.is_file())
        });
        match found {
            Some(p) if !seen.contains(&p) => {
                if !inline_includes(&p, dirs, seen, out) {
                    return false;
                }
            }
            Some(_) => {}
            None => {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    true
}

/// Hashes every file under `dir` (names and bytes, sorted) into `h`.
fn hash_tree(h: &mut std::collections::hash_map::DefaultHasher, dir: &Path) {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
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
    for f in files {
        f.strip_prefix(dir).unwrap_or(&f).to_string_lossy().hash(h);
        if let Ok(bytes) = std::fs::read(&f) {
            bytes.hash(h);
        }
    }
}

fn main() {
    let root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let tcc = std::env::var("LUST_TCC_HOME").map(PathBuf::from).unwrap_or_else(|_| root.join("third_party/tcc"));
    let lib = tcc.join("lib");
    if !lib.join("libtcc.a").exists() {
        panic!("libtcc.a not found in {}. Run scripts/build-tcc.sh first.", lib.display());
    }
    println!("cargo:rustc-link-search=native={}", lib.display());
    println!("cargo:rustc-link-lib=static=tcc");
    // The compile runs on the main thread (see `raise_stack_limit` in main.rs), which needs
    // pool::STACK_SIZE (256 MiB). macOS fixes the main stack's size at exec, from the binary,
    // and setrlimit cannot grow it later: give the size to the linker.
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!("cargo:rustc-link-arg-bin=lust-core=-Wl,-stack_size,0x10000000");
    }
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("linux") {
        println!("cargo:rustc-link-lib=dylib=dl");
        println!("cargo:rustc-link-lib=dylib=pthread");
        println!("cargo:rustc-link-lib=dylib=m");
    }
    println!("cargo:rustc-env=LUST_TCC_LIB_PATH={}", lib.join("tcc").display());
    println!("cargo:rustc-env=LUST_TCC_BIN={}", tcc.join("bin/tcc").display());
    println!("cargo:rerun-if-env-changed=LUST_TCC_HOME");
    println!("cargo:rerun-if-changed=build.rs");
    // mimalloc, the allocator of musl release builds (src/cc.rs `mimalloc_unit`): its
    // static.c with every local include inlined, one C text, from the libmimalloc-sys this
    // crate builds with. Empty when its include dir is unknown (no unit then).
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let amalg = std::env::var("DEP_MIMALLOC_INCLUDE_DIR").ok().and_then(|inc| {
        let base = Path::new(&inc).parent()?.to_path_buf();
        let mut text = String::new();
        inline_includes(&base.join("src/static.c"), &[base.join("src"), base.join("include")], &mut Vec::new(), &mut text).then_some(text)
    });
    std::fs::write(out_dir.join("mimalloc.c"), amalg.unwrap_or_default()).unwrap();
    // Build hash: compiler sources, the shipped library sources (built into
    // the binary by src/stdload.rs, S5), the manifest, and the tcc tree.
    let mut h = std::collections::hash_map::DefaultHasher::new();
    hash_tree(&mut h, &root.join("src"));
    hash_tree(&mut h, &root.join("library"));
    if let Ok(bytes) = std::fs::read(root.join("Cargo.toml")) {
        bytes.hash(&mut h);
    }
    hash_tree(&mut h, &tcc.join("bin"));
    hash_tree(&mut h, &lib);
    println!("cargo:rustc-env=LUST_BUILD_HASH={:016x}", h.finish());
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=library");
    println!("cargo:rerun-if-changed=Cargo.toml");
    println!("cargo:rerun-if-changed={}", tcc.join("bin").display());
    println!("cargo:rerun-if-changed={}", lib.display());
}
