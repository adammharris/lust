<img src="assets/icon.svg" width="64" height="64" alt="Lust logo: a pink crab with a smiling face">

# lust-lang

Lust is an experiment. It asks one question: how fast can `check` and `build` of real Rust code get if the compiler supports only a subset of Rust, keeps a warm daemon, and gives up LLVM in dev builds?

To test this, lust compiles a subset of Rust. Every program lust accepts must be valid Rust (rustc 1.99, edition 2024), and it must give the same output as the `rustc` build. When lust cannot match rustc, it rejects the program with an error code. That rule makes `rustc` a free test oracle, and it gives lust programs a release path: Cargo builds the release binary from the same source.

**Status: early, but it compiles one real project.** About 250k lines of Rust and C in `src/`, plus 44k lines of std and adapter source in `library/`. It has a real type checker, trait solver, and borrow checker, and it reads Cargo workspaces. It checks and builds [ts-rust](https://github.com/pingdotgg/ts-rust) v0.7.0, a Rust port of the TypeScript compiler, with a small set of rewrites. In the 2026-10-17 census, `lust check` passes 18 of 18 targets and `lust build` builds 11 of 11 bins. The lust-built bins give the same stdout, stderr, exit code, and written files as the Cargo-built bins on 540 of 540 fixture runs, 7 of 7 integration test bins, and 12 of 12 tool runs. 683 of 683 unit tests built by lust give the same result. The ts-rust changes are in [pingdotgg/ts-rust#93](https://github.com/pingdotgg/ts-rust/pull/93), which moves the ts-rust dev check loop to lust: 6 commits (74 files) on top of upstream v0.7.0, plus docs. Under Cargo, a normal run behaves the same; only a few error texts change. Lust dev builds turn off jemalloc, the embedded lib snapshots, and real backtraces. The rewrites include a JSON reader in place of serde in two codegen tools (no proc macros), callbacks in place of futures for ATA requests (no `async`), named fns in place of closures in statics, named types in place of nested `impl Trait` and of `dyn WorkGroup<'a>`, the condition text as the message of 16 long `assert!` calls, and one `write_all` per `write!` in 8 `io::Write` impls. It is not a general Rust replacement. Most crates from crates.io will not compile: lust has no `async`, no `unsafe` code, no proc macros other than the built-in derives, and only 18 adapter crates for dependencies. Normal Rust also hits gaps. This will fail:

```rust
fn adders() -> Vec<impl Fn(u32) -> u32> { vec![|x| x + 1] } // lust: error[L0602], impl Trait inside a Vec
```

Read [DESIGN.md](DESIGN.md) and [docs/ARCH.md](docs/ARCH.md) as plans, not as a description of the code. Some parts are older than the code. [docs/PLAN.md](docs/PLAN.md) has the current plan. This README describes only what is in the tree today.

## Numbers

All numbers come from boat sandboxes: KVM machines with 16 vCPUs of an AMD Ryzen 9 9950X and 32 GB, x86_64 Linux, `rustc 1.99.0`, one job per sandbox. Each number names its date. Expect run-to-run variance: the sandboxes share hosts, and the same test can move 2x on a loaded day. Read the test shape before you read the speedup. The shape is most of the result.

Short version: on ts-rust, a warm lust daemon checks a one-line edit inside a function body about **60x to 250x** faster than `cargo check` at the median (more for larger crates). Signature edits are slower: 54 to 109 ms at the median, but 4 to 10 s at p95. A cold check is about **2.5x** faster than `cargo check` with the same features. Programs that lust builds run **slower** than `rustc` debug builds.

### Warm edit loop on ts-rust (the best case)

`scripts/tsedit.py` edits one function or item in a real ts-rust crate, asks the warm daemon to check it, then goes back to the base text. After each edit it also runs `cargo check` of the same target, in a warm target dir, with the same features as lust (ts-rust's `.lust.toml`). Both must accept or reject together. A third to a half of the edits are mistakes that rustc rejects. The tables count only the edits that rustc accepts.

Edit kinds: `body` (a `let` in a fn body), `generic` (a body edit in a generic fn), `macbody` (a body that calls `matches!`, `write!`, or `debug_assert!`), `oblig` (a body asks for a trait impl), `infer` (a `let` whose type comes from a later use), `sig` (a `where` clause on a real fn), `sigx` (a crate-root fn's types change, callers in other modules), `rpit` (a fn that returns `impl Trait`), `derive` (one trait removed from a `#[derive]`).

On ts-rust v0.7.0 (the PR branch `7459613a7`), lust v0.2.0 (`d80937461`), three kinds, 14 probes each, 2026-10-17 15:30 to 15:52 (`tsrust-pr-2`, final run). In v0.7.0 most of the code moved from `ts_goport` into `goport_core`, so `cargo check` of `ts_goport` is faster there:

| Crate | Kind | Edits | lust median | lust p95 | `cargo check` median | Speedup at the median |
|---|---|---:|---:|---:|---:|---:|
| `ts_goport` (148k lines) | body | 28 | 23.3 ms | 27.8 ms | 1,386 ms | 59x |
| | macbody | 28 | 22.7 ms | 36.9 ms | 1,400 ms | 62x |
| | sig | 28 | 53.5 ms | 4,446 ms | 1,447 ms | 27x |
| `goport_core` (430k lines) | body | 28 | 18.8 ms | 28.9 ms | 4,742 ms | 252x |
| | macbody | 28 | 25.1 ms | 58.5 ms | 5,103 ms | 203x |
| | sig | 28 | 109.1 ms | 9,924 ms | 10,497 ms | 96x |

At p95, signature edits take 4.4 to 9.9 s, about as long as `cargo check` or longer. The `goport_core` sandbox was slower during its sig edits (`cargo check` took 10.5 s there, not 4.7 s). 0 false accepts, 0 warm answers that differ from a cold check, 0 hangs. A second run made 12 body edits in 4 `goport_core` files and checked `ts_goport` (which builds `goport_core` too): lust median 24 ms, max 28 ms; `cargo check` median 5,708 ms (238x).

All nine kinds on an older pin of ts-rust (fork `61a13796b`, `ts_goport` with 523k lines before the crate split), seeds 1 to 6, 8 probes per kind, 2026-10-17 08:36 (`w-sig-delta`). The `cargo check` medians on these sandboxes were 5.6 to 8.8 s:

| Kind | Edits | lust median | vs `cargo check` | lust p95 |
|---|---:|---:|---:|---:|
| body | 96 | 22 ms | 310x | 117 ms |
| generic | 100 | 18 ms | 380x | 51 ms |
| macbody | 96 | 19 ms | 342x | 47 ms |
| oblig | 97 | 21 ms | 322x | 86 ms |
| infer | 144 | 20 ms | 359x | 66 ms |
| sig | 80 | 94 ms | 70x | 895 ms |
| sigx | 60 | 83 ms | 76x | 121 ms |
| rpit | 115 | 68 ms | 98x | 721 ms |
| derive | 48 | 90 ms | 78x | 218 ms |
| all | 836 | 29 ms | 236x | 260 ms |

A later fix (`cd151f564`, 13:25) took the p95 of all kinds to 117 ms (sig 126 ms, rpit 123 ms) on seeds 1 to 3. Edits that rustc rejects are slower: their lust answers have a median of 195 ms and a p95 of 2.1 s (10:46, seeds 1 to 6).

What makes this test favorable to lust:

- Every edit changes one function or one item, and then goes back. That is the case the daemon is built for. Wider edits, such as a change to a type that many files use or to a `mod` tree, take the full path: about 9 to 16 s on ts-rust, like the first check of a fresh daemon.
- Most edits hit a fast path. A body edit re-parses and re-checks one body. We tuned the daemon on these edit kinds, so other kinds of edits can be slower.
- Known slow cases: a rejected `rpit` edit takes about 2 s. A signature edit of a fn that a very large body reads (for example `handle_request`, 563 lines) checks that body again. A body with a user macro in the crate root file (`lib.rs`, `main.rs`) takes the full path.
- `cargo check` gets its fastest setup for this case: a warm target dir and incremental. It still checks the whole crate after each edit, because one crate is one unit for `rustc`. The speedup grows with the size of the crate: compare `ts_goport` and `goport_core` above.

Reproduce with `scripts/tsrust-full.sh --boat --tsedit` (census, then the bench on each lib target), or see `scripts/tsedit.py --help`.

### Cold check

`lust check` and `cargo check` of the `ts_goport` lib on the v0.7.0 fork pin (`ae1c76940`: upstream v0.7.0 plus the lust PR commits). Each run starts with an empty lust cache or an empty Cargo target dir, so both include the dependency crates. 3 interleaved runs of each command on one sandbox, medians, 2026-10-17. Three sandboxes, because the load on the host moved the times by 2x to 3x:

| Sandbox | `lust check` | `cargo check`, lust's features | `cargo check`, default features | Speedup, same features |
|---|---:|---:|---:|---:|
| A | 11.5 s | - | 54.6 s | - |
| B | 15.7 s | 37.1 s | - | 2.4x |
| C (slow host) | 27.4 s | 71.8 s | 169.5 s | 2.6x |

Peak RSS: `lust check` 1.43 to 1.51 GB, `cargo check` 1.86 to 1.88 GB.

The first `lust check` in a fresh daemon takes 15.0 to 16.1 s on sandbox A (2 runs). After that, a check with no change answers in 6 to 8 ms.

What makes this test favorable to lust:

- The cargo time includes building and running the build scripts of every dependency and checking them. Lust uses adapter crates for dependencies (`library/deps`) and does not compile the real crates.
- With default features, Cargo also builds jemalloc from C. Lust dev builds turn jemalloc off (ts-rust's `.lust.toml`), so the `--no-default-features` row is the fair one.
- A cold check is not the dev loop. With the dependencies built, `cargo check` after a one-line body edit takes 1.4 s (`ts_goport`) to 4.7 s (`goport_core`), and the warm daemon above is the lust number to compare with it.

Reproduce with the commands in [Build and use](#build-and-use) on a ts-rust checkout.

### Memory

The daemon keeps the whole program in memory. On ts_goport (fork pin `61a13796b`, 523k lines), 300 tsedit requests of mixed kinds, 2026-10-17 (`fx-daemonmem`):

| | before the fix | today |
|---|---:|---:|
| Daemon RSS after the first check | 14.1 GB | 4.84 GB |
| Daemon peak RSS over 300 requests | 20.4 GB | 5.7 GB |
| Cold one-shot check, peak RSS | 5.2 GB | 1.47 GB |

The ts-rust v0.7.0 tree is larger: there the daemon holds 6.6 GB after the first check (sandbox A above, 2 runs). The v0.1.0 release has the old memory use; v0.2.0 has the fix. We have not measured the 300-request peak on the v0.7.0 tree yet.

### Run speed

Lust compiles fast. Its programs do not run fast. The backend emits C and compiles it with `tcc`, which does not optimize. In daemon builds, every call also goes through a function table.

`tsgo -p tsconfig.json --noEmit` on the 35 fixture projects of `crates/ts_goport/tests/fixtures` (v0.7.0 fork pin, same features for all three builds, median of 3 runs, 2026-10-17). The output was the same on all 35. The table sums the 24 projects where the debug build takes 0.1 s or more:

| tsgo built by | total time | per project vs the Cargo debug build |
|---|---:|---:|
| `lust build` | 64.0 s | 3.8x to 4.9x slower |
| `cargo build` (debug) | 15.7 s | 1x |
| `cargo build --release` | 0.93 s | 11x to 32x faster |

The release times are 0.01 to 0.12 s, so their ratios are coarse. In total, the lust bin is about 70x slower than the release bin. That matters when an agent runs the project's tests after each edit. For a fast binary, use `lust build --release`, which hands the build to Cargo (or to `rustc -O` for one file).

## Why it is fast

Four reasons:

1. **No LLVM in dev builds.** Lust emits C and compiles it with `tcc`. `tcc` is much faster than LLVM and produces much worse code.
2. **Less language to check.** No proc macros, no `async`, and no `unsafe` code. Trait selection matches whole trait references against a deterministic impl index and does not search (docs/ARCH.md 2.4). Lifetimes use a restricted region model with stated rejects (docs/ARCH.md 5).
3. **Parallel work per function.** Type checking, borrow checking, and C code generation run per function, on a flat IR, across cores.
4. **The daemon redoes only what an edit touches.** See the next section.

The cold check is not fast for its size. It is about 2.5x faster than `cargo check` with the same features, not 100x. The speed claim is about the warm edit loop.

## How the daemon works

`lust daemon` serves one directory over a Unix socket (`.lust-daemon-<build>.sock` in that directory). You do not need to start it. When `check`, `build`, or `run` finds no daemon, the `lust` client answers that command cold and starts a daemon in the background. The next command is warm. The daemon keeps one warm session per crate selection (crate, target, features, profile).

On each edit, the daemon takes the cheapest path it can prove is the same as a cold compile:

1. **Body patch.** If every edit sits inside one fn body, it lexes and parses only that body, rewrites its paths against the last resolve's tables, and checks only that body. Bodies with macro calls patch when the macro is a pure builtin (`matches!`, `write!`, `debug_assert!`, and others).
2. **Signature delta.** If an edit changes the header of a plain fn, it applies the new signature to the kept program and checks again every body whose recorded reads moved.
3. **Full collect.** Anything else (a type, an `impl`, a `use`, a `mod`) resolves and collects the crate again. Even then, a body whose recorded reads are all unchanged is not checked again.

Each body check records what it read: each signature, each name binding, each impl bucket and method probe, and each failed lookup, with a fingerprint. An edit makes a body dirty only when one of its reads changed. Any condition the daemon cannot prove sends the request to the next, slower path.

Builds use the same idea. Every call goes through a function table, and each function owns one stable slot. The first build links all units into `libbase.so`. Later builds compile only the changed units and link a small executable that loads `libbase.so` and replaces the changed table entries. After 32 overlays, the daemon rebuilds the base. Daemon builds are not standalone: they load `libbase.so` from `.lust-cache/bases/`. A cold `lust build` links a standalone executable.

Two safety nets watch the warm answers:

- **The fresh-session guard.** When a warm answer is an error, the daemon sends it at once, then checks again in a fresh session in the background. If the answers differ, it logs a `guard:` line and drops the warm session.
- **Panics.** A panic in one request drops that session, and a fresh session answers the request.

The daemon exits after 30 idle minutes (`LUST_DAEMON_IDLE`, for example `10m`; `0` means never). `LUST_NO_DAEMON=1` turns it off. Its log is `.lust-cache/daemon.log`. Cold runs also use a disk cache in `.lust-cache/`. Do not commit or share it: a cached build can run, so treat it like a ccache directory.

## Build and use

Linux x86_64, and macOS arm64 from source. The daemon uses Unix sockets. Other platforms are not verified.

On macOS arm64 (2026-10-21), the differential tests pass 5591 of 5597 and the crate fixtures 93 of 93. Three of the failing cases use `std::os::linux`, so rustc rejects them there too. The other three print the size of a std lock type (`Mutex`, `RwLock`, `Condvar`, `OnceLock`): lust lays these out as on Linux (futex words), where macOS std holds a pointer. The persistent front image (`LUST_FRONT_STATE`) is Linux only; elsewhere a build runs without it.

### From the release

Download `lust-0.2.0-x86_64-linux.tar.gz` from the [releases](https://github.com/t3dotgg/lust-lang/releases) page, then:

```sh
tar xzf lust-0.2.0-x86_64-linux.tar.gz
export PATH="$PWD/lust-0.2.0-x86_64-linux/bin:$PATH"
lust --version
```

The package holds `lust`, `lust-core`, the pinned `tcc`, and the std and adapter sources. You also need glibc 2.38 or later, the C library development files (`libc6-dev` on Debian and Ubuntu), and Cargo to check a Cargo crate (lust reads `cargo metadata` and the registry sources).

### From source

You need a Rust toolchain and a C build environment. The first step clones `tinycc` from GitHub, so it needs network access once.

```sh
scripts/build-tcc.sh      # builds the pinned tinycc into third_party/tcc
cargo build --release     # builds `lust` (client) and `lust-core` (compiler)
scripts/release.sh        # optional: builds dist/lust-<version>-x86_64-linux.tar.gz
```

`scripts/build.sh` builds a profile that compiles faster, for test runs.

`third_party/ts-rust` is a git submodule. It points to a private fork of ts-rust that only the census scripts (`scripts/tsrust-full.sh`) use. You do not need it to build or use lust.

### Use

```sh
lust check main.rs [--json] [--timings]     # type check and borrow check
lust run main.rs [-- args]                  # build with tcc and run
lust build main.rs [-o out]                 # build a dev binary
lust test main.rs [filter]                  # run #[test] functions
lust check main.rs --rustc                  # ask the real rustc for a second opinion
lust build main.rs --release                # release build with Cargo (rustc -O for one file)
lust explain L0602                          # long help for one error code
lust capabilities --json                    # what the subset supports and rejects
```

A target in a Cargo workspace:

```sh
lust check crates/ts_goport/src/lib.rs --manifest-path crates/ts_goport/Cargo.toml --lib
lust build crates/ts_goport/src/bin/tsgo.rs --manifest-path crates/ts_goport/Cargo.toml --bin tsgo -o tsgo
lust test crates/twig-kit/src/lib.rs --manifest-path crates/twig-kit/Cargo.toml --lib [filter]
lust test crates/twig/tests/api.rs --manifest-path crates/twig/Cargo.toml --test api
```

`lust test` of a Cargo target runs the lib's unit tests (`--lib`) or one integration test (`--test <name>`), as `cargo test --lib` and `cargo test --test <name>` do: `cfg(test)` on for that crate only, dev-dependencies in, in the package directory with Cargo's runtime env (`CARGO_MANIFEST_DIR`, `CARGO_PKG_NAME`, ...). The tests run as libtest runs them: in one process, sorted by name, on threads named by the test (`--test-threads N`, else `RUST_TEST_THREADS`, else the core count), so tests share process state as under `cargo test`, and a panic fails only its test. libtest's flags work (filters, `--exact`, `--skip`, `--ignored`, `--include-ignored`), and the report has libtest's form. Two differences: test output is not captured (it goes to stderr, as under `--nocapture`), and a test that runs past `--timeout` (10 s by default) or ends the process fails alone, while the other tests run on in a new process. Tests in module files and inline modules count, a test that `cfg` turns off is no test, and a test that returns `Result` fails on `Err`. The harness goes into copies of the crate's files in memory, so the files on disk stay as they are (`LUST_TEST_KEEP=1` keeps the generated C and the test binary).

Crate flags work as in Cargo: `--features`, `--no-default-features`, `--all-features`, `--package`, `--target`, `--offline`, `--locked`. A project can drop features from lust dev builds (for example jemalloc) with `dev-exclude-features` in `.lust.toml`. See [docs/dev-features.md](docs/dev-features.md).

Known limit: one file builds as `rustc --edition 2024 -C panic=abort -C overflow-checks=on` would, but plain `rustc` unwinds by default. So a program that catches a panic or joins a panicking thread can print other output than plain `rustc`. Pass `-C panic=unwind` for those. A Cargo target uses Cargo's dev profile.

`--json` prints one diagnostic per line, each with `code`, `message`, `span`, `fix`, and `edits`. The `fix` text tells the user what to write instead. This format exists for coding agents.

This is a complete lust program. It is also a complete Rust program:

```rust
use std::collections::HashMap;

fn main() {
    let words = ["a", "b", "a"];
    let mut counts: HashMap<&str, usize> = HashMap::new();
    for w in words {
        *counts.entry(w).or_default() += 1;
    }
    let total: usize = counts.values().map(|n| n * 2).sum();
    println!("{total} {:?}", counts.get("a"));
}
```

## Supported subset

`lust capabilities` prints the long lists: every std method lust knows, and the messages of its rejects. Each of its item, type, attribute, syntax, and reject lines has a probe in [tests/capabilities](tests/capabilities) that the gate runs (`scripts/test-capabilities.py`), so a stale line fails the gate. The lists below come from probes run against rustc on 2026-10-17.

Supported today:

- Crates: Cargo workspaces, modules and files, `pub` and `use` with globs and re-exports, `cfg`, features, build scripts of path packages.
- Items: `fn`, `struct`, `enum`, `const`, `static`, type aliases, traits with associated types and consts, generic and trait `impl` blocks, blanket impls, const generics, `macro_rules!`.
- Types: all integers (also 128-bit), floats, `bool`, `char`, tuples, arrays, slices, `String`, `&str`, references with lifetimes (also in structs), `Box`, `Rc`, `Arc`, `RefCell`, `Cell`, `Mutex`, `RwLock`, atomics, `dyn Trait` for crate traits and the `Fn` family, `impl Trait` as a whole return type.
- Closures, iterator chains, `?` on `Option` and `Result`, `let`-else, `if let` chains, labeled blocks.
- Derives: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Default`.
- Std: a std written in lust source (`library/std`, `library/core`, `library/alloc`) plus a C runtime. `HashMap`, `BTreeMap`, `VecDeque`, formatting with specs, `std::fs`, `std::io`, `std::env`, `std::process`, threads, `thread::scope`, `mpsc`, panics with unwinding and `catch_unwind`.
- Dependencies: 18 adapter crates in `library/deps` stand in for crates.io packages (`indexmap`, `smallvec`, `memchr`, `rustc-hash`, `num-bigint`, `bumpalo`, `flate2`, `jiff`, and others). Each must give the same output as the real crate.
- Borrow checking: moves, initialization, NLL-style loans, two-phase borrows, and a restricted region model for lifetimes.

Not supported yet. Each gives an error code:

- `impl Trait` inside another type, such as `Vec<impl Fn()>` (`L0602`).
- `dyn` with std traits other than the `Fn` family, `Any`, `Error`, `Debug`, and `Display`, such as `dyn Iterator` (`L0702`).
- `async` (`L0405`) and `unsafe` code (`L0404`). Adapters and shims give lust the few unsafe-backed APIs it needs.
- Unions (`L0602`), raw references `&raw` (`L0820`), `extern` blocks and fns (`L0810`).
- Dependencies with no adapter (`L0508`).
- A std item lust does not have yet (`L0505`).

Rejected on purpose, by design ([docs/PLAN.md](docs/PLAN.md), "What we will not do"):

- Proc macros, and derives other than the built-in ones (`L0403`).
- Generic associated types (`L0621`).

`lust explain <code>` says what to change. Every code has a page in [docs/errors](docs/errors).

## Tests

```sh
scripts/difftest.sh             # compare with rustc
SANITIZE=1 scripts/difftest.sh  # also run the generated C under ASan and UBSan
PANIC=unwind scripts/difftest.sh  # panic=unwind mode, plus tests/unwind
```

- `tests/pass` (2,189 programs): lust and `rustc` must give the same stdout, stderr, and exit status.
- `tests/fail` (3,124 programs): `rustc` and lust must both reject the program, and lust must give the expected error code.
- `tests/reject` (156 programs): valid Rust that lust rejects on purpose.
- Other suites: `tests/daemon` (daemon scenarios), `tests/crates` and `tests/cargo-proj` (Cargo crates), `tests/unwind`, `tests/traits`, `tests/adapters`, `tests/macros`, `tests/kernels`. Their runners are in `scripts/`.

Every change lands through a gate that runs these in lanes on several sandboxes: `cargo test`, difftest in abort and unwind mode, two sanitizer shards, the parser fuzzer, the random-edit fuzzer (`scripts/fuzz/`) on several seeds and crate shapes, daemon scenarios and soak runs, the agent-kit tests, a check of ts-rust's libs and its `tsgo` parity subset, and a perf check.

Two oracles keep the fuzzers honest:

- **The rustc sample.** Each fuzz lane keeps a random sample of the programs lust accepted and builds each one with `rustc` (`scripts/rustc_sample.py`). Any rustc rejection fails the gate. One lane also runs a sample with `rustc` and compares the output with the warm and cold lust runs.
- **The daemon oracle.** With `LUST_CHECK_ITEMPATCH=1`, every warm request is compiled again in a fresh session and must give the same answer bytes, the same errors, and the same program digest (`src/driver/item_oracle.rs`).

The ts-rust census (`scripts/tsrust-full.sh`) checks and builds every target of the pinned fork, runs each bin on every fixture project next to the Cargo-built bin, and runs each lib's unit tests built by lust and by Cargo.

The corpus checks that the two compilers agree on these programs. It does not prove that lust matches `rustc` in general.

## Code map

| Path | Role |
|---|---|
| `src/client.rs`, `src/protocol.rs` | The thin `lust` client, command-line flags, and the daemon wire format. |
| `src/main.rs`, `src/daemon.rs` | `lust-core`: cold compiles and the daemon. |
| `src/driver/` | The compile pipeline and sessions: Cargo graph, build scripts, disk cache, body patch, signature delta, read sets, and the patch oracle. |
| `src/lexer.rs`, `src/scan.rs`, `src/parser/`, `src/ast.rs` | Syntax in flat arenas, plus the token scan that finds what changed. |
| `src/expand/`, `src/resolve/` | `macro_rules!` and builtin macros, `cfg`, the module tree, and name resolution. |
| `src/check/`, `src/ty/`, `src/traits/` | Item collection, type inference, method resolution, trait selection, and match exhaustiveness. |
| `src/lower/`, `src/ir.rs`, `src/borrowck/` | Lowering to a MIR-like CFG, then init, move, loan, and region checks. |
| `src/mono/`, `src/cgen/`, `src/cgen.rs`, `src/tcc.rs` | Monomorphization, the C backend, and `tcc` integration. |
| `src/runtime/` | The C runtime: containers, formatting, panics, threads, and system calls. |
| `src/capabilities.rs`, `src/explain.rs`, `docs/errors/` | `lust capabilities`, `lust explain`, and one page per error code. |
| `library/` | Std in lust source (`std`, `core`, `alloc`) and the adapter crates (`deps`). |
| `shims/` | `liblust_shim.so`, a rustc-built library with a C ABI for system services that ts-rust gets from crates (allocator, file descriptors, processes). |
| `scripts/`, `bench/`, `tests/` | Test runners, fuzzers, the ts-rust census and benches, and the test corpus. |
