# Dev feature selection

Lust dev builds can use a different Cargo feature set than the shipped
Cargo release build. The main use is a feature lust does not need in the
dev loop, such as a native allocator. A build without the feature is
still valid Rust when the crate keeps a `#[cfg(not(feature = ...))]`
fallback, so rule zero holds. Only the dev build changes: Cargo release
builds never read this config.

## Config

Put one of these in the crate `Cargo.toml`:

```toml
[package.metadata.lust]
# Remove names from the package `default` list for lust dev builds.
dev-exclude-features = ["jemalloc"]
```

```toml
[package.metadata.lust]
# Or give the exact dev list. This implies no default features.
dev-features = ["fast"]
```

Use only one key. If both are present, `dev-features` wins.

A workspace can set the config for its members in the workspace root:

```toml
[workspace.metadata.lust]
dev-exclude-features = ["jemalloc"]
```

A `.lust.toml` file with top-level keys also works. Lust reads the
nearest `.lust.toml` at or above the crate directory:

```toml
dev-exclude-features = ["jemalloc"]
```

Lookup order, first config found wins:

1. `[package.metadata.lust]` in the crate manifest.
2. `[workspace.metadata.lust]` in an ancestor manifest.
3. `.lust.toml` at or above the crate directory.

## How a plain dev command uses it

No flags are needed:

```sh
lust check src/lib.rs --manifest-path Cargo.toml --lib
lust build src/main.rs --manifest-path Cargo.toml
lust check crates/ts_goport/src/program.rs
```

When the command line names no feature selection, lust reads the
config, computes the effective list (`default` minus the excluded
names, or the exact `dev-features` list), and stores that list in the
session key as `--features <list>` with default features off. The
daemon session key, the graph key, and the disk cache key all carry the
effective list, so an edit to the config or to `default` starts a fresh
session.

Command line flags always win: any of `--features`,
`--no-default-features`, or `--all-features` on the command disables
the config for that call. To check the release feature set with lust,
pass the flags by hand, for example `--features jemalloc`.

`dev-exclude-features` removes names from the top `default` list only.
If a kept feature enables an excluded one by transitivity, Cargo still
enables it. Fix the config or the feature table in that case.

## Example: ts-rust `jemalloc`

`crates/ts_goport` is the only ts-rust crate with a `jemalloc` feature:

- `crates/ts_goport/Cargo.toml`: `default = ["jemalloc"]`, and
  `jemalloc = ["dep:tikv-jemallocator", "dep:tikv-jemalloc-ctl"]`
  (target-gated to non-Windows, non-wasm). No other crate declares it.
  `crates/ts_wasm` already depends on `ts_goport` with
  `default-features = false`.
- The bin targets (`src/bin/tsgo.rs`, `goport.rs`, `goport_build.rs`,
  `goport_emit.rs`, `goport_typesyms.rs`) install
  `tikv_jemallocator::Jemalloc` as `#[global_allocator]` only under
  `#[cfg(all(feature = "jemalloc", not(windows)))]`.
- `src/program.rs` reads and writes `thread.arena` through
  `tikv_jemalloc_ctl` only under the same cfg, with a plain fallback.
- `src/jemalloc_layout.rs` is mounted only under
  `#[cfg(all(feature = "jemalloc", target_os = "linux"))]`.

Decision (Theo): lust dev builds of ts-rust run with `jemalloc` off.
Release builds by Cargo keep it. Add `.lust.toml` at the ts-rust
workspace root, or the `[workspace.metadata.lust]` table in the root
`Cargo.toml`:

```toml
dev-exclude-features = ["jemalloc"]
```

Effect: lust dev builds use the system allocator fallback. Allocation
speed and the parse thread counts chosen under
`cfg!(feature = "jemalloc")` in `program.rs` differ in dev builds. That
is accepted. The shipped binary is unchanged.

## Example: ts-rust `backtrace`

`crates/ts_goport` feature `backtrace` (default off) gates every
`std::backtrace::Backtrace` call. All 15 sites (lib panic logs and panic
replies, and the `GOPORT_TRACE` output of the bins' panic hooks) get their
text from `src/backtrace.rs` (`capture`, `force_capture`). Off, each gives
the fixed text "backtrace not captured (build with --features backtrace)":
a backtrace's text depends on the compiler's symbols and cannot match
Cargo's byte for byte. The fork's `.lust.toml` excludes it too, and
`build-release.sh` turns it on for the default-features release build.
`scripts/tsrust_parity.py` removes `GOPORT_TRACE` from its runs.

## Registry packages from source

A registry package with no adapter or shim rejects with `L0508`. When
the package is plain Rust inside lust's subset (for example a sister
project published on crates.io), the project config can name it, and
lust then compiles its downloaded source (`~/.cargo/registry/src/..`)
as it compiles a path package:

```toml
[package.metadata.lust]
source-deps = ["fig", "fig-core", "fig-kit@7.0.0"]
```

An entry is a package name, which matches every version the lockfile
resolves, or `name@version`, which matches that version only. A listed
package is a lust source crate (ARCH 1.1), so the usual rules apply:
edition 2024, no `unsafe`, no proc macros, and its own dependencies
classify one by one (list them too, or they reject with `L0508`). A
listed package wins over an adapter or shim of the same name. Its build
script, if any, does not run.

The key is read in the same places as the feature keys
(`[package.metadata.lust]`, `[workspace.metadata.lust]`, `.lust.toml`),
first found, but on its own: a manifest's `dev-features` does not hide
a `.lust.toml` above it that lists `source-deps`, and feature flags on
the command line do not turn it off. The list is part of the session
key, so editing it starts a fresh session. Release builds by Cargo never
read it: they build every package with rustc, as always.

## Tools

- `lust-port scan` reads the same config and evaluates
  `cfg(feature = ...)` with the effective dev features of each package
  (config, else the package defaults). Flags `--cargo-features <a,b>`
  and `--cargo-exclude-features <a,b>` override the config for one
  scan. The report JSON lists the effective features per package.
- `scripts/port-scan-sync.py --coverage` passes
  `LUST_DEV_EXCLUDE_FEATURES` (comma list) or `LUST_DEV_FEATURES`
  through to the scanner when they are set, so a scan of a read-only
  tree can still use the dev selection.
- `bench/slices/prune.py` reads the config from the ts-rust tree (or
  `--dev-features` / `--dev-exclude-features` / the same env vars),
  passes the effective list to lust and to its rustc oracle, and
  records `dev_features` in `prune.json`. `scripts/speed_slice.py`
  replays that list for both lust and Cargo on the slice crate.
