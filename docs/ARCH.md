# lust compiler architecture: milestones 4 to 9

Status: decision document, revision 2. Revision 1 got two
adversarial reviews that both said "request changes" (sol and
Opus). This revision fixes those findings. Section 11 lists
each finding and what changed. It is not implemented.
Scope: milestones 4 to 9 in `docs/PLAN.md`. The north star is ts-rust.
Rule zero does not change. Every program lust accepts is valid Rust
(rustc 1.99, edition 2024) with the same output. Release builds go
through Cargo. Lust owns only the dev loop.

This document makes one choice per open question. Each choice is
concrete enough to implement without a new design round. Where a
choice can fail, the document names a spike, a gate, and a fallback.
Section 9 splits the work so 4 to 8 agents can build in parallel.

Readers: the orchestrator and the agents who get work packages.
Conventions: `file:line` means a line in the lust worktree, or in
ts-rust at `/home/theo/.t3/projects/ts-rust` when the path says so.
"Must" is a requirement. "Reject" means a stable `L####` error, not a
panic in the compiler.

Evidence base:

- Current compiler: 10,286 lines in `src/*.rs`, 402 lines in
  `src/runtime.c`.
- `/tmp/lust-ts/inventory/INVENTORY.md`: 571k handwritten prod lines,
  19,492 prod functions, feature counts from a real parser.
- `/tmp/lust-ts/design/DESIGN-TS.md`: the port design. Section 2 is
  the restricted lifetime model. Section 3 is the trait solver shape.
- `/tmp/lust-verify/g/VERIFY.md`: the generics verdict. Lock
  monomorphization plus iterator fusion, with layout-erased std
  container cores. No dictionary passing.
- `docs/PLAN.md` and `DESIGN.md`: targets, gates, and the exact
  rule-zero contract.

## 0. Where we start

The prototype pipeline is in `src/main.rs:5-21`: flat modules
`ast, borrowck, cgen, check, collect, daemon, diag, driver, intern,
ir, lexer, lower, parser, protocol, scan, tcc, types`. One file is
one crate. The important limits, by file:

| Area today | Where | Limit to remove |
|---|---|---|
| Closed types | `src/types.rs:82-104` `TyKind` | No generic args, tuples, arrays, slices, fn ptrs, `dyn`, closures, floats, u128. `Vec(Ty)` and `Option(Ty)` are built in. |
| Std as an enum | `src/check.rs:17-79` `Builtin`, about 55 cases | Every std method is hand-written in `check.rs`, `ir.rs`, `cgen.rs`, and `runtime.c`. It cannot scale to the std ts-rust uses. |
| One flat namespace | `src/collect.rs:59-71` `Program` | `type_names: HashMap<Sym, AdtId>`, `methods: HashMap<(AdtId, Sym), FnId>`. No modules, no crates, no traits, no generics. Module paths in types are rejected at `src/collect.rs:124-131` unless they start with `std`. |
| Items | `src/ast.rs:55-61` `ItemKind` | Only `Fn, Struct, Enum, Impl, Use`. `Use` carries no data. No `mod`, `trait`, `type`, `const`, `static`, `macro_rules`. |
| Types in syntax | `src/ast.rs:138-143` `TyExpr` | Only `Path`, `Ref`, `Unit`. `PathSeg.generics` exists at `src/ast.rs:133-136` but collect rejects generics for all types except `Vec` and `Option`. |
| Lifetimes rejected | `src/parser.rs:65-72`, `src/collect.rs` ref-field check | Any `'a` token is error `L0203`. DESIGN-TS section 2 requires the opposite. |
| Trait queries are functions | `src/collect.rs:480-539` | `is_copy`, `has_clone`, `has_eq`, `has_debug`, `has_display`, `needs_drop` are fixed rules plus derives. There is no impl index and no obligation queue. |
| Inference | `src/check.rs:1-2` | Local unification plus integer vars. Output is side tables in `Checked` at `src/check.rs:155-170`. Keep this shape. Extend it, do not replace it. |
| IR | `src/ir.rs:76-99` `Rvalue` | `Call(FnId)`, `Builtin(Builtin)`, `Aggregate`, `Opt`, `VecLit`. No method-call target for traits, no closure, no vtable, no unwind edge. |
| Borrow checker | `src/borrowck.rs:1-103` | NLL loans, liveness, two-phase support. One synthetic loan for ref params. No regions, no field-carried borrows through ADTs. Keep the loan engine. Add regions above it. |
| Incremental | `src/driver.rs:1-14`, `src/scan.rs:1-45` | Three cases only. A type, impl, or `use` edit is a full rebuild. Slots are keyed by `(Sym, Sym)` at `src/driver.rs:43`. |
| Daemon | `src/daemon.rs:16-25`, `src/protocol.rs:19-47` | One `Session` per file. A request names one file. No crate, no features, no target. |
| Spans | `src/diag.rs:5-19` | `Span { start, end }` in one file. No file id, no expansion site. Macros and multi-file crates both break this. |
| Codegen | `src/cgen.rs:604-612`, `src/runtime.c:19-22` | Every call goes through `lust_fns[slot]`. `lust_Vec` is already erased: `lust_vec_push_slot(v, sizeof(T))` at `src/runtime.c:213-216`. This is the seed of the std design in section 3. |
| Panics | `src/runtime.c:111-127` | `lust_panic` prints and aborts. No payload, no recovery, no cleanup on unwind. |

Design rules for all sections:

1. Prefer the simplest design that ports ts-rust. Ts-rust is
   Go-shaped: 591 generic functions (3%), 6 blanket impls, no GATs,
   no proc macros, no unions (INVENTORY summary 1). Do not build
   general Rust where a stated subset covers the evidence.
2. Reject outside the subset with a clear error. Never guess. A
   wrong accept breaks rule zero. A reject only costs a codemod.
3. Keep flat arenas and indices. No pointer trees in hot data.
4. Check cost must grow with the edit. Every new global table needs
   an index and an invalidation rule in section 8.
5. No trait search with backtracking. No global type inference.
   These are perf contracts, not preferences.

## 1. Crate graph and modules

### 1.1 Packages, crates, targets

Lust does not write a Cargo resolver. Cargo owns version solving.
The graph key is the full resolver input, not only file hashes:
the hash of all `Cargo.toml` files plus `Cargo.lock`, the
requested packages and targets, the requested features and the
default-feature policy, the target triple, and the Cargo config
files that apply (`.cargo/config.toml` chain). The driver runs
`cargo metadata --format-version 1` with those inputs once per
graph key, and keeps its output in the crate's disk cache dir
(`cargo-graph-<key>.txt`, with the watch stamp of the path packages),
so a cold process reuses it until the key or the stamp moves
(`src/resolve/cargo.rs` `disk_graph`). `cargo metadata` alone unifies features over the whole
workspace, which can differ from a `-p ts_goport --bin tsgo`
build. So the feature set of each selected unit comes from one
cached `cargo check --message-format=json` dry run for the same
request. The dry run has lust-core as its RUSTC_WRAPPER: build
scripts, proc macros, and their dependencies compile for real, and
every check unit gets an empty dep-info file and no `.rmeta`, so a
later real check rebuilds it (`src/resolve/probe.rs`). Cargo still
picks the units and their features, so the messages are the same as
a full check. Lust reads: packages (name, version, manifest path,
features, dependencies with kind, rename, and target cfg),
targets (kind, name, `src_path`, edition, `crate_types`), and
per-unit features. Dependency kinds and target cfgs filter edges:
a dev-dependency or a `cfg(windows)` dependency of a Linux build
is in the graph data but is not a selected unit. The profile
values that change output (panic strategy, overflow checks,
debug assertions) enter every session and cache key. A Cargo
crate target reads them as Cargo does for its dev profile
(`protocol::dev_profile`: `CARGO_PROFILE_DEV_*`, then the
`.cargo/config.toml` chain, then the workspace root manifest);
a single file uses rustc's defaults (panic=unwind, as plain `rustc file.rs`).

Terms:

- A *package* is a Cargo package.
- A *crate* is one target of one package: a lib, a bin, a test, an
  example, or a bench. Each crate has one root file. A crate is the
  unit of name resolution, type checking roots, and daemon
  sessions.
- `build.rs` is not compiled by lust in milestones 4 to 7. The
  driver runs it through Cargo during `lust port prepare`, or
  reads a recorded build-script output. Recorded output is valid
  only while its recorded inputs hold: the build script source,
  every `rerun-if-changed` file, and every
  `rerun-if-env-changed` value. The driver re-checks those
  inputs per session and re-runs the script through Cargo when
  one changes. Its `OUT_DIR`, `cargo::rustc-cfg`, env outputs,
  and the contents of `OUT_DIR` files that source code includes
  enter cache keys by content hash. Ordinary source and const
  initializers see the same Cargo env values (`CARGO_PKG_*`,
  `OUT_DIR`) as the rustc build. Ts-rust needs this:
  `goport_util/build.rs` returns early on native builds but
  packs wasm data (DESIGN-TS section 4).
- Edition: lust source crates must be edition 2024. Apply the
  check only to selected units, after dependency
  classification (1.1 table below) and target filtering. An
  unselected workspace tool or the upstream package behind an
  adapter keeps its own edition and does not fail the session.
- Lints: `cargo metadata` does not report them. The driver
  reads `[lints]` and `[workspace.lints]` from the manifests of
  selected units. It enforces `unsafe_code` at forbid or deny
  level (ts-rust sets `unsafe_code = "forbid"` in
  `/home/theo/.t3/projects/ts-rust/Cargo.toml:18-19`). Any
  other rust lint at deny or forbid level rejects the session
  with `L0531` naming the lint, because rustc would reject
  code that triggers it and lust does not check it. Warn and
  allow levels need no action. Clippy lints do not run in a
  rustc build, so they are out of scope.
- Test crates: `lust test` builds the lib or bin crate again with
  `cfg(test)` on and `#[test]` fns as extra roots. Integration
  tests in `tests/` are normal bin-like crates that depend on the
  lib crate. `cfg(test)` is the test crate's alone: its
  dependencies (also the package's own lib, under an integration
  test or a dev-dependency) build as in any other session. The
  harness shims go into in-memory copies of the crate's files
  (`driver::set_source_overlay`, src/testrun/krate.rs). The test
  binary runs its tests as libtest does: one process, the main
  thread starting them sorted by name on threads named by the
  test (`--test-threads`), each under `catch_unwind`, so tests
  share process state as under `cargo test`. Its results go to a
  file line by line, so the runner can rerun the tests a dead or
  hung process did not finish. Ts-rust's baseline runner is such a target with
  `test = false` in `crates/ts_goport/Cargo.toml`, so target
  handling must not assume `cargo test` semantics.

Ts-rust workspace shape, from `/home/theo/.t3/projects/ts-rust/Cargo.toml:1-9`:
members are `ts_goport`, `parts/goport_lsproto`,
`parts/goport_util`, `ts_wasm`, and two codegen tools. The first
port scope in PLAN.md is the core CLI: package `ts_goport`, bin
`tsgo`, plus its two path dependencies. All other workspace
members stay visible in the graph but unchecked until selected.

Dependency crates split into three classes. The class is a
property of the resolved package id, version, and feature set.
It is never chosen by a source spelling.

| Class | Meaning | Ts-rust examples |
|---|---|---|
| Lust source | Lust compiles the crate from Rust source like user code: a path package, or a registry package (by name, or name and version) that the project's `source-deps` config lists (docs/dev-features.md). | `goport_util`, `goport_lsproto` |
| Adapter | Lust compiles a lust-owned crate with the same public API in place of the dependency. Section 3.6. | `indexmap`, `smallvec`, `rustc-hash` aliases over std maps |
| Shim | A rustc-built static or shared library exports C functions. Lust links it. Section 3.7. | `rustix`, `nix`, `flate2`, `jiff` |

Release always uses the original crates through Cargo. Adapters
and shims exist only in dev builds.

### 1.2 Module tree

A crate starts at its root file. The search directory for
`mod foo;` follows Rust: if the current file is a crate root,
`mod.rs`, `lib.rs`, or `main.rs`, submodules live in the same
directory. In any other file `a.rs`, submodules live in the
directory `a/` next to it. Example: `mod go_frontend;` at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/program.rs:28`
loads `program/go_frontend.rs`, not `go_frontend.rs`. An inline
module keeps the search directory of the file that holds it,
plus one path segment per inline module name. In the search
directory, `mod foo;` loads `foo.rs` or `foo/mod.rs`. If both
exist, that is error `L0502` (Rust reports ambiguity; there is
no preference order). If neither exists, `L0503`.
`#[path = "..."]` overrides the file. Its path is relative to
the directory of the file that holds the `mod` item. For an
inline module it is relative to that directory plus the inline
module path segments, as in Rust. Ts-rust has 6 `#[path]`
modules in 3 files (INVENTORY items table), so support it in
milestone 4, not later. Inline `mod foo { ... }` needs no file.
A file belongs to exactly one (crate, module) pair, with one
exception below.

Shared files across crates exist in ts-rust. The two part crates
keep their files under `ts_goport/src/` and enter through
`src/goport_util_root.rs` and `src/goport_lsproto_root.rs`
(`crates/ts_goport/src/lib.rs:1-7` and
`crates/ts_goport/Cargo.toml` comments). The same file can thus be
a module in two crates with different module paths and different
`crate::` meaning. Rule: file text and tokens are cached per
file. AST, defs, and checks are per (crate, module). Never share
a `DefId` across crates for the same file.

Module discovery is a scan, not a full parse. Extend `src/scan.rs`:
at brace depth 0, record `mod` declarations (name, visibility,
`#[path]`, `#[cfg]`), `use` headers, `macro_rules!` names, and
item header hashes. Bodies are hashed, as today at
`src/scan.rs:10-16`. The driver walks `mod` edges from the root
to build the file set. A `mod` edit can add or remove a file;
section 8 makes that a module-tree invalidation, not a full
rebuild.

Each file gets a `FileId` (u32) per workspace session, assigned
in sorted canonical path order at crate load, then append-only.
`FileId` is session-local. It must never enter a disk cache key.
Disk keys use the canonical path string hash instead.

### 1.3 Namespaces and resolution

Rust has three item namespaces: type, value, and macro. Modules
live in the type namespace. Lifetimes have their own per-item
scope (section 5) and do not enter module resolution. Lust keeps
exactly this split. One name can hold a struct (type) and a fn
(value) at once. A tuple struct fills both: the type and its
constructor in value space. A unit struct does the same.

Resolution does not run after expansion as a separate phase.
Cfg stripping, module loading, macro expansion, and import
resolution form one outline worklist per crate (section 6.1).
The worklist produces, per crate:

1. The module tree. One `ModuleId` per module. Record parent,
   file, visibility, and the inline/file kind.
2. Defined names per module: items, impl blocks (no name),
   trait items, enum variants (namespaced by the enum, plus
   prelude-style value access through the enum path), fields
   (not module names), and macro defs visible by textual scope.
3. Resolved imports, by the fixpoint below.
4. Then every path in signatures, then in bodies, resolves to a
   `Res`: a `DefId`, a local, a primitive, a self type, or an
   error. Bodies resolve in parallel after signatures, as
   collect and check split today (`src/collect.rs:1-2`).

Import fixpoint. Imports form a graph. Globs and re-exports make
it cyclic (`prelude` modules re-export whole subtrees). An
explicit import can depend on a glob binding, so one worklist
handles both. There is no "explicit first, globs later" split:

- State per module: for each namespace, a map `name -> Binding`.
  A binding is `Def(DefId, Vis)` or `Ambiguous`, plus its
  source: local def, explicit import, or glob. The source sets
  priority: local def and explicit import beat glob at all
  times, even when the glob binding arrives first.
- Work items are unresolved explicit imports and unpropagated
  globs. Start with all local defs inserted and all imports as
  work items. Repeat until the worklist is empty: resolve one
  explicit import if its target path resolves now (groups
  `use a::{b, c as d}`, `self`, `super` included); propagate
  one glob by copying each public-enough binding of its target
  module that loses to no local or explicit binding. Each new
  binding can unblock other work items, so loop over both
  kinds. Example that must work:
  `pub use crate::checker::TypeMapperKind` at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/prelude.rs:29`,
  where `checker/mod.rs:133` has `pub use mapper::*` and the
  enum is defined at `checker/mapper.rs:14`.
- If two globs bring the same name with different defs, store
  `Ambiguous`. It is an error only if code uses the name (Rust
  rule; ts-rust's `prelude.rs` relies on explicit
  disambiguation, see section 1.4).
- An explicit import that still does not resolve when the
  worklist empties is an error, not a silent miss.
- `pub use` re-exports: the binding in the re-exporting module
  carries the re-export's own visibility. The target `DefId`
  does not change. There is no alias def. The visibility of the
  binding is separate from the privacy check on the path used
  to find it: `mod hidden { pub struct S; } pub use hidden::S;`
  is valid, and `S` is public through the alias. Do not take a
  minimum over the lookup chain. The chain rule applies only
  when a use names the original path segment by segment.
- A failed import records a failed lookup (section 8) keyed by
  `(module, namespace, name)`. Adding a def or an import later
  must re-run the bodies that recorded it.

Determinism: process work items in `ModuleId` order and names in
`Sym` order. The result must not depend on hash map order. Each
binding changes state at most twice (absent, glob, explicit), so
the worklist ends. Keep a round cap of `modules + 2` full sweeps
as a bug guard: if it hits, emit `L0501 import cycle does not
settle` and stop the crate. Rust accepts all such graphs; log
any hit as a bug.

Scope priority for the first segment of a path, highest first:
lexical scopes, glob imports, the `#[macro_use]` macro
prelude (macro namespace), the extern prelude, the std prelude,
then builtin type names. Lexical scope means locals, then
block items up to the enclosing fn, then the items and
explicit imports of the current module only. It never searches
outer modules: an unqualified name that only an enclosing
module defines is not found (rustc E0425). In a `use` path,
the first segment must be `crate`, `self`, `super`, an extern
prelude name, or an item or import of the current module
(the 2018 uniform path rule, which edition 2024 keeps; a name
only an enclosing module has is rustc E0432). A local module can
shadow an extern name, but only in its own module: ts-rust has a
local module named `core` at `goport_util_root.rs:26`, and its
other modules still reach the `core` crate as `core::`. Std
source spliced at the crate root reads `std`, `core`, and
`alloc` as if written with `::`. A generated item that would change a
macro resolution that already ran is an error, as in Rust
(E0659, "time travel"): the worklist records which bindings each
expansion used, and a later binding that wins over a used one
fails with `L0504`.

Path forms to support in milestone 4: `crate::`, `self::`,
`super::` (repeated), `::dep::` absolute extern, bare extern
crate names in 2024 style, `Self`, qualified paths
`<T as Trait>::Item` (needed once traits land; parse in 4,
resolve fully in 5), and paths in type, value, pattern, and
macro positions. `use` inside fn bodies and blocks: support.
Ts-rust has function-local imports. They resolve against the
module tables plus the local scope chain.

Preludes:

- *Std prelude*: the names in `library/std/src/prelude.rs`
  (section 3). It is its own lowest scope layer, below globs.
  It is not a glob import: it applies only to the first segment
  of a relative path, it never becomes a module binding, a glob
  never re-exports it (`pub use m::*` does not carry it), and
  it is never ambiguous with a glob. A local def, an explicit
  import, or a glob with the same name wins. Ts-rust depends on
  this: it defines its own `Box` at
  `project/dirty/box_.rs:9` and its own `Result` at
  `contentmapper/host.rs:316`, both glob re-exported.
  `#[no_implicit_prelude]` on a module or crate turns it off.
- *Extern prelude*: each direct dependency's lib crate root is a
  name in the type namespace of every module's first path
  segment, with rename from `Cargo.toml` (`name = "x"` in the
  dependency, and `-` to `_`). Plus `std`, `core`, `alloc`.
  Adapter and shim crates appear here with their real crate
  name, so user source does not change.
- There is no language-level crate prelude. `crate::prelude::*`
  is a normal glob import. It must work well because ts-rust
  uses it in 698 files (INVENTORY: prelude globs 700 in 698
  files).

### 1.4 Why globs must be exact: ts-rust evidence

`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/prelude.rs:1-30`
glob re-exports `ast::*`, `binder::*`, `checker::*`, `core::*`,
and more, then pins collisions by explicit re-export:
`pub use crate::ast::NodeFactory` at line 5 with the comment
that `printer::NodeFactory` must not shadow it, and lines 27-30
pin `factory`, `TypeMapperKind`, `EmitHost`, and others. So:
explicit beats glob, glob-vs-glob ambiguity errors only on use,
and a `pub use` inside a globbed module propagates. Counts from
INVENTORY: glob imports `crate::` 822, prelude 700, `super::`
230; `pub use` 753 in 73 files; use groups 813, renames 45.
Every file uses globs or tuples. This is not an edge case. It
is milestone 4's core.

Macro namespace resolution has two layers (section 6): textual
`#[macro_use]` order inside a crate, and path-based
`crate::mac!` / `dep::mac!` for `#[macro_export]` macros.
Ts-rust needs both: `go_flags!` is `#[macro_export]` in
`goport_util` and re-imported through an inline module at
`crates/ts_goport/src/lib.rs:44-47`.

### 1.5 Visibility

Forms: private (default), `pub`, `pub(crate)`, `pub(super)`,
`pub(in path)`. Private means the defining module and its
descendants. Fields, variants, trait items, and impl methods
follow Rust rules: a trait item is as visible as its trait; an
inherent impl item carries its own visibility; enum variants
take the enum's visibility. A re-export binding carries the
visibility written on the `use` (section 1.3): a `pub use` of a
`pub` item in a private module makes a public binding. Check
visibility at path resolution time
for each segment, and again for field and method access in
check. Errors: one code family `L051x`, with a fix hint that
names the smallest widening (`pub(crate)`) that would work.
Do not auto-apply the fix. PLAN.md milestone 3 limits `--fix`
to narrow safe edits; visibility widening changes API surface.

Dead-code and unused-import warnings: out of scope for check
correctness. Unused names must not change ambiguity behavior.

### 1.6 cfg

Evaluate `#[cfg(...)]` and `#[cfg_attr(...)]` in the outline
worklist (section 6.1): strip cfg on each item and attribute
before expanding or resolving it, per item, per field, per
variant, per match arm where Rust allows it, and on `mod`
declarations before file loading. A disabled `compile_error!`
or `include!` must not run. `cfg!` expands to a `bool` literal
in the expander.

The cfg environment is a fixed set per crate session. Known
names are the full rustc well-known list: `target_arch`,
`target_os`, `target_vendor`, `target_family`, `target_env`,
`target_abi`, `target_endian`, `target_pointer_width`,
`target_has_atomic` and its width forms, `target_feature`,
`target_thread_local`, `unix`, `windows`, `panic`,
`overflow_checks`, `debug_assertions` (dev on), `test` (only
in test crates), `docsrs`, `feature = "..."` from the per-unit
feature set (section 1.1), and build-script cfgs recorded by
`lust port prepare`. `target_vendor` is required: ts-rust uses
it 8 times in `fswatch/`. The target
values come from a small built-in table for tier 1 targets
(`x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`) plus
`wasm32-wasip1` for classification only. Do not shell out to
rustc per request.

Rules for unknown cfgs: an unknown *name* (say `cfg(frobnicate)`)
is error `L0520` in lust, listing the known names. Rust treats
it as false with a warning (or an error under `check-cfg`).
Rejecting is safer: silently dropping a module changes the
program. The fix hint says to declare it via build script
output or remove it. One
lust-only cfg name exists: `lust_dev`. It is true in lust dev
builds and false in Cargo release. Only std and adapter crates
may use it: lust cannot prove "equal behavior" in user code, so
user use is `L0520`. The shipped manifests declare it in
`check-cfg`, so Cargo builds stay free of warnings. Never fake
a target cfg (say, pretend wasm) to delete threads.

Stripped items leave no def. Diagnostics in stripped code do
not fire. The scan stage still hashes stripped text so edits
there invalidate nothing but the file node.

Attributes other than cfg: parse all. Honor: `derive` (with
`default` on one enum variant, 32 uses in ts-rust; without it
`derive(Default)` on enums cannot work), `repr`,
`path`, `macro_use`, `macro_export`, `no_implicit_prelude`,
`inline` (ignored in dev codegen), `cold` (ignored),
`must_use` (ignored in v1, no warning infra), `track_caller`
(real semantics, section 3.5), `allow`/`warn`/`deny` (parsed;
`deny` follows the lint rule in section 1.1),
`non_exhaustive` (real check
across crates), `deprecated` (ignored), `doc` (ignored),
`rustfmt::skip` (ignored, 23 uses),
`test`, `bench`, `ignore` and `should_panic` (test attributes,
honored by `lust test`), `global_allocator` (recorded; dev
link picks the allocator, section 3.7). Tool attributes under
known tool namespaces (`rustfmt`, `clippy`) are ignored.
Unknown attributes: `L0521`
error with the supported list. Ts-rust uses `must_use` 1,215,
`inline` 713, `cold` 93, `track_caller` 16, `allow` 106.

### 1.7 Stable DefIds

Today a fn's stable identity is a slot keyed by `(name, owner)`
at `src/driver.rs:43`, and `FnId` shifts on edits
(`src/driver.rs:40-42`). The disk cache, the daemon overlay
table, the fuzzer, and panic line tables all depend on this
identity. Multi-crate code needs the general form now, before
parallel work starts. This is serial refactor S2 (section 9.2).

Definitions:

```rust
pub struct CrateId(pub u32);      // session-local, dense
pub struct DefPathHash(pub u64);  // stable across sessions
pub struct DefId { pub krate: CrateId, pub hash: DefPathHash }
pub struct LocalDefId(pub u32);   // dense index inside one crate, per session
```

A `DefId` answers "which item is this" across edits. Its
`krate` field is session-local, so a `DefId` as a whole must
never enter a disk key. The disk form is the pair
`(StableCrateHash, DefPathHash)`, where `StableCrateHash` is
the crate disambiguator hash from step 1 below. Only that pair
may enter disk keys, slot keys, or fuzzer transcripts. Never
`LocalDefId`, `FileId`, `Sym`, `Ty`, `ArgsId`, or `CtxtId`:
section 8.4 defines the disk form of each, by translation at
the write boundary. A `LocalDefId` is the fast array index
inside one crate session. The crate session keeps
`FxMap<DefPathHash, LocalDefId>` and `Vec<DefId>` side tables.

`DefPathHash` inputs, hashed with the existing FxHash
(`src/intern.rs:9-41`):

1. Crate disambiguator: hash of the package id string from
   Cargo metadata (name, version, source). For path packages,
   the workspace-relative manifest path replaces the source,
   so two checkouts of one workspace share hashes on one
   machine. Two path deps with the same name and version in
   one workspace are a Cargo error already.
2. The target kind and target name (`lib`, `bin:"tsgo"`, ...).
   The same lib compiled as a test crate gets a distinct
   disambiguator suffix `:test`. Test and non-test defs must
   never collide in the instance cache.
3. The module path: each segment's name string (not `Sym`,
   which is session-local), from the crate root.
4. The item kind tag and item name string.
5. A disambiguator for name-less or same-name items, below.

Name-less and synthetic items:

| Item | Disambiguator |
|---|---|
| Impl block | Hash of the normalized impl header tokens (generics, trait path, self type, where bounds), plus an ordinal among impls in the same module with equal header hash, in file order. Body edits keep the id. A header edit makes a new id. That is correct: the old impl is gone. |
| Method, assoc type/const/fn | Parent impl or trait hash plus item name. |
| Closure | Parent fn hash plus the closure's ordinal in that body, in token order. An inserted closure above shifts later ordinals. Only cache reuse is lost. Correctness never depends on it because instance keys add the body fingerprint. |
| `impl Trait` opaque | Parent fn hash plus return-position ordinal. |
| Derived impl | Adt hash plus the trait name (`derive:Debug`). |
| Static inside `thread_local!`, `const` in a body | Parent hash plus item name plus ordinal among same-name items in the parent. |
| Macro-generated item | The item's own module path and name, as if hand-written. The expansion site does not enter the hash. Two expansions that generate the same item name in one module are a duplicate-def error, as in Rust. |

Collisions: a 64-bit hash collision inside one crate is
detected when two distinct def paths map to one hash; emit an
internal error and stop. Do not add a collision-resolution
scheme. At 786k lines the birthday risk is negligible, and the
check makes it safe.

Slots live in one space per final binary, not per crate:
generated code calls `lust_fns[slot]` from one table, so two
crates must never assign the same slot to different functions.
`slot_of: FxMap<InstanceKeyHash, u32>` is owned by the driver
for the final bin (section 4.2). The
panic line table keys by slot as today. The fuzzer compares
diagnostics by (crate, module path, name), never by `FnId`.

What a `DefId` is not: it carries no generic arguments, no
types, and no span. Renaming an item changes its `DefId`. That
is intended: a rename is a delete plus an insert for caches,
and section 8 handles dependents through signature nodes.

### 1.8 Daemon sessions per crate

Replace per-file sessions (`src/daemon.rs:22-25`) with:

```text
Daemon
  WorkspaceSession per (workspace root, lust version)
    Interner (one, shared by all crates)
    Cargo graph (cached metadata)
    CrateSession per SessionKey
      Front: files, tokens, ASTs, module tree, defs
      Checks: per-DefId generic checked bodies
      Mono: instance table and slots
      Caches: C text, objects, libbase overlays
    File index: canonical path -> set of (CrateId, ModuleId)
```

`SessionKey` = (graph key from section 1.1, crate
disambiguator, per-unit feature set hash, cfg
environment hash, profile including panic and overflow
settings, lust version, adapter/shim versions for its deps).
Two feature selections or two targets in one daemon give two
sessions. A test in section 9 proves it. One shared `Interner` per workspace matters:
`Sym` values must mean the same string in every crate, or
cross-crate signature exchange needs translation tables. The
interner is already sharded and thread-safe
(`src/intern.rs:56-68`).

Request routing: the protocol gains a crate selector. New wire
form (keep tab-separated lines, add fields): manifest path,
package, target, features, then the file the user named. If the
user names a file, the daemon finds its crate through the file
index; if the file is in two crates (shared part files), the
request must name the target or the daemon checks the
"primary" crate (the one whose root owns the file by `mod`
reachability from a lib target first, then bins, in metadata
order) and says which crate it picked in the response. Silent
guessing is not allowed.

Cross-crate flow: a crate session reads dependency crates only
through their *signature surface*: defs, generic signatures,
layouts of `pub` types, impl headers, macro defs, and const
values. Dependency bodies are needed only at monomorphization
for generic fns and `#[inline]`-style cross-crate generics,
which in dev means all generic fns (mono is per final bin).
So each crate keeps checked generic bodies in memory for its
dependents. No rlib or metadata file format in milestones 4
to 9. Cold builds compile crates in dependency order in one
process. The disk cache (section 8) stores per-instance C and
objects, keyed across crates, so a cold daemon restart does
not redo codegen.

Session eviction: keep at most the crates of the last two
workspaces in memory. Ts-rust's full graph at 786k lines will
not fit a naive per-crate clone of today's `Front`. ASTs of
dependency crates can drop after collect if the crate has no
generic fns used downstream; keep defs and signatures. Measure
at milestone 8 and tune. Do not build an eviction policy
before there is a memory number.

## 2. Types and the trait system

### 2.1 Type representation

Replace the closed `TyKind` (`src/types.rs:82-104`) with an
open, interned form. Keep `Ty(pub u32)` and the two-level
global-plus-local interning (`src/types.rs:130-197`). The
global table holds signature types and is frozen after
collect. Body-local overlays hold inference state. One change
is forced: `TyKind` can no longer be `Copy` with inline
payloads only, because generic args are slices. Store arg
lists in an interned slice arena next to the kind arena.

```rust
pub enum TyKind {
    Error, Unit, Bool, Char, Never,
    Int(IntTy),          // add I128, U128
    Float(FloatTy),      // F32, F64
    Str,                 // unsized str
    Ref(Region, Mut, Ty),
    RawPtr(Mut, Ty),     // std and shim code only at first
    Slice(Ty),
    Array(Ty, ConstId),
    Tuple(TysId),        // TysId indexes interned &[Ty]
    Adt(DefId, ArgsId),  // user and std structs/enums/unions(none)
    FnPtr(SigId),        // SigId: interned (inputs, output, safety, abi)
    FnDef(DefId, ArgsId),// fn item used as a value, before coercion
    Closure(DefId, ArgsId),
    Dyn(BoundsId, Region),
    Opaque(DefId, ArgsId),        // impl Trait return
    Param(ParamId),               // index into the current Generics
    Projection(AssocId, ArgsId),  // <Self as Trait>::Assoc, unnormalized
    Infer(InferId),               // body-local only, never in global tys
}
```

Supporting interned data, all in `src/ty/`:

- `GenericArg = Ty(Ty) | Lifetime(Region) | Const(ConstId)`.
  `ArgsId` interns `&[GenericArg]` in declared parameter
  order: lifetimes, types, consts interleaved as written. One
  schema everywhere. A tuple's element list is a different
  type, `TysId` (interned `&[Ty]`), named differently so no
  code confuses the two. Store each slice once; hashing a `Ty`
  stays O(1).
- `Region = Static | Param(u32) | Bound(u32) |
  Placeholder(u32) | Infer(u32) | Erased`. `Bound(i)` is a
  de Bruijn index into the nearest enclosing `Binder`
  (below).
  `Param` indexes the lifetime params of the item whose
  signature the type sits in. `Placeholder(n)` is a fresh
  universal region that exists only during a higher-ranked
  proof (5.5): it is distinct from every other region, it
  never unifies with one, and it must not escape the proof.
  It is not an inference var. `Erased` appears only after
  borrow checking, at mono and codegen. Section 5 owns the
  rules. In milestone 4, all regions are `Erased` except the
  std-internal handling that exists today through
  `ret_borrows_from` (`src/collect.rs:52-53`), which the
  region work replaces in milestone 6.
- `ConstId` interns const generic values and const item
  values: ints, bools, chars, aggregate const values (2.13),
  and const param references. The bounded const evaluator is
  section 2.13. Anything outside it in const position is
  `L0630` reject.
- `Binder<T> { count: u32, value: T }` wraps a type, a
  signature, or a predicate that contains `Bound` regions.
  `for<'a, 'b> X` is `Binder` with count 2. Only rank-1
  binders: a `Binder` inside a `Binder` value is `L0710`.
  Instantiating a binder replaces each `Bound(i)` with a fresh
  region var (at a call site) or with a `Placeholder` region
  (in a proof, section 5.5). The two are never mixed.
- `BoundsId` interns a `dyn` bound list: one principal trait
  ref under its `Binder` (a `dyn for<'a> Fn(&'a T)` principal
  keeps count 1; 2.9), with its associated-type bindings
  under the same binder, the supertrait trait refs in
  declaration order, plus auto traits (`Send`, `Sync`,
  `Unpin`) as bits. Auto traits that a supertrait requires are
  part of the bounds: `dyn AnyValue` is `Send` because
  `AnyValue: Send` (section 2.8).
- `SigId` interns fn pointer signatures as `Binder<FnSig>`:
  `for<'a> fn(&'a T) -> U` is a binder of count 1 over a sig
  whose regions use `Bound(0)`. See 2.9.

`String`, `Vec<T>`, `Option<T>`, `Chars`, `Args` stop being
`TyKind` cases. They become `Adt` defs in the std crates
(section 3). This is the single biggest representation
change. It deletes special paths in `collect.rs`,
`check.rs`, `ir.rs`, and `cgen.rs` and replaces them with
the general Adt path. S3a adds the representation behind
compat helpers. The `Builtin` paths stay until the minimal
generic pipeline passes its gate (section 9.3). Only then
does std delete compat cases, in staged API groups.

Every def that can be generic owns a `Generics`:

```rust
pub struct Generics {
    pub parent: Option<DefId>,       // impl or trait for a method
    pub params: Vec<ParamDef>,       // lifetime, type, or const; name, span
    pub predicates: Vec<Predicate>,  // bounds, in source order
}
pub enum Predicate {
    Trait(Binder<TraitRef>),         // binder count 0 when not higher-ranked
    // The equality stays under the binder of the bound that
    // wrote it: `for<'a> Fn(&'a T) -> &'a U` binds its
    // `Output` inside the `for<'a>`. Moving the equality out
    // of the binder loses the region and is a bug.
    AssocEq(Binder<AssocEqData>),
    Outlives(Region, Region),
    TypeOutlives(Ty, Region),
}
pub struct AssocEqData { pub assoc: DefId, pub trait_args: ArgsId, pub ty: Ty }
// Self is args[0]. `bindings` is an interned list of
// (assoc DefId, GenericArg) pairs: the `Item = u8` part of
// `Iterator<Item = u8>`, the `Output = C` part of `Fn(A) -> C`,
// and dyn associated bindings. No trait ref exists without a
// place for its bindings, even when the list is empty.
pub struct TraitRef { pub def: DefId, pub args: ArgsId, pub bindings: BindingsId }
```

Bounds written as `T: A + B`, in `where` clauses, and on
assoc types all become predicates in source order. An
associated binding in a bound (`T: Iterator<Item = u8>`)
becomes two facts at elaboration: the trait predicate and an
`AssocEq`. Source order is observable in error messages only.
Keep it anyway; it costs nothing.

The *param environment* of a generic item is its predicates
plus their elaboration, computed once at collect and interned
as `ParamEnvId`:

1. Start with the written predicates, after substitution at
   each use.
2. For each trait predicate, add its supertrait predicates
   (the trait def's own bounds, with Self substituted).
3. For each associated binding, add the `AssocEq`.
4. Repeat to a fixpoint. The set is finite: supertrait graphs
   in scope are small, and a cycle adds nothing new.
5. Deduplicate. Keep first occurrence order for errors.

Selection and normalization read the param env through one
query (section 8). No other code walks raw predicate lists to
find supertraits.

Substitution and normalization are two different functions.
`subst(ty, args) -> Ty` is pure: it replaces `Param` by args
and erases nothing. It takes no solver and records no reads.
`normalize(ty, param_env, reads) -> Ty` rewrites projections
through impls and `AssocEq` facts (2.5); it can fail to make
progress and then returns the projection. Mono calls `subst`
on every type in a generic body, then `normalize` where a
concrete type is required. Both must be allocation-light:
return the input `Ty` unchanged when the type contains no
params or projections. Track "contains param/projection/infer"
as flag bits cached per `Ty` in the interner, computed at
intern time.

Owned type store. Today a body-local `Ty` is an offset into
the body's private table (`src/types.rs:168-197` in revision 1
line terms). Such ids die with the body, so no checked result
can be cached, shared with another crate, or written to disk.
Rule: when check finishes a body, lowering lifts its local
types into the crate session's append-only type store and
rewrites every `Ty` in the result. After the lift, the body
result owns stable session ids. Cross-crate readers translate
by structural fingerprint (section 8.4), never by raw id. The
lift is part of the `Checked` contract, not an optional step.

### 2.2 Definitions and signatures

Collect grows from `AdtDef` and `FnInfo`
(`src/collect.rs:35-55`) into a `Defs` table per crate:

```rust
pub enum DefKind {
    Module, Struct, Enum, Union, Variant, Field,
    Trait, TraitAlias(no: reject), AssocTy, AssocConst, AssocFn,
    Fn, Method, Const, Static, TypeAlias, Macro,
    Impl, Closure, Opaque, ForeignFn, ForeignStatic,
}
pub struct DefData {
    pub kind: DefKind, pub parent: Option<DefId>,
    pub name: Sym, pub module: ModuleId, pub vis: Vis,
    pub generics: Generics, pub span: Span,
    pub sig: SigData, // per-kind payload, resolved types only
}
```

Signatures resolve fully in collect, as today: fields,
variant payloads, fn params and returns, trait items with
defaults, assoc type defaults, const types, alias targets.
A signature may contain `Param`, `Projection`, and
`Opaque`. It may never contain `Infer`. Bodies check after
all signatures in the crate (and its deps' signature
surface) are frozen. This preserves the parallel body check
that makes lust fast (`src/collect.rs:1-2`).

Type aliases: transparent. `resolve_ty` expands an alias to
its target with args substituted, and records the alias def
in a side table for error messages ("type `Foo` is
`Bar<T>`"). Associated-type aliases in traits are defs, not
expansions. Generic aliases: 44 in ts-rust. Alias cycles
through non-Adt positions (`type A = B; type B = A;`) are
`L0601`. Recursive types through `Box`, `Vec`, `Rc`, refs,
and fn ptrs are fine. The infinite-size check at
`src/collect.rs:332` generalizes: a cycle in the
by-value field graph of Adts is an error.

Derives become synthetic impls at collect, one `DefId` each
(1.7). Supported: `Clone, Copy, Debug, Default, PartialEq,
Eq, PartialOrd, Ord, Hash`. Ts-rust counts: Clone 1,262,
Debug 1,137, PartialEq 573, Copy 427, Eq 379, Hash 151,
Default 936, PartialOrd 60, Ord 59. A derive expands to the
same impl shape rustc generates: field-wise, with bounds on
the Adt's type params as rustc adds them. The bodies are
synthetic IR built by collect, not source. Keep today's
derive validation idea (`src/collect.rs:306-330`) but emit
real impls so traits, mono, and drops all see one path.

### 2.3 The impl index

All trait selection goes through one index. Build it at
collect, per crate, then merge visible deps' indexes by
reference (never copy impl bodies).

```rust
pub enum SelfHead {
    Adt(DefId), Ref, RefMut, RawPtr, Slice, Array,
    Tuple(u16), Str, FnPtr, Dyn(DefId), // DefId = principal trait
    Int(IntTy), Float(FloatTy), Bool, Char, Never, Unit,
    Param,    // blanket: impl<T> Trait for T (optionally wrapped, see below)
    Infer,    // transient, never stored
}
// Index key: (trait DefId, SelfHead) -> SmallVec<ImplId, 2>
```

`head_of(ty)`: `Adt(d, _)` to `Adt(d)`; `Ref` to `Ref` or
`RefMut` by mutability? No: Rust treats `impl Trait for &T`
and `for &mut T` as distinct Self types that can overlap in
lookup only through the exact Self type, so the head must
distinguish them. Keep `Ref`, `RefMut`. `Param` self types
in an impl header (`impl<T> Tr for Vec<T>`) head to
`Adt(Vec)`; the param is inside the args. Only a bare param
Self, or a bare param under one reference or one known
smart-pointer Adt (`Box`, `Rc`, `Arc`), heads to `Param`
with a wrapper tag stored on the impl. These are the
blanket forms lust accepts (2.6).

Each impl stores: trait ref pattern (Self type pattern plus
trait args, with `Param`s for the impl's generics),
predicates, assoc bindings, item `DefId`s, a coherence
fingerprint, and its crate. Orphan rules: enforce Rust's
rule as written (the trait or a covering type must be
local). Ts-rust obeys it. Enforcing it keeps the index
merge sound: two crates cannot both add the impl that wins
a lookup in a third crate.

Method index, separate from the impl index:
`(SelfHead, method name) -> candidates`, split into inherent
and trait candidates. Trait candidates carry the trait
`DefId` so check can require the trait to be in scope.
Build it from the same collect pass. Method resolution is
in 2.10.

### 2.4 Obligations without search

Per body, check keeps a work queue, extending the current
unification context (`src/check.rs:196-215`). An obligation
is a `TraitRef` (with its bindings) plus the span that needs
it. Selection matches the *whole* trait reference: Self and
every input argument. Matching Self alone is wrong. Rust
accepts `impl Tr<u8> for S` and `impl Tr<u16> for S` at once,
and `From`, `PartialEq<Rhs>`, `Add<Rhs>`, `Index<I>`,
`FromIterator<A>` all need their inputs to pick an impl.

A type has a *known head* when its outer form is fixed after
following inference links: an Adt, a scalar, a ref, a tuple,
and so on. A bare unresolved `Infer`, or a generic `Param`
with no structure, has no known head. Section 2.12 lists the
points where a known head is required.

Selection algorithm. A *probe* is a tentative unification
that records every binding it makes and can roll them back.
A probe unifies headers only. The one exception is the
clause filter in step 3, which can only remove candidates,
never pick one.

A trait ref is *provably false* when this check says so.
The check binds nothing and commits nothing:

- If the ref matches a predicate in the current param env,
  it is not provably false. It can hold.
- Else collect header candidates as in step 2. If there
  are none, and the ref has a known head with no inference
  var that can change the set, the ref is provably false.
- If there are candidates, the ref is provably false only
  when every candidate has at least one trait-predicate
  where clause that is itself provably false after
  substitution with that candidate's own probe bindings.
  Recurse with the same depth cap and cycle set as
  selection (step 7). One level is not enough:
  `Box<[T]>: IntoIterator` must remove the `Iterator`
  blanket by way of `Box<[T]>: Iterator`, whose only
  candidate (`Iterator for Box<I>`) needs `[T]: Iterator`,
  which has no candidate at all.
- In every other case the ref is unknown, not false: Self
  has no known head, a clause is not a trait predicate
  (an outlives clause, an equality), a cap or a cycle
  stops the check, or a clause can hold. Unknown stays
  unknown. A candidate is never kept or dropped because
  its clauses proved *true*.
- The check records the same `ImplSet` and failed-lookup
  reads as a failed selection (section 8). A body that
  dropped a candidate because a bucket was empty must
  recheck when an impl joins that bucket.

1. If the obligation matches a predicate in the current
   param env (2.1, after substitution, supertraits and
   `AssocEq` facts included, each fact matched under its
   own binder), select `ParamEvidence`. Param
   env candidates win over impls, as in rustc. Mono re-solves
   with concrete types. If two param-env predicates match
   and unification does not pick one (for example `T:
   From<u8> + From<u16>` against the obligation `T:
   From<?X>`), defer as in step 6. Never take the first
   match: rustc stays ambiguous there too (E0283).
2. Else collect candidates. Look up `(trait, head_of(Self))`
   in the impl index, plus the blanket bucket for the Self
   wrapper shape (2.6). For each impl, probe-unify its full
   trait ref pattern (Self, all input args, and bindings)
   against the obligation. Keep the impls whose probe
   succeeds. Roll back every probe that is not confirmed.
3. If two or more candidates remain and Self is concrete
   enough for the provably-false check, run the clause
   filter: drop each candidate that has a trait-predicate
   where clause which is provably false after substitution
   with that candidate's probe bindings. This is what
   selects `IntoIterator for Vec<T>` over std's blanket
   `impl<I: Iterator> IntoIterator for I`: both headers
   match `Vec<u8>`, but `Vec<u8>: Iterator` has no
   candidate, so the blanket drops. The filter drops
   candidates only. It never selects one because its
   clauses held, and it never binds an inference var.
   If exactly one candidate remains, confirm it: keep its
   probe bindings. This binds inference vars, integer vars,
   and float vars. Two cases that must work:
   `let v: Vec<_> = it.collect()` selects the one
   `FromIterator` impl and binds the element type (ts-rust
   has 62 `Vec<_>` sites), and `s[x]` with an integer var
   `x` selects `Index<usize>`, so `x.wrapping_sub(1)` is a
   `usize` op. Push the impl's predicates (substituted) as
   new obligations. If a predicate of the selected impl
   fails, that is an error. Never fall back to another
   candidate.
4. If an impl param is still unbound after the header match,
   bind it from facts already present, in this order, with
   no search: (a) an associated binding on the obligation;
   (b) an `AssocEq` in the impl's own predicates whose
   projection normalizes now, for example
   `impl<I: Iterator<Item = T>, T> Tr for I`, where a use site
   cannot name `T`. One pass over the impl predicates. If a
   param stays unbound, defer while inference can still
   change the candidate set; at the end, error `L0613`
   ("impl parameter is not known from the trait inputs").
   Do not hint at a turbofish: a use site has no slot for an
   impl parameter. The fix hint names the impl and suggests
   a rewrite of that impl.
5. If no candidate remains and the trait ref has a known
   head with no inference var that can change the set,
   record a failed lookup (section 8) and error `L0612 no
   impl of Trait for Type`, listing the bucket's impls when
   the bucket is non-empty.
6. If two or more candidates remain after the filter, or
   Self has no known head, defer the obligation. Deferral
   ends at a point where the type must be known (2.12):
   there, an unresolved obligation is
   `L0610 type annotations needed`, matching
   rustc E0282 or E0283 as the case fits. Never pick one of
   several candidates to make progress.
7. Memoize by `TraitRef` in the body; the provably-false
   check shares the memo table. Depth cap 64 and a
   cycle set, shared by selection and the filter:
   re-entering the same `TraitRef` on the stack
   is `L0611` (overflow), matching rustc's overflow class.

Queue processing runs at fixed points only: before a
structural resolution (2.12), at coercion sites, and at body
end to a fixpoint. Running the queue after every expression
that binds an inference var can go quadratic in large
bodies. At body end, anything left is an annotation error,
never a silent default, except integer and float literal
fallback (`i32`, `f64`, as today).

What this rejects that rustc accepts: obligations where an
impl param follows only from a chain of predicates, beyond
step 4; and obligations where two candidates survive
because the losing clause is false only for reasons the
provably-false check cannot see (it depends on a generic
param's own bounds, say). Those defer and end at `L0610`.
`lust port scan` reports impl-param sites as `L0613`, a
class of its own, separate from ordinary annotation sites
(`L0610`).
Spike K7 counts both classes after this algorithm lands, not
before: with a Self-only or defer-on-infer rule the count
measured the algorithm, not the code. Do not add backtracking
or speculative predicate search. Probes over disjoint header
patterns are not search: each probe is one first-order
unification, and at most one probe is confirmed. The clause
filter is not search either: it evaluates each candidate's
clauses on its own, removes only definite "no" answers,
and keeps deferral for everything else.

Auto traits and `Sized` do not use the queue. They compute
structurally (2.7). `Drop` is not an obligation; drop glue
asks "does this type have a `Drop` impl or droppable
fields" directly.

### 2.5 Associated types and consts

A trait def lists assoc items. An assoc type use
`<S as Tr>::A` becomes `Projection(assoc_def, args)`
where args are the trait ref (Self first). Normalization:

- If the trait ref selects a concrete impl (2.4 step 3),
  the projection rewrites to the impl's binding, then
  normalization recurses.
- If it selects `ParamEvidence` and the param env carries an
  `AssocEq` for it (`T: Iterator<Item = u8>`), rewrite to
  that type. The equality matches under its binder (2.1):
  instantiate the binder the same way as the trait ref it
  came with, never outside it. The same holds for
  supertrait assoc types through the elaborated param env.
- Else it stays a `Projection` type inside the generic
  body. It unifies only with the identical projection or
  through a binding that appears later. Mono normalizes
  it after substitution. A projection that survives mono
  is a compiler bug, not an error path.

Assoc consts: same shape, values are `ConstId`s evaluated
by the const evaluator. Ts-rust declares 2 user assoc
types and uses std assoc types (`Item`, `IntoIter`,
`Target`, `Output`) in 66 impls. Example: `IntoIterator`
for `&SharedList<T>` at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/checker/types.rs:289-296`
binds `Item = &'a T` and `IntoIter = slice::Iter<'a, T>`.
Assoc const example: `ExpectedJsonKind::JSON_TYPE`
(DESIGN-TS section 3). GATs (assoc types with their own
params): reject `L0620`. Ts-rust has none.

`?` desugars through `Try` in Rust, but lust implements
`?` as a direct match on `Result` and `Option` plus
`From::from` error conversion, checked as a normal
obligation. User `Try` impls: reject. Ts-rust uses `?`
2,422 times (plus 5,516 generated) on `Result` and
`Option`. The direct form covers it and skips a
not-yet-stable-in-spirit trait.

Operator traits (`Add`, `BitOr`, `Index`, `Deref`, and
kin) are normal traits. Binary operator syntax checks the
builtin scalar path first, then the trait path with one
obligation. `go_flags!` generates `BitOr::Output`
impls at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/flags_macros.rs:53-58`,
so assoc `Output` must normalize in operator result types.

### 2.6 Coherence and blanket impls

At collect, for each trait, check every pair of impls whose
*full trait refs* can unify: Self pattern, every input arg,
and bindings. Unifying Self alone is wrong twice over.
`impl<T> From<T> for T` would seem to overlap every user
`From` impl, and std's `impl<I: Iterator> IntoIterator for
I` would seem to overlap `IntoIterator for Vec<T>` and six
impls in ts-rust (`ast/node.rs:1585`, `ast/node.rs:1594`,
`checker/types.rs:289`, `checker/types.rs:298`,
`core.rs:1134`, `core.rs:1145`). Rust accepts all of those,
so lust must too.

When the full trait refs unify, try to disprove the overlap
exactly where rustc can: by the orphan rule. A where clause
of either impl, after unification, "cannot hold" when all
of these hold:

- the clause is a trait predicate;
- its Self type is a concrete type that is local to the
  crate that checks coherence, or a fundamental wrapper
  (`&`, `&mut`, `Box`, `Pin`) of such a local type. A bare
  type param is never such a Self: a generic `T` can gain
  any impl downstream, so no clause on `T` alone is
  disprovable;
- no impl in the index matches that trait ref, and the
  orphan rule says no downstream crate can add one: for a
  local Self under fundamental wrappers, a downstream impl
  of a foreign trait would need a local covering type,
  which this Self does not give it. When the *trait* is
  local instead, the same test runs with the roles
  swapped: the impl set for a local trait is closed once
  this crate and its deps are indexed, but only for Self
  types that are already concrete here.

An empty impl bucket alone proves nothing. `impl<T: A> Tr
for T` and `impl<T: B> Tr for T` overlap even when `A`,
`B`, and `Tr` are all local and `A` and `B` have no impls
yet: some `T` can implement both. Rust rejects that pair
with E0119, and so does lust (`L0615`). That is a table
lookup under the orphan test, not a search. If nothing
disproves the pair, it overlaps: `L0615`, as in Rust.
Worked cases:

- `IntoIterator for Vec<T>` vs the blanket: unify with
  `I = Vec<T>`. The clause `Vec<T>: Iterator` cannot hold:
  `Vec` is local to `alloc`, no such impl exists, and no
  downstream crate can add one. No overlap.
- `IntoIterator for &'a SharedList<T>` vs the blanket:
  clause `&SharedList<T>: Iterator`. Self is a fundamental
  wrapper of a local type, and no impl matches. No overlap.
- `impl<T: A> Tr for T` vs `impl Tr for MyType`, with `A`
  local, `MyType` local, and no `A for MyType` impl: the
  clause is `MyType: A` after unification. A downstream
  crate cannot impl the local trait `A` for the local
  type `MyType`, so the clause cannot hold. No overlap.
  Rust accepts this pair.
- `impl<T: A> Tr for T` vs `impl<T: B> Tr for T`, on a bare
  param Self: nothing can disprove either clause, whatever
  is local. Overlap. Rust rejects these too.

Selection still checks the predicates of the chosen
candidate (2.4 step 3). Coherence never lets two candidates
both pass for one concrete trait ref, but a probe can match
two headers for one concrete Self (a concrete impl and a
blanket); the 2.4 clause filter removes the one whose
clauses cannot hold, and 2.4 step 6 defers what stays
ambiguous while inference is open.

Accepted blanket Self forms, stored with a wrapper tag:
`T`, `&T`, `&mut T`, `Box<T>`, `Rc<T>`, `Arc<T>`. A blanket
with wrapper `&T` sits in the `Ref` bucket as a param
pattern. Bare `T` sits in a per-trait `Param` bucket. At
lookup, check probes the concrete bucket and the blanket
bucket for the Self wrapper shape together (2.4 step 2).

Ts-rust's 6 blanket impls fit this subset:

- `impl<T: Any + MarshalerTo + Debug + Send> AnyValue for T`
  at `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json_ext.rs:43-47`.
  Bare param. `AnyValue` has no other impls.
- `impl<T: MarshalerTo + ?Sized> MarshalerTo for &T` at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json.rs:1660-1664`.
  `&T` wrapper. Concrete `MarshalerTo` impls are on Adt
  heads, disjoint from `Ref` by head alone.

Generic impls on named containers (178 in ts-rust), impls
for `&T` (6), and impls for `dyn Trait` (6) are normal
index entries. Negative impls and overlapping marker traits
in user code: reject. Specialization in user code: reject.
Std gets its observable specialization through the closed
predicate list in section 3.4, not through impl overlap.

### 2.7 Auto traits: Send, Sync, Unpin, unwind safety, Sized

`Send`, `Sync`, `Unpin`, `UnwindSafe`, and `RefUnwindSafe`
compute structurally per type. The two unwind traits are
real bounds on `catch_unwind` (7.2): rustc rejects a closure
that mutates a captured `&mut` across `catch_unwind` without
`AssertUnwindSafe` (E0277). An unchecked `catch_unwind` API
would accept that program, so the traits are not optional.
Each auto trait has its own fixed table. No table borrows
facts from another. In particular, a negative `UnwindSafe`
fact does not follow from the `Send` table.

- Scalars, refs, raw pointers, fn ptrs: by fixed table,
  pinned in one file. The table must state, at least:
  `&T: Send` iff `T: Sync`; `&T: Sync` iff `T: Sync`;
  `&mut T: Send` iff `T: Send`; `&mut T: Sync` iff
  `T: Sync`; `*const T` and `*mut T` are neither `Send` nor
  `Sync`; `*const T` and `*mut T` are `UnwindSafe` but the
  types that hold them still get their own facts below;
  `&mut T` is not `UnwindSafe` (it is `RefUnwindSafe` only
  under the rules in std); `PhantomPinned` is not `Unpin`,
  which makes any Adt that holds it not `Unpin`.
- `Adt`: all field types (with args substituted) must
  hold the trait, combined with the Adt's own marker
  fields. `PhantomData<T>` contributes `T`'s auto traits,
  including the raw-pointer marker idiom ts-rust uses
  (DESIGN-TS section 6 cites `core.rs:4467`).
- Std types whose fields contain raw pointers (`Vec`,
  `Box`, `Rc`, `Arc`, guards) do not get correct facts from
  structure alone. Their facts live in one checked registry
  in the shipped std source: explicit `unsafe impl` and
  negative impl lines, in the same place, diffed against
  real std by the surface parity gate (3.1). Examples that
  must be right: `MutexGuard` is not `Send`; `Rc<T>` is
  neither `Send` nor `Sync`; `Mutex<T>: Sync` if `T: Send`;
  `RefCell<T>` is `Send` if `T: Send` and never `Sync`.
  A structural guess that makes a guard `Send` accepts a
  program rustc rejects. User code may
  write `unsafe impl Send/Sync` only under the opt-in
  `unsafe` support (PLAN.md decision 3). Ts-rust has no
  `unsafe impl` in its own code.
- Closures: from capture types. `dyn`: from its bound
  bits. Params: from the param env. Cycles through Adts:
  compute by fixpoint with a three-state lattice
  (yes/no/in-progress-as-yes-then-verify), memoized per
  `(Ty, trait)`. Store results in the crate session;
  invalidate by the Adt's signature fingerprint.

`Sized`: every type param has an implicit `Sized` bound
unless written `?Sized`. Unsized types: `str`, `[T]`,
`dyn Trait`, and structs whose last field is unsized (the
struct is then unsized; only `FileRef`-style uses in
ts-rust need this, DESIGN-TS section 2). Unsized values
may only sit behind a pointer-like (`&`, `&mut`, `Box`,
`Rc`, `Arc`, raw ptr) or as the last field. Check this at
collect for fields and at check for locals and params.
`?Sized` bounds appear 203 times in 14 ts-rust files, so
this is core, not polish.

Where checks fire: `thread::spawn` and `scope` (7.3),
shared statics (`Sync`), `Arc`/`Mutex` bounds in std
signatures (they are normal predicates that the
structural solver answers), `dyn` bounds that name
auto traits, and `catch_unwind` (`UnwindSafe` on the
closure). `AssertUnwindSafe<T>` reports `UnwindSafe` for
any `T`, only where the source writes it.

### 2.8 dyn Trait and vtables

`Dyn(BoundsId, Region)`. Dyn compatibility (object
safety), checked in full at the `dyn` type's span. A trait
is dyn compatible only when all of these hold:

- The trait does not require `Self: Sized`.
- Every supertrait is dyn compatible.
- No associated consts.
- Every method is dispatchable: its receiver is one of the
  receiver forms in 2.9 with a known vtable call shape, it
  has no generic type params of its own, and `Self` occurs
  only as the receiver, behind the receiver form. There is
  no allowance for `Self` in any other position: not as a
  return, not as a plain argument by value or by reference
  (`fn other(&self, value: &Self)` fails in rustc with
  E0038), and not in a generic argument that stays
  concrete. The trait's own object type in an argument or
  return is fine (`fn f(&self, x: &dyn Trait)`, `-> Box<dyn
  Trait>`): it names the erased trait, not `Self`. `Self`
  itself, even boxed (`Box<Self>` as an argument), is
  E0038 there. `trait Bad { fn copy(&self) -> Self; }`
  with `&dyn Bad` fails in rustc with E0038 and must fail
  here. A method excluded by `where Self: Sized` is simply
  not in the vtable.
- Associated types are bound in the `dyn` bounds
  (`dyn Iterator<Item = u8>`), or every method that uses
  them is excluded as above.

Failure is `L0701` with the trait and the offending item
named. `dyn` with two non-auto principal traits: reject
(Rust rejects too). The `BoundsId` stores the principal
trait ref, its bindings, the supertrait refs, and the auto
trait bits, including auto traits that come only from a
supertrait (section 2.1). Method calls on a trait object
can use the principal trait and its supertraits with no
import (2.10).

Dev representation: a fat pointer `{ data: *mut (), vtable:
*const VTable }` (section 4.4 for the C form).

Owning pointers to unsized values (w-unsized, `check/own.rs`,
`cgen/own.rs`): `Box`, `Rc`, and `Arc` of `str`, `[T]`, `dyn Tr`,
`RefCell<dyn Tr>`, and `Mutex<dyn Tr>` are the pointee's fat form
(`lust_str`, the slice struct, or `lust_dyn`). An `Rc` or `Arc`
points at its value; the `strong` and `weak` counts are the 16
bytes before it, as in `RcI_T`, so `Rc<T>` to `Rc<dyn Tr>` or
`Rc<[T; N]>` to `Rc<[T]>` only takes the value's address. A
`RefCell<dyn Tr>` (`Mutex<dyn Tr>`) pointer's data points at the
cell (the borrow flag, or the futex word and poison byte, first),
and its vtable is the value's: the value sits at the first offset
past the cell words that the vtable's align allows. Every empty
`Arc<str>` and `Arc<[T]>` that `Default` makes shares one static
allocation (runtime `lust_arc_empty`), as std's do.

```c
struct lust_vtable {
    void (*drop_in_place)(void *);
    uint64_t size, align;
    uint64_t type_id;              // for Any, else 0
    const struct lust_vtable *super_0; // one slot per supertrait, in trait-decl order
    // then one fn ptr per object-safe method, in trait declaration order
};
```

Rules:

- One vtable instance per `(concrete type, dyn bounds)`,
  emitted as a static in the glue unit, deduplicated by
  mono like an instance (section 4). Method entries point
  at slot trampolines (4.5), never at a body address, so
  a daemon overlay edit cannot leave a stale callback.
  DESIGN-TS section 3 states this requirement.
- Upcasting `dyn Sub` to `dyn Super` uses the `super_N`
  slots. Multi-level upcasts chain at check time to a
  fixed slot path; no runtime search.
- `Any` (as built, W-CHECK-G3, `src/check/any.rs`): identity
  is the full structural key of the concrete type: kind tag,
  stable def pair (1.7) for Adts, closures, and fn items,
  and the full argument structure with regions erased.
  Primitives, tuples, arrays, slices, refs, fn pointers,
  closures, and dyn types all have keys. A `TypeId` is a
  128-bit SipHash of that key (two `u64` words), as rustc's
  is a 128-bit hash: the same in every body and every
  daemon build, so no per-binary table has to be renumbered
  when an object is reused. The planned checked 64-bit
  table was dropped for that reason; a 128-bit collision is
  as unlikely as rustc's. A `dyn Any` vtable holds the two
  words after its header (`object::VT_ANY_ID`); a user trait
  with `Any` as a supertrait reaches them through its super
  slot. `type_id`, `TypeId::of`, `is`, `downcast_ref`,
  `downcast_mut`, and `Box`/`Rc` `downcast` compare words,
  then read the data pointer (`Rvalue::DynData`). `Any`
  keeps the `T: 'static` bound; a type with a non-static
  region has no `TypeId`.
- Unsizing coercions supported: `T -> dyn`, and inside
  `&`, `&mut`, `Box`, `Rc`, `Arc`, plus `Rc<RefCell<dyn>>`
  style nesting through one smart pointer whose pointee
  unsizes. Array-to-slice unsizing in the same positions.
  Coercion sites are recorded in `Checked` like today's
  `Coerce` (`src/check.rs:117-128`); extend that enum.

Ts-rust scale: 1,917 `dyn` types, 94 user traits, `dyn Fn`
285, `dyn FnMut` 233, containers `Rc` 667, `&` 498, `Box`
316, `Arc` 109. `dyn Any` with downcasts: 127 uses. The
visitor aliases at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/ast/visitor.rs:26-33`
(`Rc<dyn Fn(Node, &mut NodeVisitor) -> Node + 'a>`) are
the design center: regional `dyn Fn`, inside `Rc`, held
in struct fields, called recursively.

### 2.9 Closures and Fn traits

Each closure expression gets a `Closure` def (1.7). Its
type is `Closure(def, args)` where args are the capture
types in capture order. At codegen it is an anonymous
struct of its captures (4.4).

Capture analysis (edition 2024 precise captures): walk
the closure body, record each used place as (local,
projection path). Capture the smallest prefix place that
covers all uses of one local, per Rust's disjoint capture
rules. Capture kind: by ref, by mut ref, or by move,
upgraded by use (move out forces move; mutation forces
mut ref; `move` keyword forces move for `Copy`-eligible
places a copy, as in Rust). The capture list is fixed at
check time and stored on the def. Borrow checking treats
the closure value as holding those loans (section 5).

Trait implementation, decided by body use of captures:

- Moves a capture out, or drops a by-move capture and the
  closure can run again: `FnOnce` only.
- Else mutates a capture: `FnMut` and `FnOnce`.
- Else: `Fn`, `FnMut`, `FnOnce`.

These are synthetic impls in the index, keyed by the
closure def. The `Fn` traits use sugar: `Fn(A, B) -> C`
is a `TraitRef` with args `(Self, (A, B))` plus assoc
`Output = C`. Higher-ranked `Fn(&T)`: the principal use
(545 implicit cases in ts-rust) is a rank-1 binder over
the ref regions in the args. Represent `for<'a> Fn(&'a
T)` by a binder on the `TraitRef` in predicates and
`dyn` bounds. At call sites, instantiate the binder with
fresh region vars. To prove that a value meets a
higher-ranked bound, use a placeholder region and a leak
check (5.5). No other higher-ranked forms:
binders on fn *items* are their late-bound lifetime params
(5.5); binders nested under another binder are `L0710`.

Closure signature inference: from the expected type when
it is an `Fn` bound, a `dyn Fn`, or a fn ptr; else from
annotations on params; else params get fresh `Infer`s. The
body checks at the definition point, in source order. A
structural use inside the body (a method call, a field
access, an index on a param) needs a known head at that
point (2.12). `let f = |x| x.len(); f(vec![1u8])` is an
error, as in rustc (E0282): the later call does not rescue
the body. Plain unification inside the body can still bind
a param: passing it to a fn with a known signature, or
returning it where the return type is known. If a param
`Infer` survives to the end of the closure body, error
`L0610` asking for an annotation on that param. Stored
closures with no expected type are the common failure;
ts-rust stores 349 in `let`s. Each one that stays unknown
needs one annotation. That is an accepted codemod
class (it does not change machine code).

`FnOnce` call consumes the closure value (or the box
pointee). Through `dyn FnOnce`, the vtable method takes
`Box<Self>`-style ownership of data and drops the env
after the call. Calling a `dyn FnMut` needs `&mut` to the
fat pointer's data. Check enforces these receiver rules.

Function items as values: type `FnDef(def, args)`,
zero-sized, implements the `Fn` traits its signature
matches, coerces to the fn ptr `FnPtr(sig)`. Early-bound
lifetime params are part of the `FnDef` args; late-bound
ones become the binder of the `FnPtr` it coerces to (5.5).
A std fn with no item value in lust (`Vec::new`, `Arc::new`,
`Ord::cmp`; the list is `parser::eta_arity`) used as a value
is parsed as the closure `|a, ..| path(a, ..)`: it behaves as
the fn item does, but each use has its own type, so a
`TypeId` of one is a reject (L0702).

Typed receivers. The receiver type grammar is recursive:

```text
Recv ::= Self
       | &Recv | &mut Recv
       | Box<Self> | Rc<Self> | Arc<Self>
       | Pin<&Self> | Pin<&mut Self> | Pin<Box<Self>>
```

So `self: &Rc<Self>` and `self: &Arc<Self>` are in the
grammar, not only `Rc<Self>`. Ts-rust uses `&Rc<Self>` in
159 places, for example
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/packagejson.rs:1092`.
Any other arbitrary self type is `L0722`. Method
resolution matches these forms by receiver type (2.10 step
3): for `&Rc<Self>`, the place must have type `Rc<T>` (or
autoderef to it) and the call takes a reference to that
smart pointer value, without dereferencing to `T` first.
The same rule covers a plain smart-pointer receiver and a
`Pin` receiver (std only at first for `Pin`).

### 2.10 Method resolution

Input: receiver type `R`, method name, arg types,
expected result. The receiver must have a known head at
this point (2.12); if not, `L0610`. Algorithm (Rust's,
restricted):

1. Build the autoderef chain: `R`, then `*R` via `Deref`
   (or `DerefMut` when a `&mut` receiver or a unique
   place is needed), repeatedly. Cap 32 steps. Builtin
   derefs: `&T -> T`, `&mut T -> T`, `Box/Rc/Arc<T> -> T`
   (through their `Deref` impls, not special-cased, once
   std is source), `[T; N] -> [T]`, `String -> str` via
   `Deref`. Record each step's type.
2. For each step type `S`, in order, probe receiver forms
   in Rust's order: by value `S`, then `&S`, then `&mut
   S`. For each form, look up inherent methods first
   (exact receiver type match up to the form), then
   trait methods whose trait is in scope and whose Self
   pattern matches. A trait is in scope when it is
   imported, in the std prelude, named by a bound in the
   current param env, or the principal trait (or a
   supertrait) of a `dyn` receiver. The last two need no
   import. First hit
   wins. Two impls of the *same* trait that both match the
   receiver are not an ambiguity here: the obligation for
   that trait ref goes through 2.4 selection, clause
   filter included, and picks the impl the method comes
   from. Two trait hits in the same probe with different
   traits: `L0720 ambiguous method`, fix hint gives the
   fully qualified form. Inherent and trait in the same
   probe: inherent wins, as in Rust.
3. Typed receivers (2.9 grammar) match by receiver type.
   For `Rc<Self>`, any chain step can equal the pointee
   while the place holds the smart pointer. For
   `&Rc<Self>`, the place must hold an `Rc<T>` and the call
   passes a reference to it; no autoderef to `T` runs for
   that candidate. The same shape holds for `&Box<Self>`,
   `&Arc<Self>`, and the `Pin` forms.
4. On a hit, create obligations for the method's bounds
   and unify args. Generic method params come from args
   and the expected type. `?Sized` Self types (`str`
   methods on `&String`) work through the deref chain.
5. Every probe records a candidate-set read (section 8):
   `(Self head, name, receiver form)` for the inherent set
   and for each trait bucket probed, hit or miss. A body
   that picked a trait method must recheck when a new
   inherent method with the same name appears, because
   Rust then picks the inherent one. No hit at all:
   record the same reads, then error `L0104` (the existing
   "no such method" code) listing same-name methods on
   other types.

Field access: the base type must have a known head.
Autoderef to the first Adt or tuple with
the field, checking field visibility. `dyn` has no
fields. Index syntax needs a known head on the indexed
value, then goes through one path: `Index`/`IndexMut`
obligations (2.4). The slice, array, and `Vec` cases are
std impls once std is source. Keep a fast path only if
profiles demand it, and only if it binds inference the
same way (the `s[x]` case in 2.4 step 3).

Current code hardcodes all of this per `Builtin`
(`src/check.rs:1002-1227`). The method index plus this
algorithm replaces it. Autoref/autoderef bookkeeping
already exists in `Res::Method { derefs, autoref }` at
`src/check.rs:91-100`; extend the recorded form to a
small `MethodRes { def, args, derefs, autoref,
receiver_coerce }`.

### 2.11 impl Trait

- Argument position (`fn f(x: impl Clone)`): sugar for a
  fresh type param, exactly as in Rust. 371 uses.
- Return position: an `Opaque` def per (fn, position).
  Check records the hidden concrete type from the body.
  All return paths must give the same hidden type.
  Captures follow edition 2024 rules: the opaque captures
  all in-scope type and lifetime params unless `use<>`
  restricts. Support `use<>` syntax; ts-rust uses it once
  (DESIGN-TS section 3, `impl Send + use<>`). Callers see
  only the bounds, with one exception: auto traits leak,
  as in rustc. If the hidden type is `Send`, the opaque is
  `Send` even when the bounds do not say so (same for
  `Sync`, `Unpin`, and the unwind traits). A test with
  `thread::spawn` on an opaque return value gates this.
  Mono substitutes the hidden type.
  Returning different closure types per branch: reject
  unless they unify, as in Rust.
- `impl Trait` in assoc type position and in `let` type
  ascriptions: reject. Not used in ts-rust.

40 return-position uses in ts-rust, mostly `impl
Iterator`. Iterator fusion (4.3) sees through the opaque
inside the defining crate only at mono time, never at
check time across the boundary. That keeps fusion sound
without making the opaque transparent to callers.

### 2.12 Inference boundary

Inference stays body-local, as today (`src/check.rs:1-2`),
plus these stated inputs: expected types flow down from
signatures, `let` ascriptions, return position, struct
field types, and `Fn` bounds for closures. Generic args
at a call come from: explicit turbofish, arg types,
the receiver, assoc bindings written at the use, and the
expected result type. `collect` gets its target from the
expected type or turbofish; ts-rust writes the target
explicitly in only part of its 804 collects, the rest
come from ascriptions and field types, which the expected
type flow covers.

When a type must be known. At these points, in check order,
the type in question must have a known head (2.4). If it
does not, error `L0610` at that point (rustc E0282 or
E0689). Never defer these to body end:

- a method call (the receiver type);
- a field access (the base type);
- an index (the indexed type; the index type then follows
  from the selected `Index` impl);
- a deref (the pointee source type);
- the `?` operator (the operand type);
- an operator on a non-scalar (the left operand type);
- a match or `if let` that must know the scrutinee enum;
- a closure body use of any of the above on a param.

Running the obligation queue happens just before each such
point (2.4). If the queue binds the head, checking goes on.
That is how `Vec<_>` collect and `s[x]` infer without any
search, and how `|x| x.len()` still fails.

Not inferred, by design: types across fn boundaries
(signatures stay explicit in source, as in Rust), impl
params beyond 2.4 step 4 (`L0613`), closure param types
with no expected `Fn` and no body constraint, and numeric
types beyond literal fallback and one-candidate selection.
Each gap errors with the specific missing annotation. This
is the "how far beyond local" answer: no further. The
deterministic solver is what keeps check near-linear and
independently re-runnable per body, which the daemon
depends on.

### 2.13 Bounded const evaluation

Const contexts are: `const` and `static` initializers,
array lengths and repeat counts, enum discriminants, const
generic args, inline `const { ... }` blocks, and
`const _: () = assert!(...)` items. One evaluator owns all
of them. It is bounded, and anything outside the bound is
`L0630`. A general const interpreter stays out of scope.

Supported forms, which are the forms ts-rust uses:

- Literals, arithmetic and comparisons on ints, bools, and
  chars, with rustc overflow rules in const (overflow is a
  const error, not a wrap).
- Layout queries: `size_of`, `align_of`, `offset_of!` on
  types the layout contract supports (4.4).
- Struct, enum, tuple, and array construction from const
  parts. Array repeat `[const { E }; N]` evaluates `E`
  once per element slot. Example:
  `[const { OnceLock::new() }; CHUNKS]` at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/core.rs:472`.
- Const fn calls where the callee body stays inside this
  list: blocks, `let`, `if` and `match` on const values,
  bounded loops, field access, and calls to other const
  fns in the list. Std const fns in scope include
  `OnceLock::new`, `RefCell::new`, `Mutex::new`,
  `Vec::new`, `String::new`, and the `new` fns of the
  adapter types. Example: the `RefCell::new(BuildStores {
  .. })` initializer at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/ast/store.rs:1157`.
- References to other consts and statics, string and byte
  literals, and promoted temporaries. A const value is
  `Scalar | Aggregate(fields) | Ref(static or promoted) |
  Slice(ptr, len)` in the const store.
- Associated const lookup through the selected impl.
- `assert!` and `panic!` with a literal message in const
  position: a false assert is a compile error, as in
  rustc.
- Inline const blocks in a generic body, for example the
  `const { assert!(size_of::<Option<V>>() <= 32) }` at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/core.rs:4085`.
  Check the block in generic form (well-formed, const
  eligible), then evaluate it again per instance at mono
  after substitution (4.1). A module-level `const _` item
  captures no generic params of any fn; do not model the
  inline form as one.

Const eligibility runs before any emission. A `static` or
`const` initializer that calls a non-const fn is `L0631`,
matching rustc E0015: `static S: String = String::from("x")`
must fail. Running a non-const initializer at startup is
not a substitute. There are no synthetic runtime init fns
for statics. A static's const value becomes static data in
the glue unit: scalars inline, aggregates as nested data,
refs as relocations to the target static or promoted
block. Mutable statics use the same data path.
`thread_local!` and `OnceLock` lazy semantics live in std
source above const initial values (7.3), not in the data
path. Step cap: 1,000,000 evaluator steps per const item,
then `L0630` with the item named.

One owner (W-CORELANG, then W-CHECK-G for the generic
form). Gates split by what exists at each stage; no gate
may cite a type from a later wave. The wave A1 gate is
an executable initializer corpus over *locally defined,
already supported types only*: local stand-ins for the
three ts-rust shapes above (a local cell-like struct in
a static, a local once-like const fn in an array
repeat), a discriminated enum const, and the E0015
reject. The source-std versions of the same shapes (the
real `RefCell::new(BuildStores { .. })` static, the real
`[const { OnceLock::new() }; CHUNKS]`, a `Mutex::new`
static) gate at the first stage that supports each
type: `RefCell` with W-STD-B in wave B, `Mutex` and
`OnceLock` with W-THREADS in wave C. The generic
inline-const case (the `core.rs:4085` assert shape)
gates with W-CHECK-G and W-MONO in wave B, where its
checker and per-instance evaluator live. Each gate
names its stage in its Done line (9.3).

## 3. Std strategy

### 3.1 The decision

Write std in lust source. Ship it with the compiler as
three crates under `library/` in the lust repo:

```text
library/core/    no OS, no alloc: traits, Option, Result, iter adapters,
                 fmt traits, slice/str methods, mem, cmp, hash, num
library/alloc/   heap types: String, Vec, Box, Rc, Arc, collections,
                 format!, Cow, BTreeMap
library/std/     OS: fs, io, env, process, path, time, thread, sync,
                 panic runtime hooks, prelude
library/deps/    adapter crates (3.6): indexmap, smallvec, rustc-hash
```

Lust compiles these crates with lust itself, once per
(lust version, target, profile) tuple, and caches the
result on disk like Go's build cache (PLAN.md decision
1). A user crate's `std` dependency is implicit, rooted
at `library/std`. The prelude (1.3) is
`library/std/src/prelude.rs`.

Why source, not more `Builtin` cases: today each std
method costs edits in four places (`check.rs` typing,
`ir.rs`, `cgen.rs`, `runtime.c`). The `Builtin` enum has
about 55 cases for a tiny surface. Ts-rust touches 24,879
`Vec`/`String`/`Option` paths alone (INVENTORY std
table), plus `Result`, iterators with 3,516 chains,
`Rc`/`RefCell` in 2,608 functions, and the `io`/`fs`/
`time` surface. As source, a new std method is one lust
fn: check, borrowck, mono, and codegen already handle
it. Std bugs become difftest programs, not compiler
hacks. And generic std code monomorphizes with the same
machinery as user generics, which VERIFY G requires:
almost all real instances come from std, not user
generics (VERIFY G section P1).

Std source is privileged in exactly four ways. This list
is closed. A fifth privilege needs a change to this
section:

1. It may use the intrinsic functions in 3.2, through a
   private module `core::intrinsics`. The checker allows
   `intrinsics` calls only in crates whose manifest the
   compiler ships (matched by crate disambiguator of the
   shipped library), never by name matching in user
   source. The shipped crates that may name intrinsics are
   `core`, `alloc`, `std`, and the adapter crates named in
   the 3.6 table, each only for the intrinsics its row
   lists.
2. It may use `unsafe` blocks, raw pointers, and
   `UnsafeCell`. This is the opt-in `unsafe` from
   PLAN.md decision 3, scoped to shipped crates first.
   User crates get `unsafe` only for shim-facing code
   in milestone 7, behind the same checker support.
3. It may call the specialization predicates in 3.4. The
   trait system does not change.
4. Its `Drop` impls may carry the may-dangle flag (5.4),
   on the same impls as real std. User impls may not.

Surface parity. Selection, method probing, coherence, and
auto traits depend on the *set* of std impls and inherent
methods, not only on behavior. A partial std changes
results: a missing inherent method lets a user extension
trait win a probe; a missing impl turns rustc ambiguity
into a single candidate; a missing impl lets an
overlapping user impl pass coherence; a structural
`MutexGuard` can come out `Send`. So lust std must declare
the same surface as real std for every type and trait it
exposes:

- Generate a std surface manifest from rustc 1.99 rustdoc
  JSON (`RUSTC_BOOTSTRAP=1` where the toolchain needs it).
  It lists every public inherent method name and every
  impl header for the std types and traits lust exposes.
- Lust std declares all of them. A body that does not
  exist yet is a stub that rejects at use with `L0640`
  naming the item. A missing declaration is a build error
  in the std build, caught by a manifest diff in CI.
- An auto-trait parity test generates rustc probes for
  `Send`, `Sync`, `Unpin`, `UnwindSafe`, `RefUnwindSafe`,
  and `Copy` over the exposed std type list and compares
  them with lust answers.
- W-STD gates include both the manifest diff and the
  parity test (9.3).

Copy from real std where the code fits. Lust std is Rust
source, so for exact behaviors (RawVec growth, sort, fmt,
float text rules) copy the rust-lang/rust 1.99 source and
adapt it to the supported subset. A copy is more exact
than a rewrite in C, and the difftest then checks the
adaptation, not a new algorithm.

Std source must be valid Rust, like all lust programs.
Where real Rust std uses compiler internals lust lacks
(`#[rustc...]`, lang items), lust std writes the plain
equivalent. It does not need to compile under rustc as a
replacement std. It needs to behave the same through
its public API in programs lust accepts. Rule zero
compares program output, not std internals.

Lang items the compiler must know by def, looked up once
when the std crates load, by a `#[lust_lang = "..."]`
attribute in std source (unknown to rustc; std source is
never fed to rustc): `Option`, `Result`, `String`,
`Vec`, `Box`, `Rc`, `Arc`, `UnsafeCell`, `PhantomData`,
`Range` family, `Iterator`, `IntoIterator`, `Drop`,
`Deref`, `Fn` traits, `Sized`, `Send`, `Sync`, panic
entry points, `Formatter`, exchange malloc hooks. Keep
the list in one table in `src/ty/lang.rs`. A missing
lang item at std load is a compiler installation error,
not a user diagnostic.

### 3.2 What stays intrinsic

Intrinsics are the only compiler-known callables left.
They replace the `Builtin` enum with a small, stable set.
Do not freeze a count: width-specific atomics, sync ops,
and the hash, memchr, xxh3, ryu-js, and catch helpers pass
any fixed number. Freeze instead: each intrinsic has a
normal fn signature in `core::intrinsics`, a C symbol, a
privilege check (3.1), and a difftest. Most intrinsics are
plain foreign runtime calls. Codegen emits the C call
directly; there is
no IR node per intrinsic family beyond "call this
runtime symbol with this signature". Sized operations
take explicit size and align (the erased-core rule).

| Group | Intrinsics (C symbol) | Why not source |
|---|---|---|
| Memory | `alloc(size, align)`, `dealloc(ptr, size, align)`, `realloc(...)`, `alloc_zeroed` | Must call the process allocator (3.7). Align up to 4 MiB must work (`jemalloc_layout.rs:66` in ts-rust). |
| Bytes | `memcpy`, `memmove`, `memset`, `memcmp` (ptr, len forms) | One call each in C; source loops are slower and touch raw ptr rules everywhere. |
| Ptr | `ptr_read`, `ptr_write` (typed in std wrappers), `ptr_offset` | The typed API is source. The raw load/store is one intrinsic so borrowck has one unsafe boundary. |
| Float text | `fmt_f64`, `fmt_f32`, `parse_f64`, `parse_f32` | Shortest round-trip printing and correctly rounded parsing, byte-exact with Rust (3.5). C code, fuzz-verified. |
| Int text | none | Write in source over `String` push bytes. |
| Panic | `panic(payload_ptr, payload_vtable, loc)`, `panic_bounds`, `panic_str` helpers | Section 7. Location stays (slot, line, col) as today. |
| Thread | `thread_spawn`, `thread_join_raw`, `tls_key_create/get/set`, `park`, `unpark` | pthreads wrappers (7.3). Policy (poisoning, results) is source. |
| Sync cores | `mutex_lock/unlock`, `rwlock_*`, `condvar_*`, on opaque handles | pthread objects have no lust layout. Handles are boxed C structs. |
| Atomics | `atomic_load/store/xchg/cas/fetch_add/...` per width and ordering | C11 `stdatomic.h` through tcc mob (DESIGN evidence). Typed `AtomicU64` etc. are source wrappers. |
| Time | `clock_now_raw`, `system_time_raw` | `clock_gettime` values out. `Duration` math is source. |
| IO raw | `fd_read`, `fd_write`, `fd_close` plus errno fetch | Everything above byte IO on fds is source or shim (3.7). |
| Process | `args` raw table, `env_get` raw, `exit` | Set once at startup in the runtime unit. |
| Hash core | none | FxHash and SipHash are source. The table core is C (3.3), the hasher is not. |
| Arena | `arena_alloc(bytes, align) -> ptr` per arena handle | The leak arena bump core (3.6). Typed `alloc_with` is source in the adapter. |

Everything not in this table is source. In particular:
`Option` and `Result` methods (hundreds), iterator
adapters and consumers, `Vec` and `String` methods above
the erased cores, sort, `Rc`, `Weak`, `RefCell`, `Cell`,
`OnceCell`, `OnceLock`, `LazyLock`, `Cow`, `VecDeque`,
`BTreeMap`, `HashMap` typed layer, `fmt` machinery,
`Display`/`Debug` for all std types, `str` methods,
`char` methods, `Path`/`PathBuf`, `io::Read`/`Write`
adapters, `mpsc`, guards. If a proposed intrinsic is
not on the list, the default answer is source. Add to
the list only with a profile.

### 3.3 Erased container cores in C

Per VERIFY G section 4: containers are typed thin
wrappers in lust source over one erased C core per data
structure, keyed by element size and align plus a small
per-type glue table (hash, eq, drop, clone fn ptrs).
Measured cost is 0.8x to 1.4x of mono under tcc, and it
removes the largest instance class after iterators.
Today's `lust_Vec` is the prototype
(`src/runtime.c:19-22`, `lust_vec_push_slot` at
`src/runtime.c:213-216`). Generalize it:

```c
typedef struct { void *ptr; uint64_t len, cap; } lust_vec;
void  lust_vec_reserve(lust_vec *, uint64_t extra, uint64_t size, uint64_t align);
void *lust_vec_push_slot(lust_vec *, uint64_t size, uint64_t align);
// plus insert/remove/splice byte moves, drain, truncate-with-drop-callback

typedef struct lust_str { uint8_t *ptr; uint64_t len; } lust_str;      // exists
typedef struct { uint8_t *ptr; uint64_t len, cap; } lust_string_core;  // exists as lust_String

typedef struct lust_hashmap lust_hashmap;  // SwissTable-compatible, see 3.5
// ops take (map, hash, key_ptr, key_size, glue) and return slot ptrs

typedef struct lust_deque lust_deque;      // ring buffer over a lust_vec
```

Rules:

- The C core never knows Rust types. All typed access
  (indexing, iteration, entry API) is in the source
  wrapper, which computes byte offsets from `size`.
  Callers stay monomorphic and typed. The compiler
  needs no erased ABI for user types (VERIFY G).
- Drop and clone of elements go through glue fn ptrs
  from the per-type glue table mono emits (4.2). The
  Vec drop loop exists today as glue in
  `src/cgen.rs:1226-1269`; it moves behind the glue
  table.
- Growth must match Rust so `capacity()` matches
  (3.5). Fix `lust_vec_reserve`
  (`src/runtime.c:199-205`): today it starts at 4 for
  every element size. Rust 1.99 `RawVec` minimum capacity
  is: 8 elements when the element size is 1, 4 elements
  when the size is 2 to 1024, and 1 element above 1024.
  (`max(8 / size, 1)` is wrong: it gives 2 for 4-byte
  elements, where Rust gives 4. A probe on rustc 1.99
  prints capacity 4 for u32, u64, u128, and a 1024-byte
  element, 8 for u8, and 1 for a 1025-byte element.)
  Then capacity doubles on the amortized path.
  `reserve_exact` takes exactly the needed capacity, with
  no minimum and no doubling. A zero-sized element type
  never allocates and reports capacity `usize::MAX`.
  Copy the exact `RawVec` growth functions from the Rust
  1.99 source (amortized, exact, `reserve`, `shrink_to_fit`,
  `shrink_to`) into the core, driven by size, and
  difftest `capacity()` hard: duplicate growth sequences,
  ZSTs, exact vs amortized reserve, and shrink.
- `String` is `Vec<u8>` with UTF-8 checks in source.
  Keep the C string core for push bytes and case ops
  where they exist (`src/runtime.c:54-99`) but route
  new methods through the source wrapper. Do not grow
  the C string API method by method.
- Sorting: no C introsort. An introsort is not stable, so
  it cannot implement `sort` or `sort_by` at all, and its
  comparison sequence differs in every case. Port the
  Rust 1.99 sort source into lust std: driftsort for the
  stable `sort`/`sort_by`/`sort_by_key` family and ipnsort
  for the `sort_unstable` family. Equal elements keep
  their order under the stable sort; ts-rust depends on
  stable output (for example
  `execute/build/orchestrator.rs:286-288` and
  `checker/nodebuilder_impl_p2.rs:602-603`). Comparator
  call order, a comparator that is not a total order
  (Rust panics; ts-rust works around it at
  `gostd/slices.rs:1480`), and caught panics mid-sort are
  all observable, so the ported algorithm must match
  comparison for comparison. If a comparator panics, the
  slice stays in the same state the Rust algorithm
  leaves: a permutation, never a duplicate or a loss.
  Gate: difftests with duplicate keys, a comparator call
  log, a panicking comparator caught by `catch_unwind`,
  and a non-total-order comparator, against rustc in
  unwind mode (9.3 test runners).

### 3.4 Iterators in source, fusion in the compiler

Iterator adapters are ordinary generic structs in
`library/core` (`Map`, `Filter`, `Take`, `Zip`, and the
rest), with real `next` methods. Any crate can consume
them unfused through mono. Fusion (4.3) is an
optimization that pattern-matches known adapter defs.
This split matters: correctness never depends on the
fusion pattern list, and user iterators (ts-rust has 5
custom `Iterator`, 2 `DoubleEnded`, 4 `ExactSize`, 6
`IntoIterator` impls) work through the unfused path.

`size_hint`, `ExactSizeIterator`, and collect capacity
behavior live in the source impls and must match Rust
(VERIFY G section P4 gives the failure cases). The
fusion spec in 4.3 consumes these exact semantics.

Real std also changes output through specialization, which
plain generic source cannot express. Examples: `zip` with
two random-access sides pulls the long side only as far as
the short side; `into_iter().map(f).collect()` reuses the
allocation and keeps capacity 100; a trusted-length
`collect` or `extend` reserves a different capacity. The
unfused path must match rustc on all of these, or
`LUST_NO_FUSION=1` and the fused path disagree.

Std gets one narrow privilege for this (3.1 item 3): three
type predicates that mono evaluates as constants after
substitution, from a closed table of std defs:

- `intrinsics::is_trusted_random_access::<I>() -> bool`
- `intrinsics::is_trusted_len::<I>() -> bool`
- `intrinsics::in_place_collect::<Src, T>() -> bool`

Std source branches on them in `Zip::next`, in `collect`,
and in `extend`. The trait system does not change, and user
code cannot name the predicates. A new predicate needs a
difftest that shows observable divergence without it, plus
a line in this list. Gate: list each std specialization
that changes output (pull counts, capacity, drop order) in
the std source README, with one unfused difftest per item
in `tests/adapters/` (9.3).

`for` loops desugar in check to `IntoIterator::into_iter`
plus a `next` loop, or to a fused chain when 4.3
applies. Range types are std structs with `Iterator`
impls, with a fused fast path for integer ranges (307
ts-rust uses).

### 3.5 Byte-exact behavior

Rule zero compares stdout and exit status. DESIGN
excludes panic text, `HashMap` order, thread
interleaving, and `{:p}`. Ts-rust narrows those
exclusions: its baseline tests compare bytes, panic
text can become an IPC response (DESIGN-TS section 1),
and ordered-map output reaches JSON bytes. So be exact
where output can observe it:

- **Float printing and parsing.** Rust `Display` and
  `Debug` for `f64`/`f32` use shortest round-trip
  decimal. Implement one C implementation (Ryu for
  print, Eisel-Lemire with exact fallback for parse),
  then wrap with Rust's formatting rules (when to use
  exponent form in `Debug` vs `Display`, trailing
  `.0`, `inf`, `NaN` signs). Gate: a fuzz difftest over
  at least 10 million random bit patterns plus directed
  edges (subnormals, powers of 10, halfway cases),
  lust vs rustc output, both `Display` and `Debug`.
  Ts-rust JS numbers need a *different* printer
  (ECMAScript `Number::toString`, the `ryu-js` crate,
  1 call site): that is a separate C port in the deps
  layer (3.6), not a reuse of the Rust printer.
- **Formatting.** `format!` compiles to `fmt::Arguments`
  built from pieces, as in Rust. Today `FmtPart`
  (`src/ir.rs:66-71`) has only literal and arg with a
  debug flag. Extend to a parsed format spec: fill,
  align, sign, `#`, zero, width (literal, arg, `.*`),
  precision, radix (`x X e E o b p`), `?`. Parsing
  happens in the expander (builtin macro), specs become
  const data, rendering is std source (`Formatter`,
  `write!` to any `fmt::Write`). Ts-rust uses width or
  precision 40 times and radix 37. Implement the full
  spec grammar once; partial specs cause repeat work.
  `{:p}` prints a dev address; output that depends on
  it stays excluded by rule zero.
- **Constant addresses.** Equal constants share one
  address program-wide, keyed by rustc's rule for one
  codegen unit: equal bytes, uninit runs and pointer
  places, or equal bytes alone for a 4, 8, 16 or 32
  byte constant with no pointer (the linker's merge).
  Each promoted temp, byte string temp and str literal
  site interns its bytes at its first use and caches
  the address (runtime/kconst.c, cgen/kconst.rs); the
  glue unit registers the pointees of statics before
  main. Equality between fns is config-dependent in
  rustc (DESIGN, rule zero), so only same-fn
  comparisons are tested.
- **HashMap order.** Rust `HashMap` (SipHash, random
  seed) has no stable order; lust keeps a fixed seed
  and the corpus rule that map order must not reach
  output. `FxHashMap` is different: deterministic
  hash, and hashbrown's table gives a deterministic
  iteration order for a fixed insertion sequence.
  Where ts-rust output depends on it, lust must match.
  The byte streams that `Hash` writes are part of the
  contract too: `str` writes a trailing `0xff` byte,
  slices write a length prefix, and a derived enum writes
  its discriminant as `isize`. The hasher is source: FxHash
  as `rustc-hash 2.1.2` computes it, SipHash-1-3 for std
  maps with a fixed seed.
  Sequence the work. First, spike K4 audits whether
  ts-rust output depends on the order at all: build
  ts-rust with a perturbed FxHasher through `[patch]` and
  run the baseline tests. Equal bytes mean a deterministic
  table is enough for the port. Unequal bytes name the
  sites that need the exact table or a sort at the site.
  The exact table, when built, must pin: the hashbrown
  version inside the pinned Rust std (the `FxHashMap`
  oracle, since `rustc-hash` aliases std `HashMap`; the
  external `hashbrown` in `Cargo.lock` is the `IndexMap`
  oracle and can differ), bucket growth (power of two,
  87.5% load via growth-left), element layout, growth,
  reserve and shrink, removal and tombstones, rehash, and
  scan order. Group width is part of the probe sequence,
  not a free choice: hashbrown adds `Group::WIDTH` to the
  probe stride, 16 bytes on x86_64 (SSE2) and 8 bytes on
  aarch64 (NEON), so one fixed-width table cannot match
  both tier 1 targets. Until the exact gate passes for a
  target, the adapter README must state that Fx map
  iteration order is not yet a supported observable on
  that target, and the port proceeds only under the K4
  audit result. Never silently diverge.
- **`type_name`.** `std::any::type_name::<T>()` reaches
  output: ts-rust parses it into error text at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json_ext.rs:647`.
  Mono generates the string for each concrete type with
  real path spelling: crate name, module path, item name,
  and generic args as rustc prints them, for std types and
  user types alike. Gate: difftest `type_name` output for
  the std types ts-rust names plus nested generic user
  types.
- **IndexMap order.** Insertion order by definition;
  `shift_remove` vs `swap_remove` differ and both are
  observable. The adapter (3.6) implements entries in a
  `Vec` plus a `lust_hashmap` from key hash to entry
  index. Iteration walks the Vec. Entry order is then
  exact by construction. JSON output at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json.rs:1643`
  (cited in DESIGN-TS section 4) is the acceptance
  shape.
- **Vec capacity.** Copy `RawVec` growth (3.3).
  `collect` uses `size_hint` lower bounds and the trusted
  length paths only through the predicates in 3.4.
  Difftest `capacity()`
  after map/filter/collect chains (VERIFY G P4 lists
  the traps: `Vec<u8>` through filter gives 8, 34 kept
  items give 64) and after in-place collect and trusted
  `extend`.
- **Panic messages from std.** Copy the Rust 1.99 texts
  verbatim for every std panic lust can raise: unwrap
  on `None`, expect messages, index out of bounds
  (today at `src/runtime.c:220-225`), slice index,
  `RefCell` double borrow, channel closed, poisoned
  lock, parse errors. Locations: `#[track_caller]` is
  real. A `track_caller` fn receives a hidden
  `&Location` param, added at mono. Codegen passes the
  caller's (slot, line, col). Nested `track_caller`
  forwards. Without it, an `unwrap` in std source
  would report a `library/` line; rustc reports the
  user line. Ts-rust has 16 `track_caller` uses and
  the `GoThread` spawn path depends on caller location
  for fatal messages
  (`crates/ts_goport/src/gopanic.rs:249`).
  Two more payload facts are observable: the payload type
  of `panic!("{}", x)` follows `Arguments::as_str()`, so a
  literal-only message is a `&'static str` payload and a
  formatted one is a `String` payload, including rustc's
  inlining of literal args; ts-rust downcasts payloads.
  And `Location::file()` is the path Cargo gives rustc:
  workspace-relative for members, never an absolute lust
  path. The line numbers in cached code follow the
  remapping rule in 4.2. Measured location rules (W-PANIC):
  the column is rustc's display column (a tab counts 4, a
  wide char 2, per-char widths measured from rustc 1.99 in
  `src/colwidth.rs`); a panic in tokens a `macro_rules!`
  body wrote reports at the outermost macro call; a std
  panic without `track_caller` (`step_by(0)`, `Ord::clamp`,
  `sum` overflow, capacity overflow) reports std's own
  `library/` line. A stack overflow prints Rust's guard-page
  text and aborts. An `assert!` condition text of more
  than 78 bytes breaks over lines as rustc's pretty printer
  breaks it (`src/expand/assert_msg.rs` ports pp.rs and the
  boxes pprust opens); a form it does not model, such as an
  item in a block, is L0809.
- **Drop order.** Already a rule-zero requirement and
  tested today with printing `Drop` impls. Std source
  must not reorder drops: `Vec` drops elements front
  to back, scope drops run in reverse declaration
  order, temporaries drop at Rust's points. Lowering
  follows rustc's MIR building: temporary lifetime
  extension by rustc's `record_rvalue_scope` rules (the
  operand of an extending borrow in a `let` initializer,
  found through struct, tuple, array, and cast operands,
  resolved-path constructor arguments, block tails, and
  `if`/`match` arms; a `ref` pattern extends the whole
  initializer); a temporary drops before its own
  expression's temporaries; destructuring leftovers drop
  at the end of the `let`; an expression statement's
  value is a statement temporary; a `match` scrutinee's
  temporaries live to the end of the statement; each
  `&&`/`||` operand is a terminating scope. Early-exit
  paths (`?`, `collect::<Result>` short-circuit) drop
  in Rust order (VERIFY G P4: closure captures drop
  before partial Vec elements). Edition 2024 has three
  drop-related rules that change output and need tests of
  their own: the `if let` scrutinee drop scope, the
  tail-expression temporary scope, and never-type
  fallback to `!`. Lowering implements the 2024 forms
  only; a 2021 crate fails at session start (1.1).

### 3.6 Adapter crates (dependency layer)

Adapters are normal lust crates in `library/deps/`,
each with the dependency's crate name and public API.
The driver swaps them in by resolved package id (1.1).
Each adapter declares the exact upstream version it
matches in its manifest comment and a `lust-adapter`
version the driver checks. An upstream version bump in
a user's `Cargo.lock` with no matching adapter is a
clear error, not a silent mismatch.

| Adapter | Implementation | Exactness gate |
|---|---|---|
| `rustc-hash` | Type aliases over lust `HashMap` with the Fx hasher in source. The upstream crate is already only aliases plus the hasher. | Hash values vs 2.1.2 on byte slices, ints, strings. Table order gate from 3.5. |
| `indexmap` | `Vec<(K, V)>` plus `lust_hashmap` side index. `IndexSet` likewise. Entry API, `shift_*`/`swap_*`, `sort_by`, slicing. | Order and capacity difftests vs 2.14.0. |
| `smallvec` | Keep the real public shape: `SmallVec<A>` where `A: Array`, so callers write `SmallVec<[TypeId; 16]>` (ts-rust `checker/types.rs:273`), not `SmallVec<T, N>`. The adapter defines the `Array` trait with its associated `Item` and storage, as upstream does. Inline storage is `[MaybeUninit<A::Item>; N]` plus spill to the Vec core. `MaybeUninit<T>` is the one union-shaped type the layout engine supports (4.4); general unions stay rejected. An alias to `Vec` is not equivalent: `capacity`, the spill point, `size_of`, and drop behavior on spill all differ. | Layout, capacity, spill, and drop difftests vs 1.15.1. |
| `memchr` | Source wrappers over libc `memchr`/`memrchr`/`memmem` via one intrinsic each. Finder types in source. | Byte-search difftests on random buffers. |
| `bumpalo` (subset) | Leak arena over `arena_alloc`. Only the API `leak_arena.rs` uses: `Bump::new`, fixed chunk limit, `try_alloc_with`, slice copy. | Alignment, failure-on-full, no-drop semantics vs the ts-rust usage at `crates/ts_goport/src/leak_arena.rs:40-80`. |
| `xxhash-rust` (xxh3) | C xxhash in the runtime, thin source API. 128-bit results as `u128`. | Digests vs upstream test vectors. |
| `ryu-js` | C port of the JS number printer. | Byte compare vs the crate on random f64 bits. |
| `num-bigint` (subset) | Small source BigInt: parse, print, the ops ts-rust calls (5 refs). | Parse/print roundtrip difftests. |

Adapter code is user-level lust. It goes through the
same check and mono as any crate. It may use
intrinsics only where the table says (memchr, arena,
xxh3, ryu-js cores).

### 3.7 Shim crates and the allocator

Shims cover coarse OS and data services: `rustix`,
`nix`, `signal-hook`, `flate2` (zlib), `jiff` (local
time), `name-to-handle-at`, jemalloc control. One Rust
crate in `shims/` in the lust repo builds all of them
into one `cdylib` (a dylib on macOS)
with `extern "C"` exports. Cargo builds it once during
`lust port prepare`, keyed by lockfile, features,
target, toolchain, and shim ABI version (DESIGN-TS
section 4).

Link rule, from a probe on the pinned tcc: a Rust
staticlib whose export catches its own panic with
`catch_unwind` links through tcc (after adding
`-lgcc_s`) but aborts at run time with "thread panicked
while processing panic". The same objects linked with
the system `cc` run and print the caught result. So the
tcc linker is not a supported final link for Rust shims.
The first supported path is: build the shim as a cdylib
with Cargo, and link or load it with the system linker
or loader, as lust already loads `libbase.so`. A daemon
build that uses a shim either links the final binary
with the system linker or loads the cdylib at startup.
Staticlib linking through libtcc becomes an option only
after spike K6 passes the semantic test (a recovered
panic inside the shim, TLS, threads, callbacks, and
allocator ownership) through the libtcc API itself, on
both tier 1 targets. Link success alone does not count. Lust-side, each shim has a lust source
crate with the public API whose bodies call the C
exports through `extern "C"` foreign fns (checker
support for foreign fns under opt-in `unsafe`).

Boundary rules (from DESIGN-TS section 4, made
concrete):

- Only scalars, byte buffers (ptr plus len), C-layout
  records (`#[repr(C)]` of scalars), and opaque handles
  (u64) cross. Never `String`, `Vec<T>`, closures, or
  trait objects by layout.
- Ownership: inputs are borrowed for the call. Outputs
  are copy-out buffers with an explicit free fn, or
  caller-provided buffers. One allocator owns each
  buffer: shim-allocated memory is freed only by the
  shim.
- Callbacks: fn ptr plus env handle plus a status
  return. A panic in a lust callback stores an in-flight
  exception in thread state (7.2) and returns the panic
  status at once; the shim must not call back again
  after a panic status, and the lust side resumes the
  unwind when control returns to lust code.
- The shim catches its own Rust panics and returns a
  status plus message. A panic must never unwind
  through lust C frames.

Allocator: dev builds link mimalloc by default, as the
compiler itself does (`src/main.rs:26-27`), through the
`alloc` intrinsic. If the crate records a
`#[global_allocator]`, dev honors it only for known
allocators: jemalloc (link the shim's jemalloc and
route `alloc` to it) or the system allocator. Ts-rust
needs jemalloc arena control
(`crates/ts_goport/src/jemalloc_layout.rs:66-99`): the
`tikv-jemalloc-ctl` surface is a shim, and thread arena
assignment must be real, not a no-op, because the
single-threaded checker allocates in the loader's
arena. 4 MiB alignment from the same file must hold in
the dev allocator or ts-rust's layout guard aborts.

### 3.8 How std gets built and cached

A signature-only cache cannot serve a new generic use:
after a restart, `Vec<MyType>` needs the generic body of
each method it calls, not only a signature and a
prebuilt object. So the std cache stores three things
per (lust version, target, profile) tuple:

1. The signature surface: defs, generics, param envs, and
   the impl and method indexes, in disk form (8.4).
2. Generic templates: the checked generic IR of every
   generic fn, method, and impl in `core`, `alloc`,
   `std`, and the requested adapters, in a std-only
   versioned format with owned type stores (2.1). Std
   cannot change inside one lust version, so this format
   does not freeze the user `Checked` format.
3. Prebuilt instances for the non-generic items: C and
   objects, as section 8 defines.

"Compile std once" means: run the normal pipeline over
the shipped crates with no `main`, with every `pub` item
as a signature root (not as a codegen root; a pub generic
fn has no single instance to build). A cold session loads
items 1 and 2. A user-specific std instance then goes
through the ordinary mono and instance cache. The
fallback is to parse and check the shipped templates on
load; W-DRIVER measures both paths at its gate and keeps
the serialized path only if it wins. The artifacts are
versioned with the compiler; a mismatch rebuilds.

Std is immutable inside a daemon session. Editing
`library/` source requires a new lust version string
in dev (use the git hash of the lust repo) or an
explicit `LUST_STD_SRC` (or `LUST_LIBRARY`) override.
That override exists for the agents who build std
(package W-STD, section 9). Under it every compile is
cold and uncached: the client uses no daemon, a daemon
refuses to start, and the disk cache is off
(`protocol::source_override`), because neither a
session nor the cache key can see edits to that tree.

## 4. Monomorphization and codegen

### 4.1 Pipeline change: generic bodies, then instances

Today: collect, then per fn check (`src/check.rs:215`)
and lower (`src/lower.rs:28`) to IR, borrowck on IR,
cgen per fn. New pipeline per crate:

```text
expand + resolve + collect      (signatures, impl index)
check generic body per fn       (parallel; Param and Projection types stay)
lower to generic IR per fn      (parallel)
borrowck on generic IR          (parallel; section 5)
mono: walk instances from roots (substitute, normalize, resolve calls)
cgen per instance               (parallel, by slot unit)
tcc per unit, link              (as today)
```

Check and borrowck run once per *template*, not per
instance. That is a deliberate difference from rustc,
which re-elaborates per instance in codegen. Soundness
argument: the generic body checks against its declared
bounds (param env). Any concrete args that satisfy the
bounds, proven at the call site, keep every call and
loan in the body valid. Two instance-dependent checks
still run at mono and can error, matching rustc's
post-mono errors: the recursion limit (VERIFY G P3)
and inline const evaluation after substitution (2.13).
A build must walk all reachable instances even where
codegen could skip one, or those errors diverge from
`rustc build`.

`lust check` does not walk instances. It stops after
generic check and borrowck, like `rustc check`, which
accepts a recursive instantiation that `rustc build`
later rejects. Tests must state which mode they pin: a
recursion case is a build reject, not a check reject.
Do not pay the instance walk in the edit loop only to
mimic a build error.

Between check and mono, lowering lifts body-local types
into the crate owned store (2.1). Mono, caching, and
cross-crate reads only ever see lifted results. Static
initializers are data, not instances (2.13).

Generic IR keeps trait method calls as
`CallTrait { trait_def, method, self_ty, args,
evidence }` where evidence is `Param(index)` for a
param-env bound or `Impl(ImplId)` already selected.
Mono resolves `Param` evidence by running selection
(2.4 step 3) on the concrete self type. If selection
at mono fails for args that passed check, that is a
compiler bug. Keep a debug assertion and a user error,
not a panic.

### 4.2 Instance keys, sharing, and the daemon cache

Discovery key (correctness):

```rust
pub struct InstanceKey {
    pub def: DefId,          // fn, method, closure, or static initializer
    pub args: ArgsId,        // type and const args only; regions erased
}
```

Regions never enter the key. They do not affect code.
Recursion detection uses the discovery stack of
`InstanceKey`s; cap depth at 128 like rustc, error on
exceed with the instantiation chain printed (must
match rustc's error class so `tests/fail` agrees).
Also cap total instances per crate (default 2,000,000,
flag-tunable) and per-template fan-out, with an error
that names the worst template. These caps stop hangs;
they are not language limits.

Roots: `main`, `#[test]` fns in test crates, exported
`extern "C"` fns, vtable method sets for every
`dyn` coercion site reached, and drop glue for every
concrete droppable type reached. Static initializers
are data (2.13), not roots. Non-generic fns are
instances with empty args. Dead generic fns produce
no instance and no C.

No instance sharing in milestones 4 to 8. The key from
revision 1 (layout class per type arg plus the set of
trait callees) is not a correctness proof: it ignores
field offsets, type-dependent constants, `size_of`,
`TypeId::of`, and `type_name` inside the body, the order
of calls, and the C calling convention (`f64` and `u64`
share a layout class and differ in registers). VERIFY G
also puts the gain under 10%. So v1 emits one C function
per discovery instance and keeps the erased container
cores (3.3), which remove the largest instance class by
a sound route. Milestone 9 may add sharing only with a
proof per shared group: the normalized concrete IR and
the C ABI signature must be equal, or the template must
be in a restricted class with its own proof. Measure
emitted instance bytes and rebuild bytes first. A 30%
byte share alone does not prove a compile-time problem.

Each instance caches its resolved edge list (callee
instance keys) with the reads that produced it. On an
edit, mono recomputes edges only for dirty instances and
walks from them (8.3). A full walk over a few hundred
thousand instances and a few million edges would eat the
edit budget by itself, so the walk is incremental from
the first version, not a later fix. Record the real
reachable instance count and the cached-walk time at the
wave B scale gate (9.3). Density estimates from VERIFY G
(0.56 to 0.80 instances per line) are a budget check, not
a prediction.

Glue per concrete type (drop, clone, eq, hash, debug
where derived or std-known) becomes instances too,
keyed by `(GlueKind, Ty)`, replacing today's per-`CTy`
glue (`src/cgen.rs:30-36`, `GlueSet` at
`src/cgen.rs:980-1054`). The per-type glue *table*
for erased cores (3.3) is a static struct of fn ptrs
to those instances' slots, emitted once per type that
reaches a container core.

Slots and cached code. There is one slot space per final
binary (1.7), assigned by W-DRIVER when it plans the link.
Generated C contains numeric slot references, so slot
assignment is part of code identity:

- Per-instance C text is cached in two layers. The mono
  IR of an instance is keyed by its instance fingerprint
  (template body, arg fingerprints, selected impls on its
  edges). The C text for a unit also depends on slot
  numbers, because call sites print them. But it depends
  only on the slots its own emitted code uses: the
  unit's key includes a *used-slots hash*, the hash of
  the `(InstanceKeyHash, slot)` pairs for every slot the
  unit's C references, its callee slots, its own
  instances' slots, and any table or trampoline it
  names. The whole-manifest hash is *not* in the key.
  Slot assignment is append-only (below), so adding one
  new reachable instance changes no old pair: every
  unrelated unit keeps its key and its cached object is
  reused. Keying on the whole manifest instead would
  reject every object on each new slot and break the
  small-edit rule of 8.3 step 6. When a unit's own used
  pairs change (a base rebuild renumbers, say), re-emit
  its C from cached mono IR; do not reuse its object.
- The one unit that does depend on the whole table is
  the table unit: it emits the `lust_fns` array and the
  slot trampolines (4.5). Its key is the full manifest
  hash, and it rebuilds whenever the table grows. It is
  small and holds no user code.
- C-unit objects and per-instance C are separate cache
  entries (8.4). The backend compiles groups of instances
  into units. The disk object key is the unit's full C
  text (plus compiler id and debug flag): the used-slots
  rule above decides when C is re-emitted, and an
  unrelated unit's C does not change, so its object is
  still reused. A key on instance fingerprints plus the
  used-slots hash served stale objects when cgen printed
  a slot the used list missed (fx-unitcache).
- Gate for this rule: add one reachable generic
  instance to a built fixture and show that the objects
  of unrelated units are reused (same keys, no
  recompiles), while the table unit rebuilds. W-DRIVER
  owns the test (9.3).
- Slot assignment is append-only per bin session, as
  today (`src/driver.rs:317-336`). Unreachable instances
  leave dead slots until the next base rebuild (32
  overlays today; keep the policy). A restarted daemon
  loads the stored manifest so slots stay stable across
  restarts, in any crate load order or instance discovery
  order. A restart test in 9.3 proves it.

Release C (`LUST_RELEASE_C=1`, one-shot builds; cgen/names.rs,
driver/release_c.rs). A release build has no session to keep
slots in, so its C must not name slots at all: then a
content-keyed object cache (key = unit C text, C compiler,
flags, target) reuses every unit a commit did not touch,
across commits, machines and CI runs. Fn bodies are extern
`f_<hash of DiskDefId>` called directly through prototypes,
Adts are `A<def hash>` or `A<instance key hash>`, vtables and
per-fn helpers count from 0 in their fn, and a panic location
reads its slot from the location unit (`lust_so_<id>`). Units
follow each fn's own identity: its source file (an instance:
its generic fn's), fns in source order, content-defined cuts
(`LUST_RELEASE_UNIT_KB`, default 128). Glue lives in
content-defined shards (fn units keep prototypes), statics in
one data unit, and a fn unit defines only the types it holds by
value: a type it only points at is forward-declared. The daemon
and dev builds keep the numbered scheme (overlays need the
table). Measured on the 12 ts-rust v0.6->v0.7 merges: see
rel-cache's REPORT.md.

LLVM backend for release C (`LUST_RELEASE_BACKEND=llvm`, with
`LUST_RELEASE_C=1` and unwind tables or panic=abort;
cgen/ll.rs). Each fn body becomes an LLVM IR fn `fl_<id>`:
an alloca per local and flag, native control flow, unwinding
as invoke/landingpad (the runtime's C++ throw and catch are
unchanged), an internal ABI (small aggregates in registers),
simple statements in IR and the rest as always_inline C
helpers cut from cgen's own statement C. A unit is three
texts (`u<N>.ll`, its helpers' C `u<N>.hc`, its C wrappers
`u<N>`) that cc.rs compiles as one module and keys as one.
`LUST_LL_INLINE=<cost>` (default 25, three levels) adds
`available_externally` copies of small callees from other units;
with a profile, only of callees it ran at least
`LUST_LL_COPY_MIN` times (default 100000): a cold copy is not
inlined and recompiles its unit with every change to the callee.
C calls an LLVM fn through its C ABI wrapper `f_<id>`; a unit
keeps the external wrapper (and the trampoline `tramp_<id>`)
only when some C text names it, and a C text that calls it gets
the wrapper as a C99 inline definition, so the call goes straight
to `fl_<id>` (`cgen::ll::CRefs`, `cgen::ll::Adapters`). `LUST_LL_RTINL=<n>`
(off by default) compiles the runtime unit through IR and links
an `available_externally` copy of its fns of up to n
instructions into each LLVM unit (cc/rtinl.rs). Tests: difftest LL=1,
and CC_DRIVER=1 with LUST_RELEASE_C=1; numbers in rel-llvm's
REPORT.md.

Locations and span remapping. Panic locations,
`track_caller` locations, and cached diagnostics are
position-dependent. A token hash that ignores whitespace
calls a body unchanged after a blank line is added inside
it, and a function-relative line number only fixes moves
of the whole function. Rule: stored results keep
locations as (item def, token ordinal inside the item).
The line and column are resolved from the current file's
token spans at print or emit time. C text that embeds
line numbers also keys on the line-index hash of its
source file. Expansion tokens carry their `CtxtId`;
their disk form is the expansion's source hash chain
(8.4), so a macro edit remaps them, by the same rule.

### 4.3 Iterator fusion with an unfused fallback

Start unfused. The first version ships ordinary source
`next` semantics with fusion off for every adapter. Fusion
then turns on per adapter chain, under the dual-run gate
below, in this order: proved single-adapter chains over
slice and range sources first (`map`, `filter`, `copied`,
`enumerate`, `take`), then the rest. `zip`, nested
`flatten`, and reverse pulls (`rev`, `next_back`) stay on
the source path until their own gates pass.

Recognition has one boundary, stated here so lowering and
mono do not each invent one. Lowering records a candidate
chain on the generic IR by std def ids. At mono, with
concrete types (and after an opaque type is substituted),
the fusion pass checks eligibility: chain shape, source
kind, and the specialization predicates of 3.4 for the
whole chain. If any fact is not proved, the instance uses
the unfused path. Fusion recognizes, when eligible:

- Source: `.iter()`, `.iter_mut()`, `.into_iter()` on
  `Vec` and slices and arrays, `str::chars` and
  `bytes`, ranges, `once`, `empty`, and std adapters
  by def: `map, filter, filter_map, copied, cloned,
  enumerate, take, skip, zip, chain, flatten (one
  level), flat_map, step_by, rev` on double-ended
  sources, `inspect`.
- Sink: `for` loop, `collect` to `Vec`/`String`/
  `HashMap`/`HashSet`/`Result<_, _>` of those,
  `for_each`, `fold`, `sum`, `count`, `any`, `all`,
  `find`, `position`, `min`, `max`, `next` chains in
  `while let`.
- The chain must be linear, single-use, not stored,
  not passed to a fn, not behind `dyn`, and every
  closure must be a local closure value (not a fn ptr
  variable that could be reassigned; fn *items* are
  fine). Else: unfused path. No diagnostic. Fusion is
  invisible.

Fused form: one loop over an index or pointer, with a
written spec. The spec is the contract; an
implementation that does not meet it is wrong even if
simple tests pass. From VERIFY G P4, the spec must
state:

- Pull order is demand-driven per `next` call. `take(n)`
  tests its count *before* pulling. `skip(n)` pulls and
  drops the skipped items, so `map(f).skip(2).next()`
  runs `f` 3 times. `step_by(k)` pulls the items it steps
  over (a 4-item source with `step_by(2).count()` runs a
  `map` closure 4 times; in general every source item up
  to the last yielded one is pulled). Never skip a pull
  because its value is unused.
- `zip` pulls left, then right, once per output. The one
  exception is Rust's random-access path, and it needs
  *both* sides to be trusted random access for the whole
  adapter chain on each side, by the 3.4 predicate. Then
  the long side is pulled only as far as the short side.
  The right side alone proves nothing: with `filter` on
  the left and a slice on the right, rustc runs the map
  closure 3 times for a 2-item output, and a
  minimum-length loop would run it 2 times and change
  output. The unfused std `Zip` makes the same decision
  through the same predicate, so both paths agree. The
  side-effect count in user closures is observable.
- `collect` capacity: pre-size from the chain's
  `size_hint` exactly as the source impls compute it
  (map preserves, filter gives (0, upper) so collect
  uses the lower bound path Rust uses). Then grow by
  the Vec rule. `capacity()` after a fused collect
  must equal the unfused value.
- Early exit (`?` in a closure, `break`, `find` hit,
  `collect::<Result>` on `Err`): drop order is
  closures first (captures), then already-collected
  elements in order, then the source if owned. Build
  the fused loop's exit edges to match the unfused
  drop tree. This is the most error-prone rule;
  difftest it per adapter.
- Panic in a closure mid-chain: elements already
  produced and owned by the sink drop on unwind
  (section 7). Elements borrowed from the source do
  not.

Gate (VERIFY G section 5): 150 or more difftest cases
with side-effect counters, `Drop` impls that print,
`capacity()` prints, and early exits, run fused vs
rustc. Keep an env flag `LUST_NO_FUSION=1` that forces
the unfused path; CI runs the iterator corpus both
ways and diffs the outputs. A fusion bug then has an
instant bisect.

Estimated share: VERIFY G measures real code at 15 to
18 iterator instances per chain, 1 chain per 58 to
137 lines, fusion removing most of 23 to 35% of -O0
code bytes. Ts-rust: 3,516 chains (2,644 with one
adapter, 205 with 2 or more), top adapters map 1,087,
copied 405, cloned 350, enumerate 336, take 250,
filter 247. Single-adapter chains dominate, so v1
fusion quality on short chains matters more than
deep-chain cleverness.

### 4.4 Layout

Layout is observable in safe Rust. `size_of`, `align_of`,
and `offset_of!` can print, and a const assert on a size
is a compile error when the size differs. So layout is a
strict contract, not a performance choice:

- For every type lust accepts, `size_of` and `align_of`
  equal rustc 1.99 on the same target. The algorithm
  below exists to meet that rule. A shape where the
  algorithm cannot prove a match is rejected, not
  accepted with a different size.
- `offset_of!` must also match where it is allowed. Rust
  does not promise field offsets for default-repr types,
  but a program can still print them, so lust rejects
  `offset_of!` on a default-repr type with `L0650`. On
  `repr(C)`, `repr(packed)`, and `repr(transparent)`
  types, offsets follow the stated rules and match.
  Ts-rust uses `offset_of!` only on `repr(C)` types.
- A scan for size asserts is not permission to diverge.
  It finds asserts; it cannot find a size printed at run
  time. No "release-only assert" rewrite changes this,
  because the assert is also a compile-time check in
  dev: a wrong size makes the port fail to build.
  Ts-rust has more than 20 such asserts on default-repr
  types (`TypeMapper == 16`, `NodeList == 16`,
  `Symbol == 56`, and more). They are build blockers,
  not performance guards.

One layout engine in `src/ty/layout.rs`:
`layout(ty) -> Layout { size, align, field_offsets,
enum_tag, niche }` for sized types, memoized per `Ty`.
Pointer width from the target table (1.6). Rules:

- Scalars: C sizes. `bool` 1 byte (values 0 and 1
  only; codegen must never produce other bytes in a
  bool slot). `char` 4 bytes. `u128/i128` 16 bytes,
  align 16 on both tier 1 targets. The pinned tcc does
  not parse `__int128` (K3, section 10), so codegen
  uses a 2-word struct with an explicit 16-byte
  alignment attribute and runtime helpers for
  arithmetic beyond add and compare. Ts-rust needs
  `u128` only for xxh3_128 values (54 uses):
  construction, compare, hash, print. Helpers cover
  that. Where a C struct field needs align 16, the
  emitter pads explicitly (the `repr(C)` rule below),
  so `size_of` and field offsets hold in C too.
- Niches. Each layout reports at most one niche: a
  scalar range inside the type that can hold tag values
  for an outer enum, as (offset, scalar, free value
  count). Sources: a non-null pointer scalar
  (`&T`, `&mut T`, `Box<T>`, `Rc<T>`, `Arc<T>`, fn ptr,
  `NonNull`), `NonZero*`, `bool` (values 2 to 255 free),
  `char` (values above `0x10FFFF` and the surrogate
  range free), and an enum tag scalar whose discriminant
  range leaves free values, including a `repr(u64)` enum
  with few variants. A struct or tuple takes the niche
  with the *most free values* among its fields, at that
  field's offset; on a tie, the first such field in
  layout order. First-in-order alone is wrong:
  `Payload { pointer: &'static u8, flag: bool }` must
  report the `bool` niche (254 values), not the pointer
  niche (1 value), or an enum with a `Data(Payload)`
  variant and two empty variants needs a separate tag
  and takes 24 bytes where rustc takes 16. This is the
  mechanism ts-rust relies on: `TypeData` is a
  default-repr enum whose tag lives in the free values
  of a `GenericArgumentsMemo` field, a `repr(u64)` enum
  (see
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/checker/types.rs:2098-2105`).
- Enums. An explicit repr that fixes the tag or the
  field order (`repr(int)`, `repr(C)`, `repr(packed)`)
  turns the niche-filled candidate off: the tag is
  explicit even when a payload has a niche.
  `#[repr(u8)] enum E { Pointer(&'static u8), Empty }`
  is 16 bytes in rustc, not 8. `repr(align(n))` alone
  does not fix the tag and does not turn the candidate
  off. Without such a repr, two candidate layouts:
  (a) Niche-filled. Take the largest data-carrying
  variant, laid out as a plain struct, as the niche
  variant. The candidate exists only when its niche has
  at least as many free values as there are other
  variants, *and* every other variant's fields fit in
  the niche variant's layout in the bytes outside the
  niche scalar, at their own alignments, without
  growing the size. The fit check is not optional:
  `enum E { Pointer(&'static u8), Byte(u8) }` is 16
  bytes in rustc, because the `u8` payload has nowhere
  to sit inside the 8-byte pointer word. The tag values
  for the other variants come out of the niche; the
  enum reports the niche values that remain. `Option<&T>`,
  `Option<bool>` (1 byte), and the `TypeData` shape all
  come from this rule.
  (b) Tagged. Lay out *each variant as a struct that
  starts with the tag*: the tag first, then that
  variant's other fields, smallest alignment first,
  ties in declaration order. This is rustc's order, and
  it is not the plain struct order below: `enum E {
  A(u8, u32), B }` is 8 bytes (tag, `u8`, padding,
  `u32`), a `TypeMapper`-like enum with an
  `Array(Box<_>, bool)` variant is 16 (tag, `bool`,
  padding, `Box`), and a variant `(u16, [u8; 3])` gives
  a 6-byte enum. Tag-first with largest alignment first
  gives 12, 24, and 8 for the same shapes. Enum size
  is the largest variant struct, rounded up to the
  enum alignment, which is the largest variant
  alignment. Tag width comes from the discriminant
  range, not the variant count: the smallest of 1, 2,
  4, 8, 16 bytes whose signed or unsigned range holds
  every explicit discriminant (46 prod plus 351
  generated in ts-rust). `enum E { A = 1000, B }` is 2
  bytes and `E::A as i32` is 1000; a 1-byte tag cannot
  hold it. Then widen the tag into padding: when every
  variant leaves a gap between the tag and its first
  field (or has no field), the tag scalar grows to the
  largest width that fits the smallest such gap. Size
  does not change; the free values in the enum's own
  niche do. `enum E { A(u32), B(u32) }` gets a 4-byte
  tag this way, so nested `Option`s over it stay at 8
  bytes. A `repr(int)` attribute fixes the tag type,
  its width, and its signedness, and skips the
  widening; discriminants outside its range are an
  error, as in Rust. Fieldless enums are just the tag.
  Choice between the candidates, in order: the smaller
  size wins; on equal size, the layout whose resulting
  niche has more free values wins; if still equal,
  take the tagged layout.
- `repr(Rust)` structs and tuples (plain structs only;
  enum variant payloads follow the enum rules above):
  order fields to shrink padding, in a fixed order: by
  alignment, largest first; among equal alignments, by
  size, largest first; then by declaration order.
  Struct align is the max field align, size rounds up.
  Codegen uses these offsets for every field access, so
  the order is internal; only `size_of` and `align_of`
  (and nesting sizes) observe it. `struct S { a: u8,
  b: u64, c: u8 }` is 16 bytes under this rule, as in
  rustc; declaration order would give 24. Closure env
  structs are plain structs under this rule (4.5).
- `repr(C)`: exact C layout, declaration order. The C
  emitter writes explicit padding fields from the
  layout engine's offsets, so the C struct's layout
  equals lust layout regardless of the C compiler's
  choices. Enums with `repr(C)`: tag per C (`int`-sized
  unless a repr int is given), payload union. A
  `repr(C)` type that contains a default-repr enum field
  still needs that field's enum layout from the rules
  above; `repr(C)` on the outer type does not fix a
  nested enum. Ts-rust: `repr(C)` 6, `repr(u8)` 6,
  align 3, packed 1, transparent 1.
- `repr(transparent)`: layout of the one non-ZST
  field. Check the one-field rule at collect.
- `repr(align(n))`: raise align. Combined with C as
  in `#[repr(C, align(64))]` on
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/checker/types.rs:853-870`,
  where `size_of::<Type>() <= 128`,
  `offset_of!(Type, data) == 24`, and
  `size_of::<TypeData>() == size_of::<TypeReference>()`
  are const-asserted. The first two follow from the C
  rules. The third needs the nested `TypeData` enum to
  niche-fill its tag; with an 8-byte separate tag,
  `TypeData` grows and `Type` no longer fits 128 bytes.
  The layout gate includes this real nested shape, with
  the real field types, not a simplified stand-in.
- `repr(packed)`: align 1, no padding. Field access by
  value goes through unaligned loads in C (memcpy).
  Taking a reference to a packed field is an error, as
  in Rust (E0793): `L0651` at the borrow, in check.
  `repr(packed(N))` for N other than 1: reject until a
  user appears. One packed use in ts-rust.
- `MaybeUninit<T>`: size and align of `T`, no niche. It
  is the one union-shaped type in the contract (std and
  the smallvec adapter need it). User unions: reject
  `L0652`. `repr(simd)`: reject.

Supported shapes, as an enforceable rule. The engine
computes a layout only for types in this grammar:
scalars; refs, raw pointers, and fn pointers; tuples;
arrays; the fat-pointer forms (slice, `str`, `dyn`);
closure env structs and `MaybeUninit<T>` over a
supported `T`; and Adts whose repr is one of the forms
above (default, `C`, `transparent`, `align`, `packed`
with no `N` or `N` = 1, an int repr, or a combination
rustc accepts of those) and whose field and variant
payload types are themselves in the grammar. `layout()`
returns a result, not a guess: a type outside the
grammar is `L0652` at the Adt def (collect) or at the
use, never a best-effort size. The gate below enumerates
the grammar, so the rule and the test grow together: a
new type form enters only when the grammar, the
generator, and the engine all gain it in the same
change, and the extended gate is green. A shape inside
the grammar where the gate shows the engine diverging
from rustc is a layout bug; until it is fixed, that
grammar production is cut back to `L0652` rather than
shipped with a wrong size.
- Unsized: fat pointers are (ptr, len) for slices and
  str (today's `lust_str`, `src/runtime.c:19`), and
  (ptr, vtable) for `dyn`. A struct with an unsized
  last field stores the fat metadata in the pointer
  to the struct, not in the struct.
- ZSTs: size 0, align from fields (1 if none). Vec of
  ZST never allocates; the erased core handles
  size 0. `PhantomData` is a ZST field that still
  contributes variance and auto traits.

Gate: a `size_of`/`align_of` difftest over every shape
ts-rust asserts (the list comes from port scan output at
gate time, and must include the nested `Type` /
`TypeData` / `TypeReference` shape and `TypeMapper`)
plus a generator that enumerates the supported-shape
grammar above, not random samples: field kinds (scalars
of each width, refs, boxes, small enums, `bool` and
`char` fields, repr-int enums, small arrays) crossed in
structs, tuples, and enum variants, with declared
bounds (fields per shape, variants per enum, nesting
depth) stated in the generator, against rustc on each
tier 1 target. The generated set must include these
pinned shapes by name, each with its rustc size:
`enum { A(u8, u32), B }` (8); variants `(u8, u64, u8)`
and `(u32, u64)` (16 each) and `(u16, [u8; 3])` (6); a
`TypeMapper`-like enum with an `Array(Box<_>, bool)`
variant (16); `Option<Option<S>>` for
`S { a: bool, b: &u8 }` (16); a `Data(Payload)` enum
with two empty variants for
`Payload { pointer: &'static u8, flag: bool }` (16); a
`Pointer(&'static u8)` / `Byte(u8)` enum (16);
`#[repr(u8)]` and `#[repr(C)]` `Pointer` / `Empty`
enums (16 each); `enum { A(u32), B(u32) }` under three
nested `Option`s (8, by tag widening). A mismatch is
a layout bug or a cut grammar production (`L0652`);
never a waived difference.

The nested `TypeData` case runs as a standalone
layout-engine test over the real field-type graph: the
test builds the `Ty` graph for `Type`, `TypeData`, and
`TypeReference` with their real field types (`Box`,
`Rc<[T]>`, `&'static [T]`, and all) directly in the
engine's own test harness. It needs no `Box` in source
std and no lifetime support, so it can gate wave A1.
The same shape re-runs as an end-to-end source program
at the first stage that supports all of its parts
(9.3).

`size_of`, `align_of`, `offset_of!` evaluate in the
const evaluator from this engine. `mem::swap`,
`replace`, `take` lower to byte moves of `size`
through a stack temp when the type is not `Copy`.
Heap alloc always goes through the `alloc(size,
align)` intrinsic. Never zero-initialize a value Rust
leaves uninit (`MaybeUninit` in std and arena code);
codegen zero-fills *locals' storage* today for safety
(DESIGN C rules) but drop flags, not bytes, decide
whether a drop runs.

### 4.5 C ABI for the dev backend

Keep today's model and extend it:

- Every lust fn instance is a C function with a slot.
  Calls go through `lust_fns[slot]` in daemon builds
  (`src/cgen.rs:604-612`) so overlays can swap bodies.
  Direct calls are allowed only within one unit in
  cold (non-daemon) builds, where nothing is swapped.
  Decide per build mode, not per call: daemon mode is
  all-indirect, cold mode is direct within the final
  link. Vtable entries and fn ptrs and closure call
  fields always store the *slot trampoline*, a tiny
  generated forwarder with a stable address, in both
  modes. One trampoline per slot, emitted in the
  table unit.
- Aggregates pass by value as C structs, as today.
  Large aggregates (over 32 bytes) pass by hidden
  out-pointer for returns only; params stay by value
  to keep the slot cast simple. This is a dev ABI.
  Nothing here promises Rust ABI compat. Only
  `extern "C"` fns (shim and FFI surface) follow the
  platform C ABI, and only with C-ABI-safe types:
  scalars, raw ptrs, `repr(C)` structs of scalars.
  Check rejects other types at foreign signatures.
- Fat pointers are two-word C structs passed by value.
- Closures: the closure value is exactly its captures
  and nothing else. Its layout is the plain struct
  layout of the capture types (4.4): an empty closure
  is size 0, a closure that captures one `u8` is size
  1, as in rustc, because `size_of_val` can print both.
  No trampoline pointer and no tag word sits in the
  value. A direct closure call knows the def and calls
  its slot with `&env` first. For `dyn Fn` erasure, the
  trampoline lives in the vtable (one vtable per
  closure def per Fn signature) and in call-site
  metadata, never in the closure value.
- Checked arithmetic, bounds, and overflow keep
  today's runtime helpers and inline checks
  (`src/runtime.c:232-300`), with panic behavior from
  section 7.
- `#line` directives map C back to the `.rs` file and
  line through the per-build line table, as today
  (`src/cgen.rs:1059-1095`). Panic locations are
  (slot, token ordinal in the item) in stored form,
  resolved to line and column by the 4.2 remapping
  rule at emit time.

Backend swap stays possible: cgen consumes mono IR
only. The milestone 9 bake-off (tcc, Cranelift,
copy-and-patch) reads the same IR. Nothing in mono or
IR may name C types. Today's `CTy` in cgen
(`src/cgen.rs:37-115`) stays inside cgen.

## 5. Lifetimes: the restricted region model

This section implements DESIGN-TS section 2 option B.
Read that section with this one. Summary of the deal:
real region checking, bounded algorithm, stated
rejects. Ts-rust needs it: about 194 user types with
lifetime params at the last port scan (an older count
said 168; gates cite scan output, 9.4), 111 with
non-static ref fields, 27
with `&mut` fields, 10 with 2 or more lifetimes, one
with 3 (`transformers/destructuring.rs:93`, cited in
DESIGN-TS). Do not cap the region count.

### 5.1 Rollout in two steps

Step A (landed with W-BORROW increment 1): `'static`
and `'_` with real region checks. Step B (increment 2):
named lifetime params on fns, structs, enums, and impls;
then on type aliases whose generics are lifetimes only
(`type R<'a> = &'a str`): the body resolves at each use
with the alias's lifetimes mapped to the use site's
regions, so a generic Adt target works; collect checks
each body once, and the driver fingerprints its tokens.

Representation. The types that check, mono, and cgen
read stay region-erased: lifetime params do not enter
`Generics.params` (type param indexes and instance keys
do not change), and an Adt type drops its lifetime args.
Only `&'static dyn Tr` keeps its `'static` in the erased
type (`check::object`, ARCH 2.8); region signatures keep
every dyn object lifetime (the written one, else the
enclosing reference's, else `'static`). Collect fills a
borrow-checker side table, `Program.regions`
(`borrowck::RegionTables`), by resolving each signature a
second time with `Scope.regions = RegionMode::Keep`:

- per fn: a `RegionSig` with the params and return as
  regioned types (`Region::Static`, `Region::Param(i)`),
  the universal count, `'a: 'b` facts, display names,
  and the early-bound flag of each named lifetime;
- per trait method: the same, for the stubs that stand
  for it in template bodies;
- per Adt template: regioned field types
  (`adt_fields`); the lifetime names live in
  `GenTables.adt_lifetimes` for the resolver;
- per impl: the regioned `Self` type and associated
  types live in the method scopes (`self_ty_regioned`,
  `assoc_regioned`).

Universal numbering of a fn: the impl's named lifetimes,
the impl header's anonymous ones (`impl Tr for &str`),
the fn's own named ones, then one per elided input.
Elision follows Rust: `&self`'s region, else the only
input lifetime (named, `'static`, a hidden path lifetime,
or a written dyn object lifetime all count), else L0202.

### 5.2 What is checked

The engine is rustc's NLL (`src/borrowck/regions.rs`):

1. Every region slot of every local's erased type gets a
   region var (a reference: its own region, then its
   pointee's; an Adt: its lifetime params, then its type
   args; closures: their captures; a fn pointer type that
   names a lifetime of the item: one, 5.6). Var 0 is `'static`,
   vars `1..=n` the fn's universals.
2. Constraints `'a: 'b` come from relating types with
   variance at assignments, borrows (plus reborrow
   constraints through each deref, stopping after the
   first shared one, and well-formedness `T: 'l` for
   `&'l T`), aggregates (operand <: field type with the
   Adt's region args substituted), calls (the callee's
   region signature instantiated: universals and type
   param slots fresh, shared across occurrences; arg <:
   param, ret <: dest, callee facts and implied bounds),
   and the entry (parameter locals and `_0` equal the
   signature). A shape lust cannot pair equates every
   slot of both sides.
3. Region values are location-insensitive: a region
   contains a point when a local whose slots it reaches is
   live there (or drop-live, 5.4); a universal region
   contains every point.
4. A loan is in scope from its borrow through every point
   its region contains, until a statement overwrites or
   ends the borrowed local (rustc `kill_borrows_on_place`).
   Lust's IR reads a statement's operands in order and then
   writes, where MIR keeps one temporary per operand: a
   loan a later operand's local still carries, or an
   earlier operand's value holds, conflicts with the
   current operand's access (`x + *m` is E0503). A call's
   destination is written after the call, a two-phase
   receiver is activated by the call, and a temporary
   root of an assignment's place is evaluated after the
   value (`v[0] = v[1]`), as in rustc.
5. Each access is checked against the in-scope loans with
   the existing conflict rules. A loan of a local (or of
   storage it owns, through `Box`) in scope where the local
   dies is L0306, or L0307 when the loan reaches the return
   place. A universal region that reaches another without
   a declared or implied relation is L0733.
6. The uses rustc's MIR adds are in the IR too: a `let`
   binding is used right after its initializer (rustc
   `FakeRead(ForLet)`, so `let _x = { let y = ..; &y };` is
   an error); `let _ = place` mentions the place (`FakeRead`:
   live there, no access, so it may be mutably borrowed);
   a reference-typed `if`/`match` arm after the first one
   that does not diverge is read after its block ends
   (rustc's LUB reborrow); a value built through `Self` has
   the impl's regions (a body annotation on its temporary).

Calls lust cannot read precisely (builtins, intrinsics,
fn pointers, a signature it cannot pair) use the
conservative rule: the result may hold every argument's
regions (equal to them when it holds a `&mut`), and each
`&mut` argument's target may receive every other
argument's regions. An iterator item call (`next`,
`find`, `last`, `min`, `collect` into a `Vec`) takes
exactly the item's regions when the receiver names them
(`iter_items`: `slice::Iter<'a, T>` yields `&'a T`, an
adapter its inner iterator's items, `copied` drops the
outer reference, a `map` closure's what its body returns);
`fold`'s accumulator and result take its initial value and
what its closure returns. `to_vec` is a receiver rule (the
elements are the slice's). A dyn call instantiates the trait
method's signature; a call of a trait impl method also
instantiates the trait's (rustc checks calls against the
trait item, and an impl may refine it). A callee's `T:
'static` bound (and a struct's, for each local) makes the
regions bound to `T` outlive `'static`, and so does a
bound `P: Tr` when `Tr` or a supertrait is `'static`, or
when the impl selected for `P`'s type has `X: 'static`
where-clauses (on the parts of `P` those params match).

Closures follow a contract computed from their capture
types (`closure_roles`): a shared capture `&'c T` makes
`'c` and `T`'s regions sources; a mutable one `&'c mut T`
makes `T`'s regions sources and sinks (`'c` neither: a
captured `&mut` cannot escape); a by-value capture's
regions are sources and sinks. In the closure body every
capture slot, output slot, and argument slot is its own
universal, and the facts are: each source outlives each
other sink and each output slot. Relations between the
captured slots, the free argument slots (below), and
`'static` are not errors in the body: as rustc's closure
requirements, the creator solves the body on demand
(`closure_reqs`) and adds each relation the body needs, at
the creating statement (or the first use of a closure with
no captures). A body that does not check or lower gets the
whole contract (its own errors reject it). Every call's
result (a direct call, or any call taking a closure that
returns borrows, and iterator items through it) may hold
the sources, except where the callee's `Fn*` bounds give
the closure's output every region (no type param there:
`output_tied`), so the signature relates it to the result.
Argument slots are higher-ranked (L0733 when stored or
returned), except for a closure an iterator method takes
(check records `free_args` from `fn_mut_param`): its
arguments are items, free regions, sources (and sinks
behind a `&mut`), except the outer reference of an `&item`
argument (`filter`, `find`); an argument that is the item
takes exactly the item's regions when the receiver names
them (`iter_items`), and any other (`fold`'s accumulator)
links to the call's other arguments, write-backs only to
element regions. A closure passed straight to a generic fn
whose `Fn` bound takes a type param or projection there
(`F: FnOnce(T) -> U`) gets the same free arguments: each
input that is a type param (`&T`: past its outer
reference) is equated with that param's instantiation at
the call (found through the type `F` binds, so a mono
instance pairs like its template); a closure no bound
pairs links like an iterator method's. Unannotated
parameters of a closure with no expected signature (a `let`
closure) are free too, as rustc infers them: a direct call's
arguments flow into them. A free or named argument slot
where a bound or an iterator method is higher-ranked (`F:
Fn(&T)`, `filter`'s `&Self::Item`) is L0735 (rustc: "not
general enough"); a lifetime the bound writes (`F:
Fn(&'static Message)`, the callee's `'a`; the region
signature keeps bound inputs with regions) ties the slot to
that region. The bound's output is the closure's return type
(rustc deduces it from the bound): what the body returns
from captured or free argument slots outlives a written
output lifetime, and `'static` where the output is
higher-ranked (`F: Fn(&u8) -> &u8`: the callee picks it).
In `Fn` sugar an elided output lifetime is the only input
lifetime (`Fn(&'a u8) -> &u8` returns `'a`), else L0202
(rustc E0106). Under such a higher-ranked output the body
may return borrows of the one higher-ranked argument
(`ClosureEntry::bound_output`; rustc deduces `for<'r>
fn(&'r T) -> &'r U`). A type param `F` or a fn item
passed for a callee's `G: Fn*` bound proves it from its
regioned signature (`F`'s own bound; the fn's signature,
late-bound lifetimes as binders, early-bound ones fresh),
place by place (`entail_bound`; trait args are invariant):
lifetimes both write are one region, a binder takes the
lifetime `G` writes there or stays higher-ranked where
`G`'s is (not both), a higher-ranked `G` input needs a
binder (L0735), and outputs must agree the same way
(L0733). Fns with such bounds run the region pass even
without loans. `impl Fn*` arguments are type
params with those bounds (also nested ones). A
parameter annotation that names a lifetime (`|x: &'a T|`,
`|m: &'static Message|`) is that region of the enclosing
fn: free in the body, tied to it by the creator, and a
direct call's arguments flow into it; a return annotation
may pin output slots to `'static` (the body then proves
its result is `'static` itself). Named output lifetimes
and named parameters of a closure called from another
closure are L0203.

Templates are checked with abstract type params. Instance
bodies are borrow-checked too, without the universal
relation check (rustc checks the template; the instance
sees through type params where the call rules are
coarser).

Traits may have lifetime params: they are the first
universals of the trait's methods (and default bodies). A
bound `T: Tr<'a>` keeps its lifetime args
(`RegionSig::trait_bounds`; also on an impl's or trait's
params and `impl Tr<'a>` arguments), an impl header its own
(`RegionTables::impl_heads`: `impl Tr<'static> for S`, or
`impl<'d> Tr<'d> for S<'d>` matched through Self). A call of
a trait method instantiates the trait's lifetimes from the
receiver's type: this body's bound on a type param (`Self`
in the trait's own default body: the trait's lifetimes), or
the one impl whose header matches a concrete type (an impl
lifetime the Self type does not name is free), else
`'static`, never fresh. A generic call that binds `T`
equates the bound's lifetimes with the bound type's (trait
args are invariant): `impl Mark<'static> for S` makes `S:
Mark<'a>` force `'a: 'static` (Sol review P0.5). An impl
whose own `T: Tr2<'x>` where-clauses name such a trait replays
them through the part of Self that `T` matches (a bounded
depth; any other form answers `'static`).
The impl contract (L0734) reads a trait lifetime as the
impl header's region.

Signature-level checks: an impl method must keep its trait
method's region contract (L0734: it may promise a
`'static` result where the trait borrows, never less, and
may not demand a `'static` input); a fn item with an
early-bound lifetime does not coerce to a fn pointer
(L0110, rustc E0308).

### 5.3 Variance

Per user Adt template, by fixpoint over field types: type
params from the erased fields, lifetime params from the
regioned ones (`AdtTables`). `&'a T`: covariant in `'a`
and `T`; `&'a mut T`: covariant in `'a`, invariant in
`T`; raw pointers: `*const` covariant, `*mut` invariant;
fn pointers: inputs contravariant, output covariant;
builtin containers covariant; a dyn object lifetime
covariant (one slot per dyn type; a coercion may also
shorten it behind the outermost `&mut`, as rustc's
unsizing does; a trait bounded by `'static` makes it
`'static`); closures, opaque types, and projections
invariant (conservative). Cycles converge
because the lattice is finite (bivariant, co, contra,
invariant).

### 5.4 Drop check

A `Drop` of a maybe-initialized local is a use of its
drop-live slots: every slot under a user `Drop` impl, the
owned parts below containers (`Vec`, `Option`, `Result`,
`Box`, tuples, arrays, closure captures, Adt fields), and
nothing behind a reference. Builtin containers act as
`#[may_dangle]` on their elements: a `Vec<&T>` may drop
after its referent, a `Vec<W<'a>>` with `W: Drop` may not.
Per Adt lifetime and type param, the drop mode (none,
owned, all) is part of the Adt fixpoint.

### 5.5 What is rejected

Both-reject (rustc rejects too): L0202 missing lifetime
specifier (E0106: elision, a reference in a field or an
alias without a lifetime, a hidden lifetime in an impl
header, E0726); L0203 undeclared lifetime (E0261),
reserved or duplicate names; L0110 lifetime arity (E0107),
unused lifetime param (E0392), unconstrained impl lifetime
in an associated type (E0207), early-bound fn item to fn
pointer (E0308); L0306/L0307/L0303/L0312 loan conflicts;
L0733; L0734; L0735.

Stated subset cuts (valid Rust lust rejects, tests/reject):

- L0203: explicit lifetimes in body types other than a
  `let` annotation on plain names or tuples of names (a
  `let` annotation's regions are kept: the binding's slots
  equal `'static` or the fn's named lifetime); a named
  lifetime in a fn pointer type outside fn signatures and
  `let` annotations, two in one, or one nested in another
  fn pointer or `dyn` type; lifetimes in a dyn type's trait args;
  an elided (`'_` or missing) lifetime arg of a trait,
  lifetime args in a trait's own bounds (supertraits,
  `Self` where-clauses), and associated types in a trait
  with lifetime params; `T: 'a` bounds on named lifetimes;
  inside a closure, a call through a type param's `Fn`
  bound whose argument names a lifetime of the enclosing
  fn, or passing such a param on to a generic fn (the
  closure body cannot name that lifetime). (`'a: 'static`
  and an Adt's own outlives facts, `struct H<'a, 'b: 'a>`,
  are checked: every use of the type meets them, and a
  signature naming it assumes them.)
- L0731: any explicit lifetime turbofish arg (rustc also
  rejects it whenever the fn has a late-bound lifetime,
  E0794).
- L0820: closure to fn pointer coercion and closures stored
  in Adts (closure.rs). A closure that returns a borrow of
  its higher-ranked argument is L0733, as in rustc, except
  where its bound's output is that argument's lifetime
  (`F: Fn(&T) -> &U`).
- L0203: a `for<..>` binder that elision cannot express (a
  binder lifetime twice in the inputs, an output one that is
  not the one input lifetime) and higher-ranked where clauses
  on types (`for<'a> &'a T: Tr`). The parser rewrites the
  other binders on fn pointer types, `Fn*` bounds, and `dyn
  Fn*` to the elided form (`parser/hrtb.rs`); check rejects a
  binder name that shadows one in scope (E0496).
- GATs (L0620), async (milestone 8b), as before.
- L0509: a name that two or more glob imports (or a glob and a
  re-export) bring with an answer that depends on rustc's glob
  event order (`resolve/order.rs`): the same item with different
  visibility where rustc can re-fetch a narrower binding and drop
  the widest, or an ambiguity carried on by a further glob. When
  no re-fetch can lower it, lust keeps the widest visibility, as
  rustc does. An explicit import of the item fixes it.

### 5.6 Negative corpus

`tests/fail` holds the both-reject corpus (region_*, nll_*,
dropck_*, named_*, alias_*, box_*, trait_method_static_*,
and the `sol_*` probes of the design review), `tests/reject`
the subset cuts, and `tests/pass` the positive twins and
the gate shapes (`lifetime_gate_parser`,
`lifetime_gate_json_decoder`, `lifetime_gate_rule_context`).
Each case runs against rustc 1.99 in difftest.

Known gaps: regions of body types other than `let`
annotations (casts, turbofish, closure params); named
lifetimes in a dyn type's trait args (L0203; `&'static`
there works) and the fn pointer cuts above; closure
arguments are higher-ranked outside iterator methods and
bounds over type params (rustc also frees an unannotated
closure's arguments); the closure contract's coarser source-to-sink
edges; `T: 'a`; Adt inferred outlives
facts (missing facts reject, never accept); precise
builtin region signatures; named lifetimes in a closure's
return annotation (`'static` works); promotion of constants
other than `&[]` and `&mut []` (they need static storage in
codegen; `Body::promoted` covers the empty array only).

Fn pointer and `dyn Fn` regions: check keeps a written
`&'static` as `Region::Static` even in erased types
(`Scope::static_refs`; a `'static` Adt lifetime arg there
stays L0203: erased Adts carry none), and a fn pointer type
may name one lifetime of the enclosing item (W-BORROW3, in fn
signatures and `let` annotations, `Scope::fn_ptr_free`):
`FnSig::free_slots` marks the signature slots it fills (check
finds them by resolving the signature again with that
lifetime as a marker), and `FnSig::free_region` is `Erased`
in check's types and the lifetime in region signatures. A
value of such a type has one region slot, that free region,
held invariant. Every other region of the signature is
`'static` where written, else elided, so late-bound (an elided output
is the one input lifetime, else L0202, as in `Fn` sugar and
fn pointer types anywhere); check's own `'static` proof
(`region_walk`) stays for `&'static dyn Tr` only, and a
coercion between two such types needs the found one to be
as general (`sig_static_mismatch`: no `'static` input where
the target takes any, no borrowed output where it returns
`'static`; L0110, rustc E0308). Borrowck relies on that:

- A call through a `dyn Fn*` value or a fn pointer
  (`call_late_bound`) gives each elided input slot a fresh
  region of the call that the argument outlives (a
  `'static` one is `'static`, a free one the pointer's
  slot), and each elided output slot the one input slot's.
  The receiver lends nothing to the result beyond its free
  region, and an argument reaches nothing else.
- A coercion to `dyn Fn*` (`dyn_fn_coercion`) proves the
  source takes any region there: a closure with a free
  argument slot (a `let` closure, a named annotation) is
  L0735 unless the target writes `'static` there (then the
  slot is `'static`; a closure checked against such a type
  gets those slots like a `'static` annotation, inputs and
  output), and what a closure returns from its captures must
  be `'static`; a closure written there may return its one
  argument (`ClosureEntry::bound_output`); a type param or
  a fn item is proved by its signature (`entail_dyn`, as
  `entail_bound`). A coercion to a `'static` object lifetime
  makes the data outlive `'static`; a body annotation's
  object lifetime is inferred when unwritten, as rustc's.
- One proof (`regions/fnptr.rs`, `sub_sigs`) serves a fn
  item coerced to a fn pointer (`Rvalue::FnValue`), a fn
  pointer coerced to another (`walk`, when either names a
  free region; two without one stay check's
  `sig_static_mismatch`), and a fn pointer passed for an
  `Fn*` bound or coerced to `dyn Fn*`: the target's binders
  are placeholders, the source's (a fn's late-bound
  lifetimes, a pointer's elided ones) existential, early-bound
  lifetimes and free regions this body's vars. Slots relate by
  variance for coercions (rustc's subtyping: `fn h<'x>(&'x u8,
  &'x u8)` is a `fn(&u8, &u8)`, but not under `&mut`) and both
  ways for trait matching. A placeholder may outlive only
  itself (L0110 for coercions, L0735 at bounds and `dyn`); a
  var that must outlive one must be `'static`. A closure or
  a fn without a region signature coerced to a pointer type
  with a free region is L0203.
- In fn pointer types elision does not count lifetimes inside
  fn pointer params (`elision_regions`, rustc E0106).
- Array and `vec!` literals join their elements by rustc's
  LUB: a fn item after the first must have the element fn
  pointer type's lifetimes up to renaming binders when either
  is higher-ranked (check `fn_elems_lub`, `lub_shapes_fit`;
  L0110, rustc E0308). `if`/`match` arms coerce to the
  expected type as before, and to a fn pointer type with a
  free region one by one (rustc's expectation).

## 6. Macros

### 6.1 Where expansion sits

Expansion does not run before cfg stripping or before
import resolution. Rust strips cfg before it expands a
node, and it resolves macro paths through imports. A
complete expansion phase followed by a complete
resolution phase cannot do either: a call under
`#[cfg(windows)]` to a Windows-only macro would expand
(or error), and a macro brought in by `use` would not
resolve. Ts-rust re-imports `go_enum` and `go_flags`
with `pub(crate) use goport_util::{...}` in an inline
module (`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/lib.rs:44-47`).

So per crate, one outline worklist interleaves all of
it (the same worklist as 1.3):

```text
lex each file to token trees (delimiters nested)
parse the "outline": items with MacroCall nodes intact,
  fn bodies as token ranges (as scan does today)
repeat until nothing changes:
  1. strip cfg on each known item and attribute (1.6)
  2. load files for `mod` items now known (1.2)
  3. resolve imports with the items now known (1.3)
  4. expand every macro call whose macro path resolves,
     outermost-first, re-lex nothing (tokens all the way)
  5. parse the new items an expansion produced; a new
     `mod` goes back to step 2, a new `use` to step 3
then: parse bodies to full AST, resolve, collect, ...
```

Rules of the loop:

- A disabled `compile_error!` or `include!` never runs:
  step 1 removes its node before step 4 can see it.
- A macro call whose path does not resolve yet waits. If
  the loop ends with calls still waiting, that is the
  unresolved-macro error (`L0802`).
- An expansion can emit items, `use` lines, and `mod`
  items. All go through the same loop. Expansion records
  the bindings it used; an item generated later that
  would change an earlier macro resolution is `L0504`
  (1.3, rustc E0659).
- One integration owner runs this loop: W-RESOLVE owns
  the worklist driver and the module, import, and cfg
  steps; W-MACRO owns step 4 behind a frozen interface
  (`expand(call, macro_def) -> token trees`). Do not
  split the loop itself between two packages (9.3).

The lexer grows token trees: `TokenTree = Token |
Delimited(kind, Vec<TokenTree>, span)`. Today tokens
are flat (`src/lexer.rs:20-115`). Keep a flat view for
the scan/hashing path; the parser consumes trees for
macro positions and flat tokens elsewhere. Macro calls
can appear in item, stmt, expr, pat, type, and vis
positions. The outline parser must find item boundaries
without expanding, which token trees make possible:
an item-level macro call ends at its closing delimiter
plus an optional `;`.

Expansion order: outermost-first per position, as in
rustc. A macro can expand to another macro call
(ts-rust forwards args between macros, DESIGN-TS
section 5). Expand until no calls remain or a cap
hits. Caps: expansion depth 128, output tokens per
call 1,000,000, total expanded tokens per crate
16,000,000. A cap hit is `L0801` with the macro named,
never a hang. Depth follows rustc: the crate root's
`#![recursion_limit]` (128 to 2048; lower is `L0522`),
and a std macro counts the levels rustc's expansion of
it uses (`builtin::rustc_depth`). Expansion moves to a
fresh thread stack when its segment is used up, so
depth never overflows the native stack. Repetition
matching is linear in the matched tokens.

Macro *definitions* are items. `macro_rules!` visibility:

- Textual: a def is usable after its point of
  definition in the same module and in child modules
  declared after it, plus across modules with
  `#[macro_use]` on the `mod` (or on the crate root
  for all modules). Implement with a scope stack built
  during the outline walk, ordered by (file, position).
- Path-based: `#[macro_export]` puts the macro at the
  crate root in the macro namespace, usable as
  `crate::name!` and `dep::name!` and importable by
  `use dep::name`. `$crate` inside expands to the
  defining crate's root path.

Both layers feed the expander a `(macro DefId)` per
call site. Unresolved macro name: if it is a builtin
(6.4), use that; else `L0802`, with the failed lookup
recorded (section 8).

### 6.2 Matching and transcription

Fragment specifiers to support, from ts-rust evidence
(INVENTORY Q2: only simple fragments) plus the std
macro needs: `expr` (2024: `expr_2021` too), `ident`,
`ty`, `tt`, `literal`, `meta`, `vis`, `pat` (2024:
`pat_param` distinction: accept `pat` as Rust 2024
defines it), `block`, `item`, `stmt`, `path`, `lifetime`.
A fragment means what the edition of its *definition*
says, not the caller's edition; the def's edition is
part of the def record and the expansion cache key
(6.5). All lust source is 2024 today, and adapter macro
defs are 2024, but the key keeps the rule honest.

Opaque fragments. A matched fragment is not a raw token
sequence. Store it as `Fragment(kind, node, ctxt)`: the
parsed node (or its tokens) with a fragment identity.
When a macro forwards `$x:expr` into another macro
call, the inner matcher sees one opaque expr unit. It
must not re-split the tokens: an outer macro that
forwards the expr `3` to a macro with a `(3)` arm and a
`($x:expr)` arm picks the expr arm in Rust. Re-parsing
the forwarded tokens as a literal would pick the other
arm and change the program. Ts-rust forwards exprs
between `by_data!` and `match_data!` at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/ast/node.rs:330-338`,
so this path is in the port, not only in tests. The
exceptions that stay transparent are `ident`,
`lifetime`, and `tt`, as in the Rust reference: an
inner matcher can match those token by token. Every
other kind is opaque to an inner matcher and can only
bind to a metavariable of the same kind (`expr` to
`expr`, `ty` to `ty`, and so on) or be transcribed
whole.

Matching: per arm, a token-tree matcher with
repetition `$( ... ) sep*`, `+`, `?`. Arms try in
order; the first full match wins, as in Rust. But a
match that only succeeds by guessing between two
fragment parses is an error, not a success. Rust
reports *local ambiguity* and stops:
`macro_rules! m { ($($i:ident)* $j:ident) => { () } }`
then `m!(x)` fails, because `x` can be an `i` or the
`j`. The matcher therefore tracks, at each input
position, the set of live partial parses. If two
different fragment bindings can both consume the same
next token, the call fails with `L0805` (local
ambiguity), even if one path would later match the
whole arm. Bounded guessing inside repetitions of
plain token trees is fine; guessing between fragment
kinds or between two metavariables is not. Keep the
live-set size capped; a cap hit is `L0801`.
Fragment parsing reuses the real parser on the
fragment's token slice: an `expr` fragment must parse
as one expr and consume exactly its slice up to the
follow set the matcher determines. Implement the follow
sets Rust requires (for `expr`: `=>`, `,`, `;`).
Transcription substitutes `$name` (whole fragments,
with kind checks) and repetitions,
checks repetition depth agreement, and handles
`$crate`. Nested repetitions to depth 4 cover
ts-rust (`flags_macros.rs:10` nested repetitions with
`ident`, `ty`, `meta`, `expr`).

Metavariables keep their tokens' spans and hygiene
contexts (6.3). The transcription output is a token
tree stream fed to the parser in the syntactic
position of the call. Parse errors inside expanded
code report at the call span with a note naming the
macro and its def span.

### 6.3 Hygiene and spans

`Span` must grow. Replace `src/diag.rs:5-19`:

```rust
pub struct Span { pub file: FileId, pub lo: u32, pub hi: u32, pub ctxt: CtxtId }
pub struct CtxtId(pub u32); // 0 = root, else index into expansion table
pub struct Expansion { pub macro_def: DefId, pub call_span: Span, pub parent: CtxtId }
```

Identifiers carry `(Sym, CtxtId)` where hygiene
matters. This is mixed-site hygiene, as in Rust, and
the split is by what the name refers to:

- *Locals and labels* (and lifetimes and generic params
  a macro introduces) resolve at the definition site. A
  local binding written in the macro body gets the
  expansion ctxt and does not capture a user local of
  the same name. An ident the caller passes in keeps
  the caller's ctxt, so a macro that uses `$name` as a
  local binds the caller's variable.
- *Item paths* resolve at the call site. An ordinary
  path written in a macro body, `helper()` say, looks up
  `helper` in the invoking module, not in the module
  that defines the macro. A probe with `helper`
  returning 1 at the def site and 2 at the call site
  prints 2 in rustc. A macro that must name its own
  crate's items writes `$crate::...`; `$crate` is
  absolute and is the only def-site path form. Item
  names a macro *defines* also land in the invoking
  module.

Comparing expanded token text does not test
any of this: two token-equal expansions can bind
differently. The macro gate is executable tests
(capture, shadowing, a passed ident used as a local, a
generated label, a call-site item path, a `$crate`
path) run in `tests/macros/` against rustc output
(9.3).

Tokens a macro body writes get the expansion's ctxt.
Tokens that come from a metavariable keep the spans
and ctxts they arrived with (6.2): transcription must
not restamp a forwarded fragment with the expansion
ctxt, or the caller's idents would stop binding the
caller's locals. Every token keeps a span that maps
back: diagnostics print the call site first, then
"in expansion of `name!` at
def:line" chain. The panic line table uses the call
site's file and line. This span change touches every
stage; it is serial refactor S1 and lands before
macros (milestone 4 can carry multi-file spans before
expansion exists).

### 6.4 Builtin macros and derives

Builtin macros stay compiler forms, parsed directly,
never expanded through the token machinery:
`format!`/`format_args!`, `println!`/`print!`/
`eprintln!`/`eprint!`, `write!`/`writeln!`, `vec!`,
`panic!`, `assert!`/`assert_eq!`/`assert_ne!`,
`debug_assert!`/`debug_assert_eq!`/`debug_assert_ne!`,
`unreachable!`, `todo!`, `unimplemented!`, `matches!`,
`cfg!`, `concat!`, `stringify!`, `include_str!`,
`include_bytes!`, `include!`, `env!`, `option_env!`,
`line!`, `file!`, `column!`, `module_path!`,
`thread_local!`, `pin!`, `offset_of!`, `compile_error!`,
`dbg!`. `line!` and `file!` read the call-site span
through the remapping rule in 4.2, with `file!` in the
Cargo path form of 3.5. Ts-rust call counts are in
INVENTORY Q2
(`format!` 1,299, `vec!` 975, `panic!` 533, `matches!`
249). Semantics notes:

- `include_bytes!` (49 uses) and `include_str!` read a
  file relative to the current file at expand time.
  The file's hash enters the expansion cache key and
  the dep graph. A missing file is `L0803`.
- `env!` (3) and `option_env!` (4) read from a driver
  provided env map: Cargo's build env (`CARGO_PKG_*`,
  `OUT_DIR`) plus the client's env: a daemon request
  carries its client's; a one-shot or front image build
  reads its own process env, each var once, and keeps
  only the vars read (no whole copy reaches an image).
  The read keys enter the cache key. Reading live env
  per request breaks cache soundness.
- `thread_local!` (73) desugars to a static marked
  `#[thread_local!]` (collect types it `LocalKey<T>`)
  plus an init fn `NAME#init`. Both spellings are
  unlexable, so the expansion needs no `unsafe` and no
  user code can name them (7.3).
- `debug_assert!` compiles to nothing when
  `debug_assertions` cfg is off. Dev default on.
- `vec![x; n]` with non-`Copy` `x` clones per element,
  as today (`src/cgen.rs:586-598` seeds the pattern).

Derives are compiler-generated impls (2.2), not
macros. Proc macros: out. A `proc-macro` dependency in
the graph is `L0804` at session start with the crate
named. Ts-rust has none.

### 6.5 Caching expansions

Cache per call site, keyed by: macro def fingerprint
(section 8 hash of the def tokens), hash of input
tokens, ctxt of the call, cfg environment hash,
edition, and hashes of any files or env vars read by
builtins during the expansion. Value: the output token
trees plus the list of items or the AST fragment it
parsed to, where position allows. An unchanged call
reuses output even when surrounding code moves. A def
edit invalidates its calls through the dep graph, not
by flushing the cache. The cache key also carries the
macro def's edition (6.2).
Gate from PLAN.md milestone 4, restated: every macro
def the port scan lists at gate time expands correctly
(the scan reports 80 defs under 70 names; an older
count said 66, so gates cite scan output, not a number
in this document). Test in three layers in
`tests/macros/`: token compare against
`rustc -Zunpretty=expanded` on fixtures (printed
expansion is lossy, so compare tokens, not text);
executable hygiene and fragment tests whose output must
match rustc (6.3); and both-reject cases for local
ambiguity and caps. Token equality alone proves
nothing about binding, spans, or forwarded fragments.

## 7. Panics and threads

### 7.1 The decision on panic recovery

Explicit propagation in IR, with cleanup edges. This
is DESIGN-TS section 6's spike, decided here with a
fallback gate. Rejected alternatives:

| Option | Normal-path cost | Why not |
|---|---|---|
| Abort only (today, `src/runtime.c:111-127`) | 0 | Ts-rust catches panics in 59 places. The LSP would die on a bad request. Not parity. |
| `setjmp` per fn with a cleanup registry | One `setjmp` per fn with droppable locals, plus registry push/pop per scope | `setjmp` cost lands on every fn, and "which locals are live" at jump time needs the same cleanup metadata as explicit edges, with worse C semantics (volatile rules). |
| `longjmp` from panic, skip drops | Near 0 | Wrong: skips drops, breaks rule zero wherever a drop prints or releases a lock. |
| Real unwinding tables for tcc C | 0 until panic | tcc emits no unwind info. Writing it is a backend project. Release builds use clang or zig cc, which emit it: 7.2a. |
| Explicit propagation (chosen) | One global counter load after each call; duplicate drop code on cleanup edges | Simple C, exact drop order, works with tcc today. No C TLS (7.2). |

### 7.2 Explicit propagation design

One boolean cannot do this job. While cleanup runs, the
original exception is still in flight, and helper calls
inside a destructor must run normally even though
`thread::panicking()` is true. A single flag makes every
helper take its unwind edge at once. So thread state
keeps two things apart: the *in-flight exception* that
must propagate, and the *unwind depth* that says cleanup
is under way.

No C TLS anywhere, in generated code or in the runtime.
The bundled tcc emits a thread-local access in a shared
object with no relocation, so a `_Thread_local` in a
`.so` aliases the executable's variable (a probe reads
the exe value 3, then sees the exe write 77). Daemon
builds link `libbase.so` with an overlay, so a C TLS
panic flag would corrupt state silently. This also
settles macOS, where the same question is open: the
design needs no Mach-O TLS answer.

State:

- One global counter `lust_panicking_threads` (a plain
  atomic load). It is 0 in almost every run. It counts
  threads with unwind depth above 0.
- Per thread, through one pthread key:

```c
typedef struct {
    int unwind_depth;        // > 0 only while a panic or its cleanup is active
    int catch_depth;         // active catch_unwind boundaries; separate count
    int inflight;            // an exception must propagate now
    uint64_t gen;            // bumped on each new exception
    void *payload_data;      // Box<dyn Any + Send> parts
    const struct lust_vtable *payload_vtable;
    lust_loc loc;
    int in_hook;
} lust_panic_state;
```

A catch boundary is not an active panic, and the state
keeps the two apart. `catch_depth` counts boundaries
only; it never feeds `panicking()`. `unwind_depth`
rises only when a panic actually starts and while its
cleanup runs. Ordinary code inside a `catch_unwind`
closure therefore sees `thread::panicking() == false`,
as in rustc. Code inside a catch that itself runs
during an outer panic (a catch inside a destructor)
still sees true, because the outer `unwind_depth` is
raised.

IR change: calls are terminators with an optional unwind
successor (S7 builds the slot; today a call is an
`Rvalue` inside a statement, `src/ir.rs:81`, and
`Terminator` has no call case). Lowering builds, per
scope, cleanup blocks that run the drops for locals live
at that scope exit, in reverse order, then propagate.
The same cleanup-edge pass serves scope-exit drops and
unwind drops; build it once, in wave A with `Drop`.

Call protocol. Before a call, the caller reads the
thread `gen` (only when the global counter is non-zero;
else the answer is "no exception"). After the call, the
caller takes its unwind edge only when a *new* exception
is in flight: the global counter is non-zero and this
thread has `inflight` set with a `gen` newer than the
saved one. Code shape in daemon builds:

```c
ret = ((SIG)lust_fns[slot])(args);
if (lust_panicking_threads && lust_inflight_new(saved_gen)) goto cleanup_3;
```

The fast path is one plain load and a predictable
branch. Every call checks. There is no can-panic
fixpoint in daemon builds: most fns can panic, and a
global fixpoint makes a leaf edit that adds a panic
rewrite the C of every caller up the graph. A later cold
build may skip the check for calls to fns proved
panic-free inside one unit, only with profile evidence.

Cleanup protocol. When a frame takes its unwind edge,
it saves the in-flight exception (payload parts, `gen`,
location), clears `inflight`, and raises `unwind_depth`.
Destructors then run as normal code: their own calls
return normally, and `thread::panicking()` (which reads
`unwind_depth > 0 || in_hook`) is true throughout. Two
ends:

- The destructor returns with no new exception: restore
  the saved exception and keep propagating.
- The destructor raises a new exception that *escapes*
  it: that is a double panic. Abort with Rust's
  double-panic message. But if the destructor catches
  its own second panic with `catch_unwind` and returns
  normally, the outer exception resumes. Rust allows
  this, and a probe prints `after true true` from inside
  the destructor, then catches the outer panic. The
  saved-slot design holds both payloads at once: the
  outer in the frame save area, the inner in thread
  state.

`catch_unwind` protocol. Enter: raise `catch_depth`
(and nothing else), save `gen`, call the closure. While
the closure runs normally, `unwind_depth` is whatever
it was on entry, so `panicking()` keeps its entry
value. A panic that starts inside the closure raises
`unwind_depth` at the raise point, like any panic. On
return: if a new exception is in flight, move its
payload into the `Err` return value, clear `inflight`,
lower `unwind_depth` back to its entry value, lower
`catch_depth`, and return normally. If the closure
returned normally, only `catch_depth` drops. Nested
catches nest by `catch_depth`, each with its own saved
`gen`.
`resume_unwind` installs the given payload as in flight
*without* running the hook. A panic that starts fresh
runs the hook first. A panic inside the hook aborts.

Semantics that must match Rust:

- Payload: `Box<dyn Any + Send>`. `panic!("...")`
  payloads are `&str` or `String` by the `as_str()` rule
  in 3.5 (`panic_any` for other types). `catch_unwind`
  returns `Result<R, Box<dyn Any + Send>>`.
  `resume_unwind` re-raises the same payload object.
  Downcasts through the checked type id in 2.8.
- Unwind safety: `catch_unwind` requires its closure to
  be `UnwindSafe` (2.7). A closure that mutates a
  captured local through `&mut` fails that bound, as in
  rustc (E0277), unless the source wraps it in
  `AssertUnwindSafe`. The wrapper overrides the check
  only where it is written.
- Panic hook: `set_hook`/`take_hook` store one fn
  (`dyn Fn(&PanicHookInfo) + Send + Sync`) in a
  global. The hook runs at panic start with payload
  and location, unless a hook is already running.
  `resume_unwind` skips the hook.
  Ts-rust's bins install hooks that format Go-style
  output and use `in_go_recover` depth to stay quiet
  during recovery
  (`crates/ts_goport/src/gopanic.rs:138-166`). The
  default hook prints Rust's panic line format.
- Lock poisoning: a `MutexGuard` or `RwLock` guard
  records `panicking()` when it acquires the lock. Its
  `Drop` poisons the lock only on the transition:
  `panicking()` is true at drop *and* was false at
  acquisition. The three cases, all checked against
  rustc: a guard locked and dropped inside a successful
  `catch_unwind` does not poison (`panicking()` is
  false at both points); a guard locked before a panic
  and dropped by the unwind poisons; a guard locked and
  dropped inside a destructor while an outer panic is
  already active does not poison (true at both points).
  The guard keeps the recorded bit itself, in std
  source; the runtime only supplies `panicking()`,
  which reads `unwind_depth` and `in_hook`, never
  `catch_depth` and never the in-flight slot. `lock()`
  returns `Err(PoisonError)` after a poison. `RefCell`
  borrow flags reset in guard drops as usual.
- Thread panic: an uncaught panic at a thread root
  ends that thread; `JoinHandle::join` returns
  `Err(payload)`. Other threads continue. Main thread
  uncaught panic: run hook, unwind `main`, exit with
  Rust's code 101.
- Foreign boundary: an in-flight exception must not
  propagate through a C or shim frame. Callback
  trampolines (3.7) turn it into a status code at the
  boundary and keep it in flight for the lust caller.
  A panic escaping an `extern "C"` lust fn aborts, as
  in Rust. Panics in shim Rust code are caught inside
  the shim (3.7 link rule).

`AssertUnwindSafe`, `catch_unwind`, `resume_unwind`,
`panic_any` live in `library/std`. `catch_unwind` needs
one compiler assist: the closure call inside it is
marked so lowering emits the landing pad above.
Represent it as an intrinsic wrapper
`intrinsics::catch_unwind_call` known to lowering.
Everything else is source.

Order of work: semantics first, cost second. W-PANIC
starts with the semantic corpus in `tests/unwind/`
(helper calls inside a destructor, a locally caught
second panic in `Drop`, nested catches, poison after a
caught panic, `resume_unwind` hook silence) against
rustc in unwind mode. Its first gate also carries the
two catch-boundary cases above as executable tests:
`panicking()` is false and a mutex stays unpoisoned
inside a successful catch, and a mutex locked and
released inside a destructor during an outer panic
stays unpoisoned. Only then run spike K2 for cost
on dense-drop code (RefCell guards, Rc captures, sort
comparators, iterator short-circuits): measure C bytes,
tcc time, and run time against abort mode. The old
estimates (30 to 60% C growth, 5 to 15% run time) are
not data. If C bytes grow over 2x or run time over 1.5x
on those fixtures, stop and evaluate per-fn `setjmp`
with a cleanup registry before building threads on top.
Keep `panic = "abort"` crates (wasm
profile in ts-rust's `Cargo.toml:38-47`) on the old
path: no checks, `catch_unwind` rejected there.

#### 7.2.1 As built (W-UNWIND)

The build follows the plan above: explicit propagation, cleanup
ladders from lowering, no C TLS, one global load on the fast path.
These parts differ from the plan, and why:

- Mode. `-C panic=unwind` sets `ProfileFlags::panic_abort` false; a
  Cargo package follows its workspace's `[profile.dev] panic` (Cargo's
  default unwinds, as ts-rust's dev profile does). A single file
  without the flag unwinds too, as plain rustc does (fx-promtuple round 5;
  it was panic=abort before, so its panics differed from rustc's). The profile is part
  of the session key, so the daemon keeps one session per mode and
  never mixes their IR or C. `Program::unwind` carries the mode to
  lowering and codegen; `cfg(panic)` follows it. Under panic=abort
  the IR and the C are unchanged.
- State. No `gen` counter and no separate unwind and catch depths.
  Each thread has Rust's local panic count (`panicking()` is
  `count > 0`; a catch lowers it), an in-hook bit, and a *pending*
  exception. When a frame takes its unwind edge it moves the pending
  exception into a frame local (`lust_exc ex`), so nothing is pending
  while its destructors run, and gives it back at the end of its
  ladder. The global `lust_unw_pending` counts threads with a pending
  exception, so it is 0 during cleanup too and destructors take the
  fast path. A drop that ends with a new pending exception in a
  cleanup block aborts with Rust's "panic in a destructor during
  cleanup".
- Statement edges. Panics also start inside statements (overflow,
  indexes, unwrap, RefCell, runtime helpers, drop glue of a scope
  exit). Lowering records a cleanup entry for each statement that can
  unwind (`Body::stmt_unwind`; empty under abort), built from the
  same ladder as calls. A scope's drops lower while the scope is
  still on the stack, so a panicking drop still drops its siblings.
  Codegen checks after such a statement, wraps each call statement in
  it (`cgen/unwind.rs`), and emits an index as a GNU statement
  expression that jumps to cleanup before it reads the element (tcc
  and gcc both accept a `goto` out of one).
- Code that runs on. A runtime helper that panics returns a safe
  placeholder (an empty range, 0 for a division) so the rest of its C
  statement does no harm, and any lust fn called while its thread has
  a pending exception returns at once (one check in the prologue).
  That covers glue and runtime callbacks (sort comparators, hash
  callbacks) without changing them: they finish with placeholder
  answers and the caller's check unwinds.
- Glue. Drop glue drops the remaining fields and elements as cleanup
  after a panic (`lust_unw_dstep`) and passes the exception on at its
  end, as Rust's drop glue does. A print writes piece by piece
  through the stream (`lust_print_begin`, both modes); a fmt impl that
  panics stops the print like a fmt error, so the text it wrote stays
  in order with what its cleanup prints.
- Hook text. The default hook prints the backtrace note only for the
  first panic of the process; a panic while panicking prints Rust's
  "stack backtrace:" header and no frames (difftest drops frame lines
  on both sides). A TLS destructor that panics aborts with Rust's
  "thread local panicked on drop" line. `main` that ends by a panic
  exits 101 after TLS destructors and the stdout flush.

- Catch and payloads (slice 2). `catch_unwind`, `resume_unwind`, and
  `panic_any` are compiler-known (check/unwind.rs, lower/unwind.rs,
  cgen/unwind.rs); `catch_unwind`'s call is lowered with no cleanup
  successor, which is the catch boundary: codegen calls the closure,
  and a pending exception becomes `Err(lust_unw_catch())` (the count
  falls). `AssertUnwindSafe`, `PanicHookInfo`, `set_hook`, `take_hook`,
  and the `UnwindSafe`/`RefUnwindSafe` marker traits are std source
  (library/std/src/panic.rs, an overlay). Payload types follow rustc:
  a `&'static str` when the message is a literal after W-STD-B's
  literal-argument inlining (and for core's literal messages:
  overflow, division by zero, unwrap on None, assert without
  arguments), else a `String`. The runtime builds the `Box<dyn Any +
  Send>` of those two itself, with vtables over the two type ids main
  passes in (`lust_unw_init`).
- Hooks. The hook lives in the runtime as the bytes of std's
  `Option<Box<dyn Fn(&PanicHookInfo) + Sync + Send>>` (std-only
  intrinsics `panic_hook_swap`/`panic_hook_ref`). A panic with a hook
  installed calls std's `__lust_run_hook`, whose slot main registers;
  `PanicHookInfo` reads the payload and location from the runtime's
  thread state (lust's region model ties a stored reference to the
  struct's lifetime). The hook runs in both modes; a panic inside it
  aborts with Rust's text. `thread::panicking()` reads the runtime in
  both modes.
- Unwind safety. `UnwindSafe` and `RefUnwindSafe` answer from one
  fixed table (check/unwind.rs header), measured against rustc 1.99
  with one probe per std type; an answer that needs an unknown type
  rejects (L0820) instead of guessing. `catch_unwind` checks its
  closure at body end (L0612, rustc E0277).

- Threads and poisoning (slice 3). A panic that reaches a spawned
  thread's root ends that thread: the packet keeps the payload and
  `join` returns `Err(Box<dyn Any + Send>)` (`thread::Result`). An
  unjoined panicking scoped thread makes `thread::scope` panic ("a
  scoped thread panicked") at its call after every thread ended. The
  hook line names the thread ("main", the Builder name, or
  "<unnamed>"), in both modes. A Mutex or RwLock write guard records
  whether its thread was panicking when it locked (bit 1 of the lock's
  `poison` byte) and poisons the lock (bit 0) when it drops during a
  panic that started later; read guards never poison. `lock`,
  `get_mut`, and `into_inner` then return `Err(PoisonError(..))`.
- Iterator expansions (lower/iter.rs) put each droppable local they
  make (a `vec::IntoIter`, a collected Vec) on the cleanup chain of
  the expanded call, so its values drop when a closure inside panics.

### 7.2a Unwind tables in release builds

The flags of 7.2 cost a load and a branch after every call. A release build (the
release driver, `src/cc.rs`) compiles the C with clang or zig cc, which emit unwind
tables, so it uses the platform's C++ exceptions instead (`Program::unwind_tables`,
`lust_unwind_mode` 2 in `runtime/panic.c`):

- A panic throws a private C++ type (`LustPanic` in `src/runtime/unwind.cc`, the one
  C++ unit of the build) that holds the runtime's exception record. Only lust's catch
  points catch it: `catch_unwind`, a thread's root, `main`, and drop glue that must go
  on to drop the other fields. Other C++ exceptions pass through.
- The generated units stay C, compiled with -fexceptions. A frame with drops keeps its
  droppable locals and drop flags in one struct that is a cleanup variable
  (`__attribute__((cleanup))`), and stores its ladder entry (`L.st`) before each
  statement that can unwind. When an exception passes the frame, the cleanup function
  runs the same cleanup ladder that 7.2 jumps to. A builtin that owns a value while it
  can panic (`Vec::insert`, `resize`, `retain`, `dedup_by`, `OnceLock::get_or_init`)
  keeps it in a guard (`lust_dguard` and its kin) for the same reason.
- A panic while the cleanup of an exception runs, which the same catch point would
  take, aborts before the throw ("panic in a destructor during cleanup"), as Rust
  does. A `catch_unwind` inside a destructor still catches.
- The tcc dev build keeps 7.2. One runtime serves both modes (`lust_unwind_mode`).

Tests: `EH=1 PANIC=unwind scripts/difftest.sh` and `EH=1 RELEASE=1 scripts/difftest.sh`
build every case this way (clang, clang++). `LUST_UNWIND_TABLES=0` turns it off in a
release driver build; `LUST_UNWIND_TABLES=1` turns it on for `--emit-c`.

### 7.3 Threads, TLS, atomics, sync

- Runtime: pthreads through tcclib-linked libc.
  `thread_spawn(trampoline, env_ptr, stack_size,
  name)` returns a handle id. The trampoline is the
  closure instance's slot trampoline. Env is a boxed
  closure value. Thread result: the trampoline writes
  (value slot, panic payload) into a heap cell;
  `thread_join_raw` reads it. Stack size and names
  pass through; spawn failure returns the OS error so
  `Builder::spawn` can be fallible and ts-rust's
  EAGAIN retry in `GoThread`
  (`crates/ts_goport/src/gopanic.rs:249-296`) works.
- `thread::scope`: scoped threads are normal spawns
  plus a join-all on scope exit, with the region
  model proving borrows do not escape (5.2: the scope
  fn's region param covers them). A panic in a scoped
  thread resumes in the scope after all joins, as in
  Rust.
- `Send`/`Sync` gate at check (2.7): spawn closure
  and return `Send + 'static`; scoped: `Send + 'scope`.
  Generic spawn works (bounds in std signatures),
  removing DESIGN's old "no spawn in generic code"
  limit, which ts-rust violates
  (`GoThread::spawn<F, T>` at gopanic.rs:249).
- TLS (W-TLS, `runtime/thread.c`): pthread keys only.
  No C `_Thread_local` or `__thread` in generated code
  or the runtime (7.2: tcc breaks TLS in shared
  objects). One pthread key holds each thread's block:
  a cell per `thread_local!` static the thread touched
  (found by the static's slot word, set at its first
  access from any thread) and the destructor list. Not
  one key per static: glibc clears a key's value before
  its destructor runs, and Rust's order is newest
  registration first (glibc `__cxa_thread_atexit_impl`,
  which std uses on Linux). A value that needs drop
  registers at its first access, a `const` one too.
  Destructors run at thread exit from the key's
  destructor, and for the main thread after `main`
  returns and in `process::exit` (glibc's `exit()` runs
  them for Rust std), before stdout is flushed. After
  its destructor a key is destroyed: `with` panics with
  Rust's AccessError text, `try_with` is `Err`. A
  recursive lazy init makes the inner value, then the
  outer value replaces and drops it (Rust 1.99
  `LazyStorage`, no panic). `LocalKey` is a builtin type
  with builtin methods (`check/tls.rs`, `lower/tls.rs`)
  until generic source std lands. A TLS destructor that
  panics aborts. 73 `thread_local!` uses, including
  per-thread leaked arenas (3.6).
- Atomics: types in source over C11 `stdatomic.h`
  intrinsics (3.2). Widths: bool, 8 to 64-bit ints,
  ptr, usize. Orderings map to C11 memory orders
  one-to-one, including CAS failure orderings and
  fences. Linux x86_64 evidence (K3): atomic load and
  fetch-add work under the pinned tcc, with two pthread
  workers at 100,000 relaxed increments each ending at
  200,000. That proves one path, not every width and
  ordering, and nothing on macOS. The named fallback if
  the macOS arm64 spike fails: emit the same operations
  through `__sync_*` builtins where tcc accepts them,
  and through a per-width spinlock-guarded runtime
  helper where it does not. The fallback is correct and
  slow, and it keeps the tier 1 claim honest until the
  spike runs there. `spin_loop` hint (emit
  `__builtin_ia32_pause` where tcc allows, else a
  compiler barrier; measure in the spike). Ts-rust:
  404 atomic uses in 46 files.
- Sync in source over C handles (3.2): `Mutex`,
  `RwLock`, `Condvar`, `Once`, `OnceLock`,
  `LazyLock`, `mpsc` (channel and `sync_channel`
  with disconnect semantics), `Arc`/`Weak` with
  atomic counts. Wait/notify timeouts use the time
  intrinsics. No serial-execution shortcut for
  workers: ts-rust's bind/check/emit pools
  (`program.rs` sites in INVENTORY Q3) deadlock
  without real threads.

## 8. Incremental invalidation

Today the daemon has three cases (`src/driver.rs:7-14`):
body edits are cheap, signature edits recheck name
users, everything else rebuilds. A type change in
ts-rust costs rustc 60.2 s and lust a full rebuild
(PLAN.md target table). Milestone 9 needs finer
invalidation, but the graph must be designed now or
every stage will need a rewrite to record its reads.

### 8.1 Nodes and fingerprints

A node is a pure function of its inputs with a 64-bit
fingerprint (FxHash over normalized content, never
over session ids). "Normalized" means token-level, no
positions, as `src/scan.rs` already hashes bodies and
item headers without positions.

| Node | Inputs | Fingerprint covers |
|---|---|---|
| `File(file)` | bytes on disk | raw bytes |
| `Tokens(file)` | File | token stream with trees, no spans |
| `ModTree(crate)` | mod decls in all files | module set, parents, file assignment |
| `MacroDef(def)` | Tokens | def token stream (arms, normalized) |
| `Expansion(call)` | MacroDef, input tokens, cfg, files/env read | output token trees |
| `Items(file)` | Tokens, Expansions | parsed item headers |
| `Sig(def)` | Items, Sigs it names | resolved signature: types with def hashes, generics, predicates, repr, vis |
| `LayoutOf(adt)` | Sig of adt and the adts it holds by value (generic form) | size/align function shape: field order, offsets as functions of params; concrete layouts derive at mono. A type behind a pointer or in a collection counts by identity |
| `Structure(adt)` | Sig of adt and of every adt its fields name | the same content over all of them, behind pointers too: what auto traits and derive glue answers read |
| `AssocVis(adt, name)` | the resolver's item tables | visibility and module of one inherent item (method and `Type::item` privacy) |
| `ImplSet(trait, head)` | all impl headers in the bucket, across visible crates | set of impl header hashes, sorted |
| `Binding(module, ns, name)` | ModTree, the imports and defs that decide this one name | the resolved `Res` (def disk pair, or ambiguous, or absent) for that name only |
| `MethodSet(head, name, form)` | inherent impls and trait impls that can answer this probe | candidate def list for one (Self head, method name, receiver form), in probe order |
| `Checked(def)` | Sig(def), body tokens, every node it reads (8.2) | typed side tables exist; key is the read set plus body hash |
| `BodyIR(def)` | Checked | generic IR fingerprint |
| `Instance(key)` | BodyIR(template), arg layout fingerprints, selected impl instances on edges | substituted IR fingerprint plus its cached edge list |
| `CUnit(unit)` | Instances in the unit, glue set, the unit's used-slots hash (4.2); for the table unit only, the full slot manifest hash | C text hash |
| `FailedLookup(query)` | the `Binding`, `ImplSet`, or `MethodSet` fingerprint at fail time | the same key as the query that failed |

There is no whole-module `Scope` node. A scope
fingerprint over a full binding map makes one new export
in the central prelude dirty every body in about 698
files that glob it, used or not. Reads are per name, so
adding a name dirties only the bodies that read that
name (or failed to find it).

Const values (`Const` nodes) fold into `Sig` for const
items and assoc consts: the evaluated value is part of
the signature fingerprint. A const body edit that
keeps the same value invalidates nothing downstream.
Same idea for enum discriminants.

### 8.2 Recording reads

Check, collect, and mono take a `Reads` sink. Every
cross-item query records the node it used:

- `sig_of(def)`, `layout_of(adt)`, `impl_set(trait,
  head)` at every obligation (success records the
  impl; failure records a `FailedLookup` plus the
  bucket fingerprint), `binding(module, ns, name)` at
  every path segment resolution (one read per name,
  never a whole scope), `method_set(head, name, form)`
  at every method probe in 2.10 step 2 and 3, hit or
  miss, including the inherent probes that ran before a
  trait hit, `macro_binding` in the macro namespace at
  every expansion, `checked(def)` at every call edge in
  mono, `layout(arg)` per instance arg.

This is a discipline, not a framework. Rules:

1. A stage may only read another item through a query
   fn on `Program`/`MonoCtx` that logs to `Reads`.
   Direct field pokes into other defs from check are
   banned by module privacy where Rust allows it, and
   by review where it does not.
2. The read set of a `Checked(def)` is stored with
   the result. On the next request, recompute the
   fingerprint of each read node (cheap hashes, bottom
   up) and reuse the result if all match and the body
   hash matches.
3. Failed lookups are first-class reads, with the same
   keys as successes. Adding an impl changes
   `ImplSet(trait, head)`: bodies that failed an
   obligation on that bucket recheck. Adding a def or
   an import changes only the `Binding` nodes for the
   names it exports: bodies that read or failed those
   names recheck, and no others. Adding an inherent
   method changes `MethodSet(head, name, form)`: a body
   that had picked a trait method of that name
   rechecks, because Rust now picks the inherent one (a
   probe pair that prints 1 before the inherent method
   exists and 2 after). This is distinct from a failed
   lookup: the first lookup succeeded, and its answer
   still changed. Without these reads, "add the missing
   impl" would keep failing until a full rebuild, which
   is the rule DESIGN-TS section 3 states.

Today's name-based approximation ("bodies that mention
the name", `src/scan.rs:35-38` body idents) stays as a
prefilter for signature edits in milestones 4 to 5.
The read-set mechanism replaces it incrementally:
queries land with each subsystem (traits first, since
impl edits are the painful case).

### 8.3 Edit processing

Per request, per crate session:

1. Stat and read changed files (mtime plus size, then
   hash; hash is the truth). Re-run scan on them.
2. If `ModTree` changed (mod decl edit, file added or
   removed), rebuild the module tree and the `Binding`
   nodes of affected modules. Files not reachable any
   more leave the session.
3. Re-expand only calls whose inputs changed (6.5).
4. Re-collect changed items. Compare `Sig`
   fingerprints: unchanged sigs stop propagation even
   if the item body or formatting changed. One limit:
   an unchanged unexpanded module tree does not stop
   propagation by itself. A macro def edit can add an
   item or a whole module under the same tree, so the
   `Items` and `Expansion` fingerprints are inputs to
   this step, not the tree alone.
5. Dirty marking: reverse-walk `Reads` edges from
   changed nodes. Re-run `Checked`, `BodyIR` for
   dirty defs, in parallel.
6. Mono, for builds only (`lust check` stops at step
   5): recompute edges for dirty instances from their
   cached edge lists (4.2), then walk only from dirty
   instances and roots. Only instances whose
   fingerprint changed re-emit C. Do not re-walk the
   whole instance graph per edit.
7. Recompile dirty C units with tcc, overlay-link as
   today. Base rebuild after 32 overlays or when the
   slot table outgrows capacity, as today.

Worst case stays a full rebuild, but only when the
graph says so. The milestones sequence the wins:
milestone 4 keeps today's three cases at crate scale;
milestone 5 adds `ImplSet` and failed-lookup reads
(type and impl edits stop forcing full rebuilds
within a crate); milestone 9 adds cross-crate edges
and the disk instance cache, and tunes against the
ts-rust edit benchmark.

### 8.4 Disk cache

Content-addressed, local, ignored by git (PLAN.md
decision 1). Disk forms first. Nothing session-local is
written as-is; each value translates at the write
boundary. The cache file carries a format version, and
these forms are *not* frozen interfaces: nothing
writes them before wave D, so pinning them in the
serial phase would only freeze a guess. W-DRIVER owns
the forms and may change any of them by bumping the
cache version; an old-version cache is dropped, never
migrated. The table below is the starting shape, not a
contract other packages code against.

| In memory | On disk |
|---|---|
| `DefId` | `(StableCrateHash, DefPathHash)` (1.7) |
| `Ty`, `ArgsId` | structural fingerprint: kind tag plus child fingerprints, defs in disk form. Regions in signature types keep their form (`Static`, a `Param` index, or a `Bound` index under its binder count): a stored signature must rebuild the same regions, early-bound and late-bound alike (5.5). `Placeholder` regions never reach disk; they exist only inside a proof. Only mono `InstanceKey` args erase regions (4.2). Per-crate type tables and body overlays do not align across sessions, so raw ids never cross. Read side rebuilds session ids by interning the structure into the crate owned store (2.1). |
| `Sym` | the string |
| `CtxtId` | the chain of (macro def disk pair, call-site file hash, token ordinal) up to the root |
| `FileId`, `Span` | canonical path hash plus token ordinal in the item (4.2) |
| `InstanceKey` | def disk pair plus arg fingerprints |

Key per entry: (lust version, target, profile flags,
cfg hash, graph key of 1.1, node fingerprint). Stored:

- Std crates: signature surface, generic templates, and
  prebuilt non-generic instances (3.8).
- Per instance: its mono IR, keyed by the instance
  fingerprint. Per C unit: the compiled object, keyed
  by the unit's C text (4.2). These
  are separate entries, because the backend compiles groups
  of instances, not one object per instance. A
  cached-cold build re-runs the front end (fast, and it
  must, to know the instance set), re-emits C from
  cached IR for a unit whose used slots moved, and
  links cached objects for every unit whose key held.
  The complete manifest stays stored (below) so a
  restarted daemon recovers the same slot assignment;
  storing it does not put it in any ordinary unit's
  key.
- Expansion outputs for the 20 largest macros by
  output size. The rest are cheap to redo and not
  worth disk IO.
- The slot manifest per final binary:
  `InstanceKeyHash` to slot, so a restarted daemon
  reuses `libbase.so` instead of rebuilding it, in any
  crate load order.

Not stored: user checked bodies. Serializing `Checked`
plus local tys costs more than rechecking at lust's
check speed, and it freezes an IR format early. The one
exception is the std-only generic template format
(3.8), which is versioned with the compiler and covers
shipped crates only.
Revisit the general case only if cached-cold check
profiles say the front end dominates after milestone
9's work.

Soundness rule: a cache hit must be indistinguishable
from recomputation. Every input that can change an
output is in the key: file bytes, cfg, features,
edition, env reads by builtins, build-script outputs,
shim and adapter versions, allocator choice, overflow
and debug flag state. The milestone 2 "fixed
whole-request disk cache" work owns the key list;
this section extends it per node. CI runs the
random-edit fuzzer with the cache on and compares
against fresh sessions (the fresh-session guard in
PLAN.md milestone 1). Any mismatch is a cache bug,
not a flake.

## 9. Work breakdown for parallel agents

### 9.1 Source layout

Split the flat modules into owned directories. The
split serves ownership. It is not a rewrite: files
move, contents mostly stay, in serial refactor S4,
which runs first so later serial diffs land on final
paths. `runtime.c` also splits in S4, by subsystem,
behind one `runtime.h`: one file can then have one
owner per subsystem instead of four packages editing
one C file.

```text
src/
  main.rs  client.rs  daemon.rs  protocol.rs   (driver shell)
  diag.rs                Span, Diag, rendering            [S1]
  intern.rs              Sym, FxHash                      (shared, stable)
  lexer.rs               tokens, token trees              [W-MACRO]
  scan.rs                outline scan, hashes             [W-RESOLVE]
  parser.rs              AST parse                        [AST owner, per wave]
  ast.rs                 AST nodes                        [AST owner, per wave]
  expand/
    mod.rs  match_.rs  transcribe.rs  builtin.rs          [W-MACRO]
  resolve/
    cargo.rs             cargo metadata, crate graph      [W-RESOLVE]
    modules.rs           module tree, mod loading         [W-RESOLVE]
    imports.rs           worklist, globs, visibility      [W-RESOLVE]
    cfg.rs               cfg env and strip                [W-RESOLVE]
    worklist.rs          outline loop driver (6.1)        [W-RESOLVE]
  ty/
    mod.rs               TyKind, interning, subst, normalize [W-TRAITS-CORE in A, then W-TRAITS]
    defs.rs              Defs, Generics, signatures       [W-TRAITS-CORE in A, then W-TRAITS]
    layout.rs            layout engine                    [W-CORELANG, then W-CGEN]
    consteval.rs         bounded const eval (2.13)        [W-CORELANG]
    lang.rs              lang item table                  [W-STD]
    print.rs             ty_name, type_name strings       [W-MONO]
  traits/
    index.rs             impl and method index, coherence [W-TRAITS-CORE, then W-TRAITS]
    solve.rs             obligation queue, selection      [W-TRAITS-CORE, then W-TRAITS]
    auto.rs              auto traits (2.7)                [W-TRAITS]
  check/
    mod.rs               body checking (today check.rs)   [W-CORELANG, then W-CHECK-G]
    collect.rs           signature collection (today)     [AST owner, per wave]
    obligations.rs       queue run points, 2.12 hooks     [W-TRAITS-CORE in A, then W-TRAITS]
    generics.rs          generic collect, param env       [W-TRAITS-CORE in A, then W-TRAITS]
    method.rs            method and field resolution      [W-TRAITS-CORE in A, then W-CHECK-G]
    coerce.rs            coercions, unsizing              [W-CHECK-G]
  borrowck/
    mod.rs               loans, liveness (today)          [W-BORROW]
    regions.rs           region vars, variance feed       [W-BORROW]
  ir.rs  lower.rs        IR and lowering                  [W-LOWER]
  mono/
    mod.rs               instance walk, substitution      [W-MONO]
    fuse.rs              iterator fusion                  [W-MONO]
  cgen.rs  tcc.rs        C backend (today)                [W-CGEN]
  runtime/
    runtime.h            shared C declarations            [W-CGEN]
    core.c               alloc, vec, string, float text   [W-CGEN]
    hash.c               hash table core                  [W-STD-B, W-CGEN reviews]
    panic.c              panic state, hooks               [W-PANIC]
    thread.c             spawn, TLS keys, sync cores      [W-THREADS]
  driver/
    session.rs           workspace and crate sessions     [W-DRIVER]
    graph.rs             dep nodes, fingerprints, Reads   [W-DRIVER; W-PERF from wave B]
    cache.rs             disk cache, slot manifest        [W-DRIVER]
    compile.rs           pipeline orchestration (today)   [W-DRIVER]
library/                 lust std source (3.1)            [W-STD; deps by W-DEPS]
  core/  alloc/  std/  deps/
shims/                   Rust shim crate (3.7)            [W-SHIM]
tests/  bench/           as today, plus runners in 9.3
```

Every package name used above is defined in 9.3. There
are no owner names without a package.

Shared files have exactly one owner per wave. Other
packages send small patches through that owner:

| File | Serial | Wave A | Wave B | Wave C |
|---|---|---|---|---|
| `parser.rs`, `ast.rs`, `check/collect.rs` | S3a/S3b owners | W-CORELANG | W-CHECK-G | W-BORROW |
| `ty/mod.rs`, `ty/defs.rs` | S3a owner | W-TRAITS-CORE | W-TRAITS | W-TRAITS (W-BORROW paired for variance in `defs.rs`) |
| `check/obligations.rs`, `check/generics.rs` | new in wave A (S3a hooks) | W-TRAITS-CORE | W-TRAITS | W-TRAITS |
| `check/method.rs` | new in wave A | W-TRAITS-CORE | W-CHECK-G | W-CHECK-G |
| `ty/lang.rs` | S5 owner | W-STD | W-STD | W-STD |
| `ir.rs`, `lower.rs` | S7 owner | W-CORELANG | W-LOWER | W-LOWER |
| `cgen.rs`, `runtime/runtime.h`, `runtime/core.c` | S4 owner | W-CGEN | W-CGEN | W-CGEN |
| `runtime/panic.c` | stub by W-CGEN | W-CGEN | W-CGEN | W-PANIC |
| `runtime/thread.c` | stub by W-CGEN | W-CGEN | W-CGEN | W-THREADS |
| `driver/*.rs` | S6 owner | W-DRIVER | W-DRIVER | W-DRIVER |
| one `library/` file | S5 owner | W-STD (ledger names the file) | W-STD | W-STD |

Trait work in body check does not wait for wave B.
S3a puts empty hook calls at the fixed queue run points
of 2.4 and 2.12 inside `check/mod.rs`, calling into
`check/obligations.rs`. In wave A, W-TRAITS-CORE fills
those hooks and owns `check/obligations.rs`,
`check/generics.rs` (generic Adt and fn collect, param
env), and `check/method.rs` (the MGP needs trait
candidates in method probing). W-CORELANG does not
become the merge queue for trait changes to check.

W-LOWER is one owner across waves B and C. W-CHECK-G
records captures and coercions; W-LOWER emits places,
calls, field moves, drops, and cleanup edges. W-BORROW
and W-PANIC consume that contract. They do not edit
lowering on their own.

### 9.2 Serial refactors first (keep this list closed)

These land one at a time, each by one agent, each
small, each with the full test suite green. No
parallel package starts until the serial list is in.
Execution order: S4, S0, S1, S2, S3a, S3b, S5, S6, S7.
S4 runs first because it only moves files, so later
diffs land on final paths. S4 is file moves only: the
`Session`-per-crate and `CrateKey` behavior change is
S6 work, not part of the move. Total serial cost target:
3k to 5k lines of churn. If a serial item grows past
its estimate by 2x, stop and re-split; do not let it
absorb feature work. The serial phase is mechanical.
It deletes no `Builtin` compat path and proves no
generic compilation. Each Done line says what its gate
does and does not test.

| ID | Change | Files | Size | Done when |
|---|---|---|---|---|
| S4 | Directory split per 9.1, including `runtime.c` split by subsystem behind `runtime.h`. Moves only, no logic change. `driver.rs` splits into `driver/` by file move; session behavior does not change here (S6 owns `Session` per crate and `CrateKey`). | all of `src/` (git mv) | 200-400 churn | `cargo build` and tests green. `git log --follow` works. Gate tests paths only. |
| S0 | Diagnostic registry: Appendix A ranges become the checked list. `scripts/check-explain.sh` (or its successor) fails on a new code outside the reserved ranges or on a collision with the 43 codes in use today. | `docs/errors/`, `src/explain.rs`, check script | 100-200 | Registry check green on today's codes. No new codes emitted yet. |
| S1 | `Span { file, lo, hi, ctxt }`, `FileId`, per-file line indexes. One file per crate still. | `diag.rs`, all span users (mechanical) | 400-700 | Difftest green. Diagnostics print file paths. |
| S2 | `DefId`/`DefPathHash`/`CrateId` types; slots keyed by hash; `FnId` becomes the session-local `LocalDefId`. No behavior change. | `collect.rs`, `driver/`, `cgen.rs` | 300-500 | Fuzzer green. Slot manifest round-trips. |
| S3a | Types first: `TyKind` v2 with `Adt(DefId, ArgsId)`, arg interning, `Generics`, `Binder`, `AssocEq` under its binder and the `Placeholder` region form (2.1), `Defs` skeletons behind compat helpers. Empty hook calls at the fixed 2.4/2.12 run points in `check/mod.rs`, calling stubs in `check/obligations.rs`. `Vec`/`Option`/`String` keep their `Builtin` paths. | `types.rs` to `ty/`, `check/mod.rs` hooks, `check/obligations.rs` stubs | 500-800 | Difftest green. Gate tests the representation and the hook points; it proves no generic type checking. |
| S3b | AST v2 *shapes* for all syntax of milestones 4 to 7: items (`mod`, `trait`, `type`, `const`, `static`, `macro_rules`), patterns, expressions, attributes, generics with lifetimes, `where` clauses, qualified paths. Shapes freeze here; broad parser work does not land here. Each syntax form's parser lands later with its feature owner (W-CORELANG for core syntax in wave A). Until its parser lands, a new form is a clean reject with a stable code from Appendix A, never a parse panic. | `ast.rs`, `parser.rs` (reject paths only), `collect.rs` | 500-800 | Difftest green. AST shapes compile and are frozen. Unimplemented forms reject cleanly on sampled ts-rust files. The syn-based `lust-port` item and expression count check runs per feature package as its parser lands, starting with W-CORELANG. Gate tests shapes and rejects only; it proves no type checking. |
| S5 | Lang item table, intrinsic registry (signatures and privilege checks in check and cgen), the `library/` loader, and a source path for *non-generic* std fns only. Generic std waits for the minimal generic pipeline (9.3). | `library/` skeleton, `ty/lang.rs`, `check/`, `cgen.rs` | 400-700 | A test program that calls one non-generic source std fn compiles through the loader. Gate tests loading and the registry. It does not test generic source std, and no `Builtin` case is deleted. |
| S6 | Protocol and routing: a request names a crate; the daemon routes by `SessionKey` (1.8). `driver/` gains `Session` per crate keyed by `CrateKey` (the behavior change kept out of S4). Single-file programs become a synthetic one-crate package. Add the multi-file test runner `scripts/test-crates.sh` and `tests/crates/` with fixtures that work under today's language. Cargo graph loading itself is W-RESOLVE work. | `protocol.rs`, `daemon.rs`, `driver/session.rs`, `tests/crates/` | 400-700 | `lust check file.rs` is unchanged for users. Two feature selections in one daemon stay in separate sessions (routing test). The two-file `mod` fixture is *not* part of this gate; it belongs to W-RESOLVE, which builds module loading. |
| S7 | Frozen-interface plumbing, record-only where noted: the `Reads` sink and the query fns of 8.2 with per-binding and method-set keys (recorded, not yet used for invalidation), including the frozen `Binding` query fns that wave A codes against (9.3); IR calls become terminators `Call { target, args, dest, unwind }` with `unwind: None` everywhere today; `InstanceKey` as a type; the owned type store lift of 2.1, which is the identity until generics land; the final-bin slot manifest type. No 8.4 disk forms: the cache file is versioned and W-DRIVER owns its forms (8.4). | `ir.rs`, `lower.rs`, `driver/graph.rs`, `ty/` | 500-800 | Difftest green. A grep shows no call left as an `Rvalue`. Query fns exist and tests assert that a sample body records binding and method-set reads. Gate tests recording, not invalidation speed. |

One live bug fix runs beside this list, with its own
owner: today's binary accepts NLL problem case 3
(section 11). S4 moves `borrowck.rs`, so the fix starts
right after S4 and runs in parallel with S0 to S7. It
touches borrow checking only; no serial item edits
that code, so there is no collision.

Interface freeze at the end of the serial phase.
These change only through their owner, with a note to
all package owners: `Span`, `DefId` and its disk pair,
`Ty`, `TyKind`, `ArgsId`/`TysId`, `Binder`,
`TraitRef` with bindings, `Predicate` with `AssocEq`,
param-env elaboration (2.1), the owned type store lift,
`Generics`, `Defs` queries, AST node shapes, IR
`Rvalue`, the `Call` terminator and its unwind slot,
field drop-flag shape, the runtime status values at
the FFI and shim boundary, the `Reads` query fns and
their keys (`Binding`, `MethodSet`, `ImplSet`),
intrinsic signatures, the 3.4 predicate signatures,
the receiver grammar (2.9), `layout()` output
including `niche`, the const value form (2.13),
final-bin slots and the slot manifest. Two stated
exceptions: `InstanceKey` is owned by W-TRAITS-CORE
through wave A, because the MGP may still reshape it;
and the 8.4 disk forms are not frozen at all (versioned
cache file, W-DRIVER owns them). Everyone else codes
against the frozen list. Add new variants at the end
of enums only. Never renumber.

### 9.3 Parallel work packages

Packages run in waves. Sizes are implementation lines
(compiler plus runtime plus std source in the package),
not tests. "Difftest green" means the commands in the
runner table below that the package lists, plus
`SANITIZE=1` where codegen changes, per the brief.
Focused tests only; no bulk-generated slop.

Test runners. W-DRIVER builds each runner before the
first gate that needs it. A gate that names a fixture
dir no runner can execute is not a gate.

| Runner | Runs | Oracle |
|---|---|---|
| `scripts/difftest.sh` | `tests/pass`, `tests/fail`, `tests/reject` with each compiler's defaults (panics unwind); `PANIC=abort` runs them with `-C panic=abort` on both sides | rustc with its defaults (or `-C panic=abort`) |
| `PANIC=unwind scripts/difftest.sh` | `tests/unwind/` plus panic cases in `tests/pass` | rustc with `-C panic=unwind`, overflow checks on. Needed because abort mode cannot test recovered panics, poison, or unwind drops. |
| `EH=1` with `PANIC=unwind` or `RELEASE=1` | as without `EH=1` | lust's C with unwind tables (7.2a), built by clang -fexceptions and clang++, in place of the tcc build. |
| `RELEASE=1 scripts/difftest.sh` (with or without `PANIC=unwind`) | `tests/release/` plus every `tests/pass` case | rustc and lust both with `-C overflow-checks=off -C debug-assertions=off`, a release profile's semantics: wrapping arithmetic, masked shifts, no debug assertions. |
| `scripts/test-crates.sh` | `tests/crates/*`: multi-file Cargo fixtures, each built by Cargo and by lust, stdout and exit compared. Sets target and features per fixture. | Cargo |
| `scripts/test-macros.sh` | `tests/macros/`: token compare, executable hygiene cases, both-reject cases | `rustc -Zunpretty=expanded` tokens; rustc run output |
| `scripts/test-traits.sh` | `tests/traits/`: selection, coherence, and inference cases, accept and reject | rustc accept/reject per case, with the rustc error class recorded in the fixture |
| `scripts/test-adapters.sh` | `tests/adapters/`: std and adapter semantics (specialization pull counts and capacity, sort, hash order, SmallVec spill) | rustc with pinned crate versions from ts-rust `Cargo.lock`, in abort and unwind modes |

Every runner takes a filter, has a per-case timeout,
and works with `SANITIZE=1` where it builds C. Fixture
dirs a runner cannot find fail the run; they do not
skip in silence.

Minimal generic pipeline (MGP). Wave A has one joint
gate that breaks the old bootstrap cycle. The MGP is a
thin end-to-end slice, built by W-TRAITS-CORE,
W-CORELANG, W-CGEN, and W-DRIVER together, over local
types only (no std types): one generic
Adt, one trait with an input parameter (whole trait
ref, not Self alone), one associated
equality used in a signature, one generic method call
(inherent and trait), one drop of a generic value, and
one trait that has both a concrete impl and a bounded
bare-param blanket impl, selected through a `for` loop
over a local iterator type. That last shape is the 2.4
clause-filter case (the std `IntoIterator` blanket in
local form); without it, the filter bug would first
show in wave A2 against real std. The slice runs
through collect, generic check, mono, and cgen, built
and run *through the daemon*, output compared with
rustc. Until the MGP gate passes that way, all
`Builtin` compat paths stay, and no std package
deletes a compat case. After it passes, W-STD deletes compat cases one
API group at a time, each group behind its own
end-to-end gate. State in every report which path a
test exercised: a green compat path proves nothing
about source generics.

This moves a thin slice of PLAN milestone 5 (traits
and mono) into the milestone 4 window. The alternative
(std first, traits later) cannot reach its own gate.
The orchestrator must accept the shift; 9.4 records it.

Scale gate, every wave. At each wave end, W-PERF (or
W-DRIVER in wave A) reports, on the 31k benchmark crate
and on a pinned ts-rust slice that grows per wave:
changed `Checked` bodies, instances visited,
invalidated binding and method-set queries, C bytes
emitted, dirty units, link time, and memory. The slice
report pins target, features, and reachable file set.
Line counts state which count they use: 571k
handwritten lines, 672k production-plus-generated, or
786k physical source. Edit scenarios, each timed on its
own row (body check/build, structural edit, fresh
cold, cached cold never merge): a new `pub fn` exported
through the central prelude; an inherent method added
where a trait method was in use; a type edit that
changes a niche; a macro edit that adds a generated
item; a cross-crate generic body edit; an edit that
adds one reachable generic instance (unrelated objects
must be reused, 4.2); a daemon
restart that must reuse disk objects and the slot
manifest under a different crate load order. Wave A
runs only the scenarios its features can express: the
new `pub fn` (in single-file form until W-RESOLVE
lands), the niche-changing type edit, the macro edit,
and the restart (slot manifest reuse; disk objects
once the cache exists). The inherent-method scenario,
the cross-crate generic body edit, and the
added-instance scenario need the MGP and join at the
wave A gate at the earliest, in full from wave B. A
wave A scale report that lists them as run is wrong.
Do not wait for wave D to learn that invalidation or
the instance walk eats the edit budget.

#### Wave A1 (milestone 4 core): modules, macros, core language, trait core

Six packages in parallel after the serial list. No A1
package waits for W-RESOLVE: S7 freezes the `Binding`
query fns, and wave A packages code against those fns
with today's single-file resolver behind them until
W-RESOLVE lands. W-CORELANG, W-TRAITS-CORE, and
W-MACRO fixtures stay single-file until then. When
W-RESOLVE lands, it swaps the implementation behind
the same fns; no caller changes.

**W-RESOLVE: crate graph, modules, imports, cfg, worklist.**
Owns: `src/resolve/*`, `src/scan.rs`, visibility checks
through the AST owner.
Interfaces out: `CrateGraph`, `ModuleTree`, per-name
`Binding` queries, cfg env, file set per crate, the
outline worklist driver (6.1) with W-MACRO behind the
`expand` interface. In: AST v2.
Depends on: S1, S2, S6, S7. Until W-MACRO lands, the
worklist runs with expansion disabled for macro-free
fixtures.
Work: 1.1 graph loading with per-unit features, 1.2
module loading (file rules, ambiguity, `#[path]`),
1.3 import worklist and scope priority, 1.5
visibility, 1.6 cfg strip, function-local `use`,
`const`/`static` item collection, non-generic aliases.
Tests: `scripts/test-crates.sh` fixtures (glob
collisions from 1.4, explicit import through a glob,
re-export through a private module, `pub(crate)`
edges, cfg on/off, shared file in two crates,
`#[path]`, both `x.rs` and `x/mod.rs`, two feature
selections and two targets in one daemon) plus
difftest.
Gate: `lust port scan` module findings for ts_goport
(`modules.imports`, `modules.path_attr`) each compile
in a fixture or are listed rejects; the ts-rust
`prelude.rs` shape resolves in a fixture crate. Size:
2.5k-3.5k.

**W-MACRO: token trees, expansion, builtin macros.**
Owns: `src/lexer.rs` (token trees), `src/expand/*`,
hygiene contexts. Parser changes go through the AST
owner.
Interfaces out: `expand(call, macro_def) -> token
trees` for the worklist, expansion cache, span mapping
for diagnostics. In: macro defs and bindings through
the frozen `Binding` query fns (S7), with today's
single-file resolver behind them until W-RESOLVE
lands; macro fixtures stay single-file until then.
Depends on: S1, S3a, S3b.
Work: 6.2 opaque fragments and local-ambiguity errors,
6.3 mixed-site hygiene, 6.4 builtin macros (format spec
parsing with W-STD), 6.5 caching, caps, `$crate`,
textual and path macro scopes.
Tests: `scripts/test-macros.sh`: every macro shape the
port scan lists (80 defs, 70 names at last scan),
fragment forwarding (`by_data!` shape), local
ambiguity both-reject, hygiene capture and shadowing
as executable cases, recursion caps, a disabled
`compile_error!` under cfg, a `use`-imported macro.
Gate: all three test layers green. Token compare alone
does not pass this gate. Size: 2.5k-4k.

**W-CORELANG: core language without std types; AST owner for wave A.**
Owns: `parser.rs`, `ast.rs`, `check/collect.rs` (wave
A AST owner), `src/check/mod.rs`, `src/ir.rs` and
`src/lower.rs` (wave A lowering), `ty/layout.rs`,
`ty/consteval.rs`.
Interfaces out: checked bodies and IR for the new
forms, the layout engine. In: scopes through the
frozen `Binding` query fns (S7), with today's
single-file resolver behind them until W-RESOLVE
lands; fixtures stay single-file until then.
Depends on: S3a, S3b, S7. Takes no std
types: `Box`, `Result`, `?`, and let-else are W-STD-A
work in wave A2.
Work: tuples, arrays, slices, patterns (slice, ref,
tuple, struct update), control flow (labels, `if let`
chains), enum discriminants, the const evaluator of
2.13 (non-generic form), static data emission, u128
and f32/f64 scalar paths, the layout contract of 4.4
with its gate, IR cleanup edges built with `Drop`
(scope exit and unwind share one pass; wave C adds the
runtime), the check half of the MGP. Derives are not
in this package: today's derive path stays as compat,
untouched, until W-TRAITS-CORE's synthetic impls land
and replace it. Building a second checked-forms derive
path here would be throwaway work.
Tests: difftest per feature, `tests/adapters/` layout
cases (the nested `TypeData` shape as the standalone
engine test of 4.4 over the real field-type graph,
`TypeMapper`, the pinned 4.4 generator shapes,
explicit discriminants, packed-field reference
reject), the wave A1 form of the 2.13 initializer
corpus (locally supported types only, per 2.13), the
MGP fixture.
Gate: MGP (joint) plus the layout gate of 4.4. Size:
6k-9k. The biggest wave A package; the AST-owner duty
is part of the size, not extra.

**W-TRAITS-CORE: generics, impl index, selection, mono walk.**
Owns: `src/traits/*`, `ty/mod.rs` (`TyKind`, interning,
`subst`, `normalize`) and `ty/defs.rs` (wave A),
`check/obligations.rs` (queue run points and the 2.12
hooks S3a planted), `check/generics.rs` (generic Adt
and fn collect, param env), `check/method.rs` (wave
A), `InstanceKey`, and the mono walk in
`src/mono/mod.rs` (basic form).
Interfaces out: `select(obligation) -> Selection` per
2.4, coherence per 2.6, method candidate queries,
instance discovery with cached edges. In: `Defs`,
`Binding` queries for traits in scope, through the
frozen S7 fns; single-file fixtures until W-RESOLVE
lands.
Depends on: S3a, S7.
Work: generic Adts and fns in collect (in
`check/generics.rs`), full trait-ref matching with
probe unification, the 2.4 clause
filter (provably false where clauses remove
candidates, multi-level, never selecting on a "yes"),
orphan-based coherence (2.6), param-env elaboration,
associated equalities and normalization, the narrow
impl-param binding of 2.4 step 4, derives as synthetic
impls (the one derive path; today's checked-forms
path stays compat until this lands), `Sized` and
`?Sized` basics, the mono half of the MGP. No
closures, no `dyn`, no fusion.
Tests: `scripts/test-traits.sh`: same Self with
different trait inputs, supertrait evidence, associated
equality binding, `Vec<_>` collect shape (with a local
`Vec`-like fixture type, since std `Vec` lands in A2),
integer var through `Index`, must-reject inference
(E0282 and E0283 classes), std `IntoIterator` blanket
shape plus the six ts-rust `IntoIterator` impl shapes,
the clause-filter cases (a concrete impl next to a
bounded blanket through a `for` over a local iterator
type; the multi-level `Box<[T]>` shape in local form;
two matching param-env predicates deferring), the
coherence cases (`impl<T: A> Tr` vs `impl<T: B> Tr`
with local traits and empty buckets rejects, E0119
class; the orphan positive case accepts),
`L0613` vs `L0610` split.
Gate: MGP (joint) plus the trait corpus. Size: 3k-4.5k.

**W-CGEN: C backend and runtime cores.**
Owns: `src/cgen.rs`, `src/tcc.rs`, `runtime/runtime.h`,
`runtime/core.c`.
Interfaces out: C per unit from concrete IR; slot
trampolines; runtime call emission. In: layouts
(W-CORELANG), instances (W-TRAITS-CORE, then W-MONO),
slot manifest (W-DRIVER).
Depends on: S4, S7.
Work: concrete layout emission (explicit padding,
niche-filled enums, align-16 i128), scalar helpers,
aggregate ABI and the large-return out-pointer (4.5),
fn pointer values, drop glue emission for the MGP,
the Vec growth fix (3.3), float print and parse with
the K5 fuzz gate, `alloc(size, align)`.
Tests: difftest with `SANITIZE=1`, float fuzz in
`tests/adapters/`, capacity cases, MGP run.
Gate: MGP (joint); float text byte-equal on the fuzz
corpus. Size: 2k-3.5k plus 1k-1.5k C.

**W-DRIVER: sessions, graph, slots, runners.**
Owns: `src/driver/*`, `src/daemon.rs`, `src/protocol.rs`
(after S6).
Interfaces out: crate sessions, `Reads` recording (S7)
turned into reuse for `Binding` nodes first, final-bin
slot assignment and the slot manifest, object-unit
identity (4.2), config and graph keys (1.1). In: every
stage's queries.
Depends on: S6, S7.
Work: session routing by graph key, build-script
refresh checks, std loading path (S5 artifacts), the
six test runners, restart and load-order tests.
This package is correctness plumbing from day one.
W-PERF later measures and improves it; W-PERF does not
supply missing plumbing.
Tests: driver tests (restart with disk objects,
different crate load order; one added reachable
generic instance reuses the objects of unrelated
units and rebuilds only the table unit, per 4.2;
a change to a unit's own used slots forces its C
re-emit but not a front-end redo), plus all runners
green on their starter fixtures.
Gate: MGP (joint) built and run through the daemon;
runners land before the gates that cite them. Size:
2k-3k.

#### Wave A2 (milestone 4 gate): source std, first half

Starts only when the MGP gate passes. One package,
plus AST-owner support from W-CORELANG.

**W-STD-A: core and alloc source over the generic pipeline.**
Owns: `library/core/*`, `library/alloc/src/{string,
vec,boxed,rc,borrow}.rs`, `library/std/src/{prelude,
env,io basics,path,time}`, `ty/lang.rs`.
Interfaces out: lang item defs, prelude, the intrinsic
list in use. In: MGP language support. Std source must
not use a feature before its package lands it; a
`library/README` ledger names, per file, the features
and the surface-manifest state.
Work: `Option`, `Result`, `?`, let-else support in
check (with the AST owner), `Vec`, `String`, `Box`,
then `Rc` basics. Delete `Builtin` compat cases in
staged API groups, in this order: (1) `Option` and
`Result`, (2) `Vec` and `String`, (3) `Box`. Each group
lands only when its end-to-end gate passes: difftest
green with the compat code for that group removed,
the surface manifest diff for those types (3.1), and
capacity and drop-order cases from 3.5.
Tests: difftest, `tests/adapters/` (capacity,
in-place collect after 3.4 predicates exist in basic
form), manifest diff in CI.
Gate: PLAN.md milestone 4 gate: ts-rust scanner and
JSON kernels as owned fixtures compile with byte-equal
output, through the source path, with the three compat
groups deleted. Size: 4k-6k of lust source.

#### Wave B (milestone 5): traits in full, closures, dyn, mono

Entry conditions, in order:

1. Spike K1 (compatibility, full list in section 10)
   for the wave B items: a `NodeVisitor` with stored
   `Rc<dyn Fn>` callbacks (borrowed, not `'static`
   only), `ArenaBox` with `Deref`, one blanket impl,
   `go_flags!` output types, one stored callback. The
   borrowed-visitor and higher-ranked parts double as
   spike K8: run them before broad closure work. Spike
   code is throwaway.
2. Spike K2 has *not* run yet at this point in its
   cost form; the wave A cleanup edges let K2 measure
   early at wave B end (section 10).
3. W-PERF starts part-time: it owns `Reads` after S7
   and reviews read granularity of each landed stage.

Then six packages.

**W-TRAITS: traits in full.**
Owns: `src/traits/*`, `ty/defs.rs` (wave B).
Work: auto traits in full (2.7, including the unwind
traits and the std registry), dyn compatibility checks
(2.8), the coherence disproof table at full crate
scale, operator traits, `?` conversion errors, derive
impls completed.
Tests: `scripts/test-traits.sh` extended: dyn
compatibility rejects (bare `Self` return, generic
method, assoc const, `Self: Sized` trait), auto-trait
parity probes (3.1), overlap cases from 2.6.
Gate: trait corpus plus auto-trait parity green.
Size: 2k-3k.

**W-CHECK-G: generic bodies, closures, method calls; AST owner for wave B.**
Owns: `parser.rs`, `ast.rs`, `check/collect.rs` (wave
B AST owner), `src/check/*`.
Interfaces out: generic `Checked` bodies with closure
captures and `CallTrait` evidence. In: W-TRAITS
selection, layout queries.
Work: capture analysis, `Fn` bounds and binders,
closure signature rules of 2.9 and 2.12, `impl Trait`
(arg sugar, opaque recording, auto-trait leak),
coercions and unsizing, typed receivers in full
(including `&Rc<Self>`), generic inline const
(well-formed form; per-instance eval in W-MONO),
foreign fn signatures (small; W-SHIM needs them in
wave C).
Tests: difftest closure matrix, `tests/traits/`
method ambiguity and autoderef order, one fixture per
INVENTORY closure class (adapters, std methods, user
fns, stored, `dyn Fn`), the actual
`self: &Rc<Self>` method shape from
`frontend/packagejson.rs:1092`.
Gate: closure class fixtures byte-equal. Size: 4k-6k.

**W-LOWER: lowering owner for waves B and C.**
Owns: `src/ir.rs`, `src/lower.rs`.
Interfaces out: generic IR with places, call
terminators, field moves, drops, cleanup edges. In:
`Checked` from W-CHECK-G.
Work: closure env lowering, coercion and unsizing
lowering, `dyn` calls, drop trees for fused and
unfused forms (with W-MONO), the place-holds-loan
shapes W-BORROW needs (frozen before wave C).
Tests: difftest; drop-order fixtures in
`tests/adapters/`.
Gate: IR place shapes frozen for W-BORROW; drop-order
corpus green. Size: 2k-3k.

**W-MONO: instantiation, vtables, fusion, predicates.**
Owns: `src/mono/*`, `ty/print.rs`.
Interfaces out: concrete IR per instance, vtable
statics, `TypeId` table, `type_name` strings. In:
generic IR, W-TRAITS selection on concrete types,
layouts, slot manifest from W-DRIVER.
Depends on: W-CHECK-G, W-LOWER, W-TRAITS.
Work: 4.1-4.3 in full: cached instance edges, inline
const per instance, glue instances, the 3.4 predicate
evaluation, fusion in the staged order of 4.3
(starting unfused), recursion limits in build mode
(never in check mode).
Tests: `tests/adapters/` fusion corpus (150 or more
cases: side-effect counts, drop prints, capacity,
early exits; zip both-sides rule, skip and step_by
pull counts) run fused and with `LUST_NO_FUSION=1`;
the generic inline-const assert case of 2.13,
evaluated per instance (its well-formed check gates
in W-CHECK-G);
recursion build-reject vs check-accept pair.
Gate: `Rc<dyn Fn>` callback fixture byte-equal;
fusion corpus dual-run green; reachable instance
count and cached-walk time recorded (scale gate).
Size: 4k-6k (fusion 3k-4k of it).

**W-STD-B: traits-heavy std and containers.**
Owns: `library/alloc` collections, iterator adapters
in `library/core`, `fmt` full surface, `Rc`/`Weak`/
`RefCell`/`Cell`/`Cow` completion, `runtime/hash.c`
(W-CGEN reviews).
Interfaces out: adapter def list for fusion (by
`DefId`, frozen), the specialization list of 3.4 with
one unfused difftest each. Depends on: W-TRAITS,
W-CHECK-G.
Tests: `tests/adapters/`: sort (stable and unstable,
comparator log; caught comparator panics are not a
wave B gate, because W-PANIC lands in wave C: they
run there, see W-PANIC),
capacity through collect and extend, specialization
parity on the unfused path, surface manifest diff and
auto-trait parity for the new types, and the
source-std `RefCell` static initializer case of 2.13
(first stage that supports it).
Gate: manifest and parity green; `Rc<RefCell<T>>`
fixture set passes. Fx map order gate follows the K4
audit outcome (3.5), not a blanket claim. Size: 5k-8k
lust source, 0.8k-1.2k C.

**W-DEPS: adapter crates.**
Owns: `library/deps/*`.
Work: 3.6 table, including `SmallVec<[T; N]>` in its
real shape. Depends on: W-STD-B containers.
Tests: `scripts/test-adapters.sh` per crate, pinned
versions.
Gate: per-crate exactness table green. Size: 3k-5k.

Step A lifetimes (`'static`, `'_`, 5.1) land at wave B
tail by the W-BORROW agent (1k-2k), with the static
well-formedness checks of 5.1. Named-region gates stay
distinct from step A in every report.

#### Wave C (milestones 6 and 7): regions, threads, panics

**W-BORROW: regions over the loan engine; AST owner for wave C.**
Owns: `src/borrowck/*`, `parser.rs`, `ast.rs`,
`check/collect.rs` (wave C AST owner, for region
syntax), variance feed paired with W-TRAITS in
`ty/defs.rs`.
Depends on: W-LOWER frozen place shapes. Starts from
the 5.6 corpus, not from features. NLL problem case 3
is already fixed as milestone 1 work (section 11);
the corpus keeps it as a regression case.
Work: 5.2 NLL live ranges with universal regions,
5.3 variance, 5.4 drop check with the std may-dangle
flag, 5.5 early/late-bound split, lifetime turbofish
reject, placeholder leak check.
Tests: `tests/fail` and `tests/reject` corpus of 5.6,
difftest positive fixtures.
Gate: `Parser<'a>`, `JsonDecoder<'a>`,
`RuleContext<'a, 'c>`, a borrowed `NodeVisitor`
callback, and the `FileRef` guard-backed borrow shape
compile; the full 5.6 corpus rejects in both lust and
rustc. Size: 3.5k-6k.

**W-PANIC: explicit propagation.**
Owns: `runtime/panic.c`, the unwind terminator use in
lowering (through W-LOWER), cgen call-site shape
(through W-CGEN).
Entry: the semantic corpus first (7.2). The cost
spike K2 runs after the corpus passes, before
W-THREADS builds on it.
Depends on: wave A cleanup edges, W-MONO instances.
Does not depend on any can-panic fixpoint; there is
none (7.2).
Tests: `PANIC=unwind scripts/difftest.sh` over
`tests/unwind/`: helper calls in a destructor, a
second panic caught inside `Drop`, nested catches,
poison, `resume_unwind` hook silence, `UnwindSafe`
reject (E0277 class), drop-on-unwind print order,
the two catch-boundary cases of 7.2 (`panicking()`
false and no poison inside a successful catch; a
mutex locked and released inside a destructor during
an outer panic stays unpoisoned) in the first gate,
abort-mode run of the same dir where semantics allow.
The wave C integration gate also runs the caught
sort-comparator panic fixtures from W-STD-B here,
because they need both the sort code and unwind.
Gate: semantic corpus byte-equal in unwind mode; K2
numbers recorded. Size: 2k-3.5k.

**W-THREADS: std thread and sync surface.**
Owns: `library/std/src/{thread,sync}`,
`runtime/thread.c`.
Depends on: W-PANIC (join payloads, poisoning),
W-BORROW (scoped borrows), auto traits.
Tests: difftest in both panic modes: parallel
bind-shaped fixture (scoped workers over files, mpsc
results, shared `Arc<Mutex>`) with equal sorted
output; `Rc` across `spawn` rejects; the source-std
`Mutex::new` and `OnceLock::new` static initializer
cases of 2.13, array-repeat form included (first
stage that supports them).
Gate: as stated in Tests. Size: 3k-5k (mostly lust
source).

**W-SHIM: rustc shim and platform surface.**
Owns: `shims/` crate, lust-side foreign fn crates for
rustix/nix/signal/zlib/time/jemalloc-ctl,
`lust port prepare` shim build, allocator selection
(3.7).
Depends on: foreign fns (W-CHECK-G, wave B), W-PANIC
boundary rules.
Link rule: system linker or loader with a cdylib,
first and by default (3.7). W-SHIM does not wait on
K6. K6 gates only the optional libtcc staticlib path.
Tests: one end-to-end syscall path (file watch event
or signal) in a fixture; a recovered panic *inside*
the shim (the K6 semantic case, through the system
linker path) in `tests/unwind/`; TLS, callback, and
allocator-ownership cases; jemalloc arena assign plus
4 MiB align fixture.
Gate: all of the above on Linux; macOS rows recorded
as open until K3 runs there. Size: 2.5k-4k plus Rust
shim code.

#### Wave D (milestones 8 and 9): port and speed

**W-PORT: ts-rust core CLI port.**
Owns: no compiler files by default. Owns the port
tree. Compiler gaps found here are filed to the owning
package with a fixture, not fixed ad hoc.
Depends on: waves A-C gates.
Gate: PLAN.md 8a, baseline tests byte-equal, release
through Cargo at equal speed. The gate names its exact
target, features, reachable files, and release recipe.
Do not replace ts-rust's protected output comparisons
with a smaller chosen subset in silence; a smaller
scope is a stated scope cut. Size: 3k-6k tool and fix
lines.

**W-PERF: invalidation depth and cold speed.**
Owns: `driver/graph.rs` and `cache.rs` (paired with
W-DRIVER), read-set coverage reviews, instance disk
cache depth, front-end profiles, the backend bake-off
harness. Part-time from wave B (above), full-time in
wave D.
Gate: PLAN.md milestone 9 measurements on the ts-rust
edit loop, cold rows separate, scale gate scenarios of
9.3 all green. Size: 4k-8k.

**Async (8b): a decision, then maybe a package.**
No W-ASYNC exists until the port reaches ATA and a
decision gate picks its form. At that gate, compare
two costed options on the one real user
(`project/ata/ata.rs`, about 2.5k lines, with its own
`block_on` and waker): (a) a state-machine lowering
(3k-6k lines: executor, wake delivery, borrowed
suspension, cancellation and drop, pinning, panic
behavior), (b) a reviewed rewrite of that one IO-bound
file with no release speed impact. The default is the
rewrite, unless a second project needs async. A
borrowed-future spike (K9) runs before either choice.
If the lowering wins, define W-ASYNC here in full
before work starts, with its own executable gate in
`tests/pass` and `tests/unwind/`. Until then, 8b makes
no async coverage claim. It depends on W-BORROW
(borrows across suspension) and W-PANIC either way.

### 9.4 Milestone map

| Milestone (PLAN.md) | Packages | Gate (short) |
|---|---|---|
| 4 Rust core (13k-20k) | Serial, wave A1, wave A2. Includes the MGP: a thin traits and mono slice pulled from milestone 5. | Scanner and JSON kernels byte-equal through source std. Macro gate (scan-listed defs) green. |
| 5 Traits, closures, dyn, Rc (25k-38k) | K1/K8 spikes, W-TRAITS, W-CHECK-G, W-LOWER, W-MONO, W-STD-B, W-DEPS, step A lifetimes | Compatibility spike set byte-equal. Fusion corpus dual-run. Surface and auto-trait parity. |
| 6 Lifetimes (5k-9k) | W-BORROW | Three named fixtures compile. 5.6 corpus rejects, NLL case 3 included. |
| 7 Threads and panics (9k-15k) | W-PANIC, W-THREADS, W-SHIM | Parallel bind. Recovered panic byte-equal in unwind mode. Shim panic recovered through the system linker. |
| 8 Port (3k-6k) | W-PORT plus filed fixes; async decision at 8b | Core CLI baselines pass. |
| 9 100x (4k-8k) | W-PERF | Measured 100x edit loop; cold rows stated. |

Package sizes sum inside the PLAN.md ranges, with the
MGP slice counted in milestone 4. Gates cite port-scan
output at gate time for feature counts. Numbers in
this document (66 macros, 168 lifetime types in older
counts; 80 macro defs and 194 lifetime types in the
last scan) drift, so no gate hard-codes them.

### 9.5 Coordination rules

1. One owner per file at a time (brief rule). The
   table in 9.1 is the ownership map. Cross-owner
   edits go through the owner or land as a paired
   commit with the owner as reviewer.
2. Frozen interfaces (9.2) change only in a dedicated
   commit that touches no logic, so rebases stay
   mechanical. Announce in the wave channel before,
   not after.
3. Std source and compiler land features in lockstep
   per the std feature ledger (W-STD). A std file
   that needs a feature lists it; the feature package
   adds a fixture from that file.
4. Every package keeps its listed runners green on its
   branch tip before asking for merge, and says which
   path (compat or source) each std test exercised
   until the compat group in question is deleted. The
   orchestrator rebases packages in dependency order
   at wave end, then runs the full gates.
5. Perf: the scale gate of 9.3 runs at every wave end.
   In addition, each wave B and later package records
   check and build time on the 31k crate plus its
   fixtures, before and after. A regression over 10%
   needs a note or a fix in the same package. Cold
   numbers use interleaved runs and medians (brief
   rule for the shared box).

### 9.6 `unsafe` in lust's own code

lust's own Rust code uses `unsafe` only by opt-in, and
every use is documented. (This is about the compiler
itself. `unsafe` in the source that lust compiles is
the PLAN.md decision 3 opt-in; see 3.1.)

1. A C or libc call (libtcc, `fork`, `waitpid`,
   `flock`, `signal`, `pipe`) may use `unsafe`. Each
   block has a `SAFETY:` comment.
2. Any other `unsafe` needs a waiver in the table
   below: the site, what the `unsafe` does, and why
   safe code does not do the job. The site has a
   `SAFETY:` comment with the proof and names this
   section.
3. A waiver goes when its code goes.

| Site | What it does | Why not safe code |
|---|---|---|
| `src/pool.rs`, `run` | Erases the lifetime of a phase's job (`&(dyn Fn() + Sync)` to `'static`), so the persistent workers can call it. `EndPhase` runs on every exit path of `run`, a panic included: it stops new workers from joining and waits until no worker is inside the job, so no use outlives the borrow. | Scoped threads are safe but start new threads in every phase: a cold check of the 31k-line crate started 149 threads with them and 23 with the pool (review of land-t2). |
| `src/image.rs` (front image, `LUST_FRONT_STATE`) | The global allocator wraps mimalloc: in an image process every block comes from one fixed-address arena, a new block's bytes past its layout (mimalloc's size-class slack, `mi_usable_size`) are zeroed, and a free of a block restored from an image zeroes it instead of freeing it. `save` reads live blocks through mimalloc's block visitor and writes them out with `writev` (no allocation while it walks); `load` maps the saved pages back at their addresses and turns the saved root pointer into the `Box<Roots>` it was. The image is used only by the same build at the same addresses (build id and address anchors checked, randomization off), and only when nothing else is mapped in its window. A background save (`LUST_FRONT_SAVE=background`) forks only after every other thread has stopped, so the child's heap and its locks are consistent; the child calls only `setsid`, `dup2`, the calls that put it at idle priority (`setpriority`, `sched_setscheduler`, and `ioprio_set` by `syscall`), the calls that watch the build process so the save runs on 4 threads while the build lives (`pidfd_open` by `syscall`, `getppid`, `poll`, `close`), the drops of what the image leaves out (the parked cc step, the kept programs no later build reuses), the save, one write of its result line, and `_exit`. When the image is too scattered for a base, the child instead clears close-on-exec on the state lock's descriptor (`fcntl`) and execs the same command to rebuild the image cold (`compact_exec`); that process sets close-on-exec again (`compact_lock`), so the lock passes to it with no gap in which another build could take it. Packed layers (`LUST_FRONT_ZSTD=1`) call the system's libzstd through `dlopen` and `dlsym` (function pointers cast to zstd.h's own signatures, every length checked against the layer's section table) and unpack straight into anonymous mappings of the image's runs (`fill`: each worker copies only the pages of its own sections, and the newest-layer table is disjoint), storing a hash of each page placed in raw memory outside the heap; a save reads a resident page (pagemap) to compare its hash (`changed_runs`). Such a save also packs the fns' C texts into zstd frames that stay in the heap (`pack_bytes`, `cgen::pack_texts`); `unpack_bytes` checks that a frame unpacks to its recorded length. `LUST_FRONT_RESTORE=memfd` unpacks them into `memfd_create` files that the regions then map privately, as raw layer files. | A one-shot build cannot keep a daemon's session (4.4 GB of heap on tsgo, hundreds of types with `Arc` sharing) any other way: a serializer would be thousands of lines that every type other packages add must follow. The image restores exactly the memory a daemon keeps, with no per-type code. |


## 10. Spikes, risks, and rejected options

Spikes are time-boxed, throwaway, and end in a number
or a yes/no. Schedule them at wave entries, not after
trouble.

| # | Spike | When | Question | Fallback |
|---|---|---|---|---|
| K1 | Compatibility spike, full PLAN list: a visitor with stored callbacks, `ArenaBox` with `Deref`, a blanket impl, `go_flags!` output, a scoped thread, a recovered panic, one C shim, one borrowed async task | Wave B entry for the trait, dyn, and closure items; thread, panic, shim, and async items as bounded probes at wave C and D entries | Do 2.4, 2.8, and 4.2 hold on real shapes? Each non-B item ends in a written yes/no with probe output, or a stated reason it moved. No item drops in silence. | Widen the solver only where a probe points. No backtracking. |
| K8 | Borrowed visitor and higher-ranked callback spike (the hard half of K1, split out so it cannot hide) | Before broad closure work in wave B | Does an `Rc<dyn Fn(&T) + 'a>` callback work with a real borrow check, including the leak check of 5.5? A `'static`-only stand-in cannot answer this. | Restrict closure bounds and record the codemod class; do not weaken the region check. |
| K3 | tcc platform check: `stdatomic.h` widths and orderings, TLS, `__int128` | Linux x86_64: done. Atomics load and fetch-add work (two workers, 200,000 total); `_Thread_local` works in an exe and is broken in a shared object (7.2); `__int128` does not parse. macOS arm64: before any tier 1 claim there, with the exact pinned tcc build. | Can the C backend express 3.2, 4.4, and 7.3 as written, per target? | Already the plan: pthread keys, 2-word i128 with align 16, the named atomic fallback in 7.3. |
| K6 | Rust shim link semantics | Decided for the default path on Linux: tcc links a Rust staticlib but a panic caught inside it aborts; the system `cc` link runs (3.7). Remaining spike, only if someone wants the libtcc staticlib path: prove a recovered panic, TLS, threads, callbacks, and allocator ownership through the libtcc API itself, on both targets. | Can libtcc ever be a final link for Rust shims? | The system linker with a cdylib is the supported path. W-SHIM does not wait on this spike. |
| K4 | FxHasher audit (replaces "build an exact table first") | One day, before W-STD-B claims map-order support | Build ts-rust with a perturbed FxHasher through `[patch]`; run the baselines. Equal bytes? | Equal: a deterministic table suffices for the port. Unequal: the diff names the sites; fix those sites or build the exact table per 3.5 (per-target group width). Keep the result in the adapter README either way. |
| K5 | Float printer fuzz | Wave A (W-CGEN) | Byte-equal on 10M random bit patterns? | Swap Ryu variant; keep fuzz in CI at lower count. |
| K2 | Panic propagation cost, after semantics | After the `tests/unwind/` corpus passes; at wave B end on wave A cleanup edges if they allow it, else in W-PANIC | C bytes and run time vs abort (7.2 thresholds) on dense-drop code, not only on a visitor fixture | Per-fn setjmp with cleanup registry. |
| K7 | Annotation burden count | After 2.4 lands, on port scan | How many ts-rust sites hit `L0610` (annotation) vs `L0613` (impl param), counted after macro expansion and dependency classification? | Annotations are codemods. A large `L0613` count (order of 200) reopens only the step 4 binding rules, with the same no-search limit. Counted before 2.4 lands, the number measures the algorithm, not the code. |
| K9 | Borrowed async task spike | At the 8b decision gate (9.3) | Can one ATA-shaped borrowed future run under the proposed lowering, with suspension, wake, cancel, and panic behavior? | The rewrite option of 9.3. |

Order rules: K3 (Linux) and the K6 default-path
decision are already evidence, before std and runtime
ABI work starts. Panic *semantics* (7.2 corpus) come
before K2 cost. K8 comes before broad closure work.
K7 comes after 2.4. No spike moves later than the
package that consumes its answer.

Risks that can change the plan, with first evidence:
restricted lifetimes growing toward full Rust (the
5.6 corpus passing but real ts-rust modules still
needing rewrites); mono C size on real modules
(measured per the scale gate in 9.3; a byte share
alone proves nothing, 4.2);
adapter drift on upstream version bumps (pins make it
loud, not silent); daemon memory at 786k lines (1.8
eviction note; measure at milestone 8); the layout
engine meeting a shape where its size differs from
rustc (the gate in 4.4 turns that into a reject or a
fix, never a waiver).

Rejected, with reasons on record:

- Dictionary passing for generics (VERIFY G: saves
  about 10 ms per 31k lines at real density, costs a
  second codegen path, still needs the instance walk
  for rustc's post-mono errors).
- One-time macro expansion as source (PLAN.md decision
  7: 29k lines of boilerplate to maintain).
- Serial worker execution in place of threads
  (INVENTORY Q3: 2.8x to 3.2x slower, and watch/LSP
  block on IO threads anyway).
- Handle conversion for borrowed fields (DESIGN-TS
  option C: callback and guard shapes do not map; also
  slows the release binary).
- A metadata (rlib-like) crate format for user crates
  before milestone 9 (in-process signature surfaces
  cover the port; a format freezes too much too
  early). The std-only generic template format of 3.8
  is the one exception, because std cannot change
  inside a lust version.
- Instance sharing by layout class (4.2: the key is
  not a correctness proof, and VERIFY G puts the gain
  under 10%).

## Appendix A: diagnostic codes

Audit first. The compiler emits 43 codes today
(`grep -rhoE 'L[0-9]{4}' src/` at revision 2, each with
a doc in `docs/errors/` and a row in
`src/explain.rs:9-50`). Their meanings do not change.
Revision 1 of this document reused several of them by
accident. The used set:

| Codes in use | Area today |
|---|---|
| L0001 | syntax error |
| L0101-L0107 | names, types, fields, methods, arity, duplicates |
| L0110-L0119 | type mismatch, inference, trait not implemented, operators, callable, match, casts, recursion, literal range, bad range bounds |
| L0120-L0122 | break/continue, assignment target, `mut` under a ref |
| L0130 | no `main` function (not an import cycle) |
| L0201-L0203 | refs in fields, lifetime elision, lifetime syntax not supported |
| L0301-L0312 | borrow checker: move, assign, borrow conflicts, lifetime of values (not macros) |
| L0401-L0405 | user macros, attributes, derives, `unsafe`, `async` not supported |
| L9001 | feature not supported yet |

Free ranges are therefore L05xx up. All new codes in
this document live there. `tests/fail` files key on
codes, so a collision silently retargets a test. S0
(9.2) makes this table a checked registry before any
new code is emitted. The registry is
`docs/errors/REGISTRY.md`, checked by
`scripts/check-codes.sh`; this appendix is the
rationale, the registry is the enforced list.

| Range | Area |
|---|---|
| L0501-L0509 | Modules and imports (L0501 import cycle does not settle, L0502 ambiguous module file, L0503 module file not found, L0504 generated name changes an earlier resolution) |
| L0510-L0519 | Visibility |
| L0520-L0529 | cfg and attributes (L0520 unknown cfg name, L0521 unknown attribute) |
| L0530-L0539 | Crate session (L0530 unsupported edition, L0531 unsupported deny-level lint) |
| L0601-L0609 | Types and aliases (L0601 alias cycle) |
| L0610-L0619 | Traits and inference (L0610 type annotations needed or type must be known, L0611 selection overflow, L0612 no impl, L0613 impl parameter not known from trait inputs, L0615 overlapping impls) |
| L0620-L0629 | Associated items (L0620 GAT) |
| L0630-L0639 | Const eval (L0630 outside the bounded evaluator or step cap, L0631 non-const call in a const or static initializer) |
| L0640-L0649 | Std surface (L0640 std item declared but not yet implemented) |
| L0650-L0659 | Layout (L0650 `offset_of!` on a default-repr type, L0651 reference to a packed field, L0652 unsupported layout form) |
| L0701-L0709 | dyn compatibility (L0701, with the offending item named) |
| L0710-L0719 | Binders (L0710 nested higher-ranked binder) |
| L0720-L0729 | Methods and receivers (L0720 ambiguous method, L0722 unsupported receiver type; plain "no such method" stays L0104) |
| L0730-L0739 | Regions and drop check (L0730 drop check, L0731 explicit lifetime turbofish arg, L0732 placeholder region escapes) |
| L0801-L0809 | Macros (L0801 expansion caps, L0802 unknown macro, L0803 include file not found, L0804 proc-macro dependency, L0805 local ambiguity) |
| L0810-L0819 | Foreign and shim boundary |
| L0820-L0829 | Core syntax forms (added by S3b: no range above covers core expression, pattern, and statement syntax). L0820 is the S3b parser reject for those forms. |
| L9001 | Unsupported prototype feature (existing). New work must not add L9001 sites for planned features; use the ranges above. |


## 11. Review responses

Revision 1 got two reviews, both "request changes":
sol (`/tmp/lust-wt/reviews/arch-sol.md`, 17 blocking
items) and Opus (`/tmp/lust-wt/reviews/arch-opus.md`,
11 blocking items). I re-ran the rustc probes from
both review dirs with rustc 1.99, edition 2024, and
re-ran the tcc shim and TLS binaries. Every load
bearing claim below held as the reviewers stated it,
except one detail noted at Opus B4. This section is
the checklist the orchestrator verifies against.

Revision 2 (the result of round 1) then got two
round-2 reviews, both "GO WITH THESE FIXES": Opus
(`arch-r2-opus.md`, items N1-N4 plus a list for S0-S7
and A1) and sol (`arch-r2-sol.md`, items A-G plus a
"changes before work starts" list). The round-2
tables are at the end of this section. I verified each
claim with rustc 1.99, edition 2024 before I changed
the text (probes in `/tmp/arch-r2-probes/`): layout
sizes, the local `IntoIterator` shape, both coherence
directions (E0119 for two bounded blankets over a
generic `T`; accept for the orphan positive case),
call-site macro path lookup, `panicking()` and poison
in the three guard cases, E0038 for a non-receiver
`&Self`, closure sizes 0 and 1, and E0425 for an
unqualified outer-module name. Every claim held. Where
a round-2 row and a round-1 row conflict, the round-2
row wins; the round-1 tables stay as history.

### Live rule-zero bugs in today's lust

These are bugs in the current compiler, not in this
document. Route them to bug-fix agents; do not wait
for the milestones that touch the same area.

1. **Lust accepts NLL problem case 3.** The program in
   5.2 (`first_or_push`) builds with today's lust and
   prints `1`. Rustc rejects it with E0502 (verified
   with both compilers in this revision). Fix as
   milestone 1 work: add the case to `tests/fail`,
   then fix loan liveness for loans under a universal
   (return) region. W-BORROW later keeps it as a
   regression case in the 5.6 corpus.

That is the only live accept-side bug either review
proved against today's binary. The other probes test
features lust does not have yet (traits, dyn, macros),
where lust rejects, which the subset rule allows; or
they test rustc or tcc behavior the design must match.

### sol: blocking items 1-17

| Item | Action |
|---|---|
| 1. Layout observable; missing enum niche; tag width | Fixed in 4.4: strict size/align contract, general niche computation, niche-filled enums, tag width from discriminant range and repr ints, real nested `TypeData` shape in the gate, `offset_of!` on default-repr rejected (L0650), packed-field reference rejected (L0651). The 112/192-byte size estimate is not used as a fact; the gate measures the real shape. |
| 2. Match the whole trait ref; assoc equalities; binders; param env | Fixed in 2.1 (bindings on `TraitRef`, `AssocEq`, `Binder`, param-env elaboration) and 2.4 (full-ref probe). Probe matches sol's `Tr<u8>`/`Tr<u16>` case (re-ran: prints `1 2`). |
| 3. Lifetime turbofish accepts E0794 | Fixed in 5.5: early/late-bound split is computed; all explicit lifetime turbofish args reject (L0731), the smaller first step sol proposed. Placeholder leak check added. Probe re-ran: E0794 confirmed. |
| 4. dyn checks; `&Rc<Self>` receiver | Fixed in 2.8 (full dyn compatibility, bare `Self` return included; probe E0038 re-ran) and 2.9/2.10 (recursive receiver grammar; ts-rust shape at `packagejson.rs:1092` verified, 159 uses). Supertrait auto traits on dyn in 2.1/2.8. |
| 5. Import fixpoint; re-export visibility; mod ambiguity | Fixed in 1.2 (L0502) and 1.3 (one worklist retries explicit imports through globs, with the `TypeMapperKind` chain verified; binding visibility separate from lookup path; re-ran sol re-export probe). |
| 6. Macro ambiguity; opaque fragments; expansion order | Fixed in 6.1 (interleaved worklist, cfg first), 6.2 (opaque fragments with `ident`/`lifetime`/`tt` exceptions, L0805 local ambiguity), 6.3 (mixed-site hygiene, executable gate). Both probes re-ran (forward prints 4; ambiguity errors). |
| 7. Panic flag; nested catch in Drop; UnwindSafe | Fixed in 7.2 (in-flight exception split from unwind depth, saved outer exception, nested catch by `gen`, hook and poison rules) and 2.7 (unwind traits). Probes re-ran: nested Drop catch prints `after true true`; `catch_mut` fails E0277. |
| 8. Const eval too small; static eligibility | Fixed in 2.13 (bounded evaluator over the three cited ts-rust shapes, static data path, L0631 for the E0015 case; probe re-ran). One owner named. |
| 9. Stable sort; RawVec formula | Fixed in 3.3 (driftsort/ipnsort port, no introsort; min capacity 8/4/1 by size, exact reserve, ZST capacity; layout probe re-ran and matches). |
| 10. Zip fusion needs both sides | Fixed in 4.3 (start unfused; both-sides predicate rule; one recognition boundary at mono) and 3.4 (source `Zip` uses the same predicate). Probe re-ran: filter-left runs the closure 3 times, plain map 2. |
| 11. Dep graph: candidate sets; per-name reads | Fixed in 8.1-8.3 (`Binding` and `MethodSet` nodes, every probe recorded, inherent-method addition rechecks; probe pair prints 1 then 2, re-ran). Macro-edit propagation fixed in 8.3 step 4. |
| 12. Disk-stable keys; slot space; span remap | Fixed in 1.7 (disk pair), 4.2 (one slot space per bin, manifest in object keys, token-ordinal locations), 8.4 (disk form table, IR vs C-unit keys split). |
| 13. Std generic templates missing | Fixed in 3.8 (signature surface plus serialized generic templates plus non-generic instances; recheck-on-load as the measured fallback). |
| 14. Bootstrap cycle; missing owners | Fixed in 9.2-9.3 (serial phase deletes no compat; MGP joint gate before staged deletes; W-CGEN and W-DRIVER explicit; one lowering owner; per-wave shared-file table in 9.1). |
| 15. Gates unrunnable; diagnostic collisions | Fixed in 9.3 runner table (unwind mode, crates, macros, traits, adapters) and Appendix A (43 current codes audited; new codes in L05xx-L08xx). Recursion check-vs-build split in 4.1. |
| 16. Cargo config omitted from keys | Fixed in 1.1 (full resolver input as graph key, per-unit features, build-script refresh, edition after classification and target filtering). |
| 17. tcc-linked shim cannot catch its panic | Fixed in 3.7 and K6: system linker with a cdylib is the first supported path; libtcc staticlib only after the semantic spike. Binaries re-ran: `cc` link prints the caught result, tcc link aborts. |

### sol: non-blocking items

| Item | Action |
|---|---|
| Defer instance sharing | Fixed in 4.2: sharing removed for milestones 4-8; a proof bar is stated for milestone 9. |
| Checked identity for `Any` | Fixed in 2.8: structural key, checked id table, collision stops the build, `'static` kept. |
| Pin auto-trait exceptions | Fixed in 2.7 (per-trait tables, `PhantomPinned`, std registry) and 5.3 (variance rows for `&mut`, `*const`, `*mut`). |
| SmallVec real API | Fixed in 3.6: `SmallVec<[T; N]>` with the `Array` trait; `MaybeUninit` as the one supported union shape in 4.4. Caller line verified. |
| Honest intrinsic list | Fixed in 3.1 item 1 and 3.2: signatures and privilege frozen, no count; permitted shipped crates named. |
| One schema for type args | Fixed in 2.1: `ArgsId` vs `TysId` split by name; `Bound` region added; `subst` split from `normalize`. |
| No instance walk in `lust check` | Fixed in 4.1: check stops at generic check; build walks. The policy is stated as rustc parity, so no benchmark is needed to justify it. |
| Budget discovery at scale | Fixed in 4.2 (cached edges, walk from dirty only) and the 9.3 scale gate (real counts recorded per wave). |
| Measure panic cost on dense-drop code | Fixed in 7.2: K2 fixture list now names RefCell guards, Rc captures, sort comparators, iterator short-circuits; old percentages marked as estimates, not data. |
| Pin reachability and counts | Fixed in 9.3 scale gate and 9.4: target, features, file set, and which line count (571k/672k/786k) each report uses. |

### sol: calls on the 7 open items, and 9.2/9.3 suggestions

| Item | Action |
|---|---|
| Call 1: no sharing keys yet | Agreed. 4.2. |
| Call 2: predicate-only impl params | Agreed on the diagnosis, and the narrow fix from Opus call 2 is in 2.4 step 4. Leftovers are `L0613` with no turbofish hint. K7 counts `L0610` and `L0613` apart, after expansion. Probe re-ran (the `Item = U` shape proves). |
| Call 3: hashbrown fidelity, per-target width | Partly agreed, sequenced with Opus call 3: 3.5 keeps the exactness requirement and the per-target pin list (16-byte x86_64, 8-byte aarch64; std-internal hashbrown is the Fx oracle), but K4 audits first. The port may run on a deterministic table only under a passed audit, stated in the adapter README. |
| Call 4: tcc facts, Linux only | Agreed and recorded in 7.3 and K3. TLS-by-pthread-keys is the only plan on both targets; an atomic fallback is named for arm64. macOS stays an open spike row. |
| Call 5: reject tcc staticlib default | Agreed. 3.7 link rule. |
| Call 6: edition 2024 only | Agreed, with the scope rule (selected units only) and def-edition fragments in 1.1 and 6.2. |
| Call 7: async thin | Agreed. 9.3 wave D turns it into a decision gate plus K9; no 8b coverage claim before a full W-ASYNC exists. |
| Suggestion 1: smaller serial phase | Done in 9.2 (S5 non-generic only, S6 routing only, compat kept, module fixture moved to W-RESOLVE). |
| Suggestion 2: freeze missing interfaces | Done: S7 plus the freeze list in 9.2, including the call-terminator move (`src/ir.rs:81` today). |
| Suggestion 3: one AST/collect owner | Done: 9.1 table; worklist driver has one owner (W-RESOLVE) with W-MACRO behind one interface. |
| Suggestion 4: minimal generic pipeline first | Done: the MGP joint gate in 9.3, with the exact contents sol listed. |
| Suggestion 5: W-CGEN and W-DRIVER explicit | Done in wave A1. |
| Suggestion 6: one lowering owner; runtime split | Done: W-LOWER across B and C; `runtime/` split in 9.1; `ty/defs.rs` and `ty/lang.rs` owners named per wave. |
| Suggestion 7: runner commands over fixture names | Done: runner table in 9.3; each Done cites commands. The named fixture shapes (nested `TypeData`, borrowed visitor, `&Rc<Self>`, `FileRef`, predicate-only impls, caught second panic) appear in W-CORELANG, W-CHECK-G, W-BORROW, W-TRAITS-CORE, and W-PANIC gates. |
| Suggestion 8: spikes earlier | Done in section 10 order rules (K3, K6 decision, K8, panic semantics first). |
| Suggestion 9: narrow first-pass optimization | Done: unfused and unshared start (4.2, 4.3); fusion staged by adapter. |
| Suggestion 10: scale gate per wave | Done in 9.3, with sol's six edit scenarios and separate cold rows. |

### Opus: blocking items B1-B11

| Item | Action |
|---|---|
| B1. Selection and inference | Fixed in 2.4 (probe the full trait ref, param env first, one candidate confirms and binds, defer rules) and 2.12 (type-must-be-known list). Probes re-ran: `idx` prints `1 18446744073709551615`, `infer2` accepts, `infer1` fails E0282. |
| B2. Coherence rejects std and ts-rust | Fixed in 2.6: full-ref unification plus the local/fundamental disproof as a table lookup. The six ts-rust `IntoIterator` impls verified at the cited lines. |
| B3. Std surface parity | Fixed in 3.1: rustdoc-JSON manifest, `L0640` stubs, auto-trait parity probes, W-STD gates in 9.3. |
| B4. Specialization replacement | Fixed in 3.4 (three closed mono predicates) and 4.3 (zip both-sides rule, skip and step_by pull rules). One correction to the review: `step_by(2).count()` runs the closure 4 times on Opus's 4-item probe, but my re-run at lengths 5 and 6 gives 5 and 6. So 4.3 states the pull rule (every item up to the last yielded one is pulled), not a fixed count. In-place collect keeps capacity 100 (probe re-ran). |
| B5. Region check accepts more than NLL | Fixed in 5.2 (universal regions, exact live-range rule) and 5.6 (corpus). Live bug listed above; verified with today's lust binary. |
| B6. Layout vs size asserts | Fixed in 4.4 (field order by alignment, enum niche filling, tag from discriminant range, shape-generator gate, `type_name` in 3.5). Partly rejected: "offsets of default-repr types do not need to match" is not safe, because a program can print `offset_of!` (sol's layout probe prints offsets 0 and 9). Lust instead rejects `offset_of!` on default-repr types (L0650) and matches sizes and alignments everywhere it accepts a type. |
| B7. Macro order for cfg and imports | Fixed in 6.1 (interleaved worklist, E0659 time-travel rule). |
| B8. Coarse reads, global mono walk, global can-panic | Fixed in 8.1-8.3 (per-binding reads, method-set reads), 4.2 (cached edges, dirty walk), 7.2 (no can-panic fixpoint in daemon builds; global counter fast path). |
| B9. tcc TLS in shared objects | Fixed in 7.2 and 7.3: no C TLS; global counter plus pthread keys. Probe re-ran: the `.so` sees the exe's write (3, then 77). Also covers macOS by construction. |
| B10. Work breakdown | Fixed in 9.1-9.3 and Appendix A: AST v2 covers all syntax in S3, W-TRAITS-CORE in wave A, W-STD after the MGP, every named owner has a package, S7 builds the frozen plumbing, codes moved. |
| B11. Resolution details | Fixed in 1.2 (non-`mod.rs` search dir, `program.rs:28` verified; both-files error; `#[path]` bases), 1.3 (std prelude layer, scope priority table, local `core` module), 1.6 (`target_vendor`, `default`, `rustfmt::skip`, `ignore`, `should_panic`), 6.4 (`line!`, `file!`), 1.1 (lints read from manifests, `unsafe_code` enforced, other deny lints reject). Counts verified by grep, including 32 `#[default]` uses. |

### Opus: non-blocking items 1-14

| Item | Action |
|---|---|
| 1. Dropck too strict for std | Fixed in 5.4: std-only may-dangle flag on the same impls as real std. Probe re-ran (`Vec<&String>` case accepts). |
| 2. Early-bound lifetimes | Fixed in 5.5 and 2.9: the split is computed; early-bound params are `FnDef` args, late-bound become binders. |
| 3. Auto traits leak through opaque | Fixed in 2.11, with a `spawn` test in the gate. |
| 4. Edition 2024 drop scopes | Fixed in 3.5 drop-order item (all three rules named, with tests). |
| 5. Hash byte streams and group width | Fixed in 3.5 (0xff suffix, length prefix, discriminant as `isize`; width 16 vs 8 by target). |
| 6. Panic payload type and `Location::file` | Fixed in 3.5 and 4.2 (span remapping); unwind harness mode in 9.3. |
| 7. Features per unit from Cargo | Fixed in 1.1; cfg-set equality is testable per unit. |
| 8. Std generic IR on disk | Fixed in 3.8 (serialized templates; recheck fallback measured at the W-DRIVER gate). |
| 9. `lust_dev` only in shipped crates | Fixed in 1.6, with `check-cfg` declared. |
| 10. Methods from param env and dyn with no import | Fixed in 2.10 step 2. |
| 11. Sorting | Fixed in 3.3 (port driftsort and ipnsort; total-order panic; no C introsort). |
| 12. Copy from real std | Fixed in 3.1 (stated policy for RawVec, sort, fmt, float text). |
| 13. Numbers drift | Fixed in 6.5, 9.4, and the W-MACRO gate: all counts cite port-scan output at gate time. |
| 14. Obligation queue timing | Fixed in 2.4 (fixed run points only). |

### Opus: calls on the 7 open items, and 9.2/9.3 suggestions

| Item | Action |
|---|---|
| Call 1: no sharing in milestones 5-8 | Agreed. 4.2, including the `f64`/`u64` ABI point. |
| Call 2: narrow impl-param fix now | Agreed. 2.4 step 4; K7 only after B1 lands. |
| Call 3: hash audit over exact table in 5 | Agreed as sequence; final exactness kept per sol call 3. 3.5 and K4. |
| Call 4: tcc facts on Linux | Agreed and recorded. K3; macOS stays open and does not block the no-TLS design. |
| Call 5: skip libtcc staticlib; use cdylib | Agreed for the default path. Partly differs from sol, who wants the API proved: the spike stays, but it gates only the optional path (K6). W-SHIM does not wait. |
| Call 6: edition 2024; move the code | Agreed. Edition error is L0530; L0112 keeps its meaning. |
| Call 7: async defer, prefer the file rewrite | Agreed. 9.3 wave D decision gate with the rewrite as default, K9 before either option. |
| Serial 1-6 (S4 first, AST v2, S5 cut, S7, free code ranges, crates harness) | All done in 9.2 (execution order S4, S0, S1, S2, S3, S5, S6, S7; S3 splits past 1.2k lines; counts checked against `lust-port`). |
| Parallel 1 (wave A1 with W-TRAITS-CORE) | Done. W-CORELANG takes no std types and owns the layout engine. |
| Parallel 2 (W-STD after trait core) | Done as wave A2 behind the MGP. The milestone shift is stated in 9.3 and 9.4 for the orchestrator to accept. |
| Parallel 3 (one owner for cgen, runtime, driver) | Done, with one change of shape: `runtime.c` splits by subsystem (sol's form), so W-PANIC and W-THREADS own their files in wave C while W-CGEN owns `runtime.h` throughout. Closure lowering sits with W-CHECK-G records and W-LOWER emission (9.1 table), which keeps one lowering owner. |
| Parallel 4 (cleanup edges in wave A) | Done: W-CORELANG builds them with `Drop`; runtime and hooks stay in wave C; K2 can measure at wave B end. |
| Parallel 5 (more std gates) | Done: manifest, auto-trait parity, unfused specialization parity in W-STD gates. |
| Parallel 6 (trait oracle corpus) | Done: W-TRAITS-CORE gate lists the must-reject and `IntoIterator` cases. |
| Parallel 7 (NLL corpus first; fix the bug now) | Done: corpus in 5.6; the live fix is routed above as milestone 1 work, not held for W-BORROW. |
| Parallel 8 (spikes: K1 full, K4 audit, K6 drop, K3 done) | K1 full list restored with per-wave probes; K4 is the audit; K6 is not dropped but demoted to an optional-path gate (see call 5); K3 Linux recorded as evidence. |
| Parallel 9 (W-PERF part-time from wave A/B) | Done: scale gate owner is W-DRIVER in wave A, W-PERF from wave B, owning `Reads` review. |
| Parallel 10 (gates cite scan counts) | Done: W-RESOLVE and W-MACRO gates cite scan findings; 9.4 states the rule globally. |

### Round 2: Opus items N1-N4 and the S0-S7/A1 list

| Item | Action |
|---|---|
| N1. 2.4 cannot select through the std `IntoIterator` blanket | Fixed in 2.4: a *provably false* check (binds nothing, shared depth cap 64 and cycle set, recursive through candidates, so the two-level `Box<[T]>` case works) and a clause filter in step 3 that drops a candidate only when one of its trait-predicate where clauses is provably false for the concrete Self. Never selects because clauses said yes; unknown stays unknown and defers (step 6). The filter records `ImplSet` reads (8), so a later impl rechecks bodies that filtered on an empty bucket. The same selection path serves trait candidates in 2.10 step 2. The shape is in the MGP (9.3) and in W-TRAITS-CORE tests. Probe: a local trait with one concrete impl and one bounded blanket prints 7 under rustc; `for` over `Box<[i32]>` and `Vec<u8>` accept. |
| N2. Three 4.4 layout rules give wrong sizes | Fixed in 4.4. Variant layout is a struct that starts with the tag, other fields smallest alignment first, ties in declaration order; enum size is the largest variant rounded up to the enum alignment. The false "(Box, bool) fits in 16 by small fields last" sentence is deleted. A struct or tuple takes the niche with the most free values, tie by layout order. Layout choice is now a rule: smaller size, then more free niche values, then tagged. Tag widening into padding is stated (non-blocking item, done too). The three shapes (`A(u8, u32)` = 8, `TypeMapper`-like = 16, `Option<Option<S>>` = 16) are pinned in the 4.4 gate by name. My probes add `(u8, u64, u8)` = 16, `(u32, u64)` = 16, `(u16, [u8; 3])` = 6; all match the new rule and break the old one. |
| N3. Wave A1 is a chain on W-RESOLVE | Fixed in 9.3: S7 freezes the `Binding` query fns; wave A packages code against them with today's single-file resolver behind them until W-RESOLVE lands; W-CORELANG, W-TRAITS-CORE, and W-MACRO state this in their In/Depends lines and keep fixtures single-file until then. No A1 package lists W-RESOLVE as a dependency. |
| N4. Wave A ownership gaps and overlaps | Fixed in 9.1 and 9.3. W-TRAITS-CORE owns new files `check/obligations.rs` and `check/generics.rs` plus `check/method.rs` in wave A; S3a plants empty hook calls at the fixed 2.4/2.12 run points in `check/mod.rs`. `ty/mod.rs` (TyKind, interning, `subst`, `normalize`) goes to W-TRAITS-CORE in wave A. The ownership table and the tree in 9.1 name all three files. |
| N4. Derives built twice | Fixed: W-CORELANG's "derives as checked forms" item is removed. Today's derive path stays as compat, untouched, until W-TRAITS-CORE's synthetic impls land. Stated in both packages. |
| S0-S7/A1 item 1: split S3 now | Done in 9.2: S3a (TyKind v2, args, `Generics`, `Binder`, `AssocEq`, `Defs` skeletons, hook points) and S3b (AST v2 shapes frozen; parsers land with feature owners; clean rejects until then). See also sol's matching cut below. Execution order is S4, S0, S1, S2, S3a, S3b, S5, S6, S7. |
| S0-S7/A1 item 2: remove 8.4 disk forms from S7 and the freeze list | Done: S7 no longer defines disk forms; 8.4 carries a cache format version, states the forms are not frozen, and gives them to W-DRIVER; the 9.2 freeze list drops "every disk key form in 8.4". `InstanceKey` is owned by W-TRAITS-CORE through wave A, since the MGP may reshape it. |
| S0-S7/A1 item 3: give the live NLL bug an owner | Done in 9.2: the fix starts right after S4 (which moves `borrowck.rs`), runs in parallel with S0 to S7, and touches borrow checking only. |
| S0-S7/A1 item 4: two matching param-env predicates | Done in 2.4 step 1: defer (rustc E0283), with the `T: From<u8> + From<u16>` example. Probe confirms rustc rejects the ambiguous form instead of picking one. |
| S0-S7/A1 item 5: name the wave A scale-gate scenarios | Done in 9.3: wave A runs the new `pub fn` (single-file form until W-RESOLVE), the niche-changing type edit, the macro edit, and the restart; the inherent-method, cross-crate generic body, and added-instance scenarios join at the MGP at the earliest and run in full from wave B. |
| S0-S7/A1 item 6: N1 shape in the MGP, N2 shapes in layout fixtures | Done: MGP carries a local concrete-plus-blanket trait selected through a `for` over a local iterator type (9.3); the 4.4 gate pins the three N2 shapes by name. |
| B11 wording: 1.3 lexical scope searches outer modules | Fixed in 1.3: lexical scope is locals, block items up to the enclosing fn, then the current module only; it never searches outer modules (E0425 probe). The wider enclosing-module rule is stated as the `use`-path rule only. |

### Round 2: sol items A-G and "changes before work starts"

| Item | Action |
|---|---|
| A. Header matching is not selection (2.4, 2.6) | Fixed in 2.4 (the provably-false check and clause filter; same row as Opus N1) and 2.6. Coherence now states the orphan rule in full: disproof needs a concrete local Self (or a fundamental wrapper of one, or a local trait with a concrete Self) plus no possible downstream impl. A bare param Self is never disprovable, and an empty impl bucket alone proves nothing for a generic Self. The `impl<T: A> Tr for T` vs `impl<T: B> Tr for T` pair with local traits and no impls is an overlap (`L0615`, rustc E0119, probed). The orphan positive case (`impl Tr for MyType` next to `impl<T: A> Tr for T`, `A` and `MyType` local) is a worked accept case (probed). Both cases are in W-TRAITS-CORE tests. |
| B. Item paths resolve at the call site (6.3) | Fixed in 6.3: locals, labels, lifetimes, and generic params resolve at the definition site; ordinary item paths resolve at the call site; `$crate` is the only def-site path form; items a macro defines land in the invoking module. The unconditional "every token gets the expansion ctxt" rule is replaced: metavariable tokens keep their spans and ctxts (6.2), only macro-written tokens get the expansion ctxt. Probe: `helper()` returning 1 at the def site and 2 at the call site prints 2. |
| C. Layout algorithm misses its contract (4.4) | Fixed in 4.4: niches are chosen by free value count with the pinned tie rule (see N2 row); the niche-filled candidate also checks that every other variant's fields fit outside the niche scalar (`Pointer`/`Byte` enum = 16, probed); an explicit repr that fixes the tag or field order (`repr(int)`, `repr(C)`, `repr(packed)`) turns the niche candidate off, `repr(align)` alone does not (probed: `#[repr(u8)]` = 16, `#[repr(align(8))]` = 8). A supported-shape rule is now stated as a grammar: `layout()` returns `L0652` for any type outside it, the generator enumerates the grammar under stated bounds, and a new form enters only when grammar, generator, and engine change together with a green gate. All of sol's probe shapes are pinned in the gate. |
| D. Gates that need later waves (2.13, 9.3) | Fixed in 2.13, 4.4, and 9.3. Wave A1 gates use only locally supported types: the 2.13 A1 corpus uses local stand-ins, and the nested `TypeData` shape runs as a standalone layout-engine test over the real field-type graph (no source `Box`, no lifetime support). Source-std versions gate at their first supported stage: `RefCell` static with W-STD-B (B), `Mutex`/`OnceLock` statics with W-THREADS (C), the generic inline-const case with W-CHECK-G/W-MONO (B). Caught sort comparator panics move from W-STD-B to the wave C integration gate in W-PANIC. Each moved gate states its stage in its Done line. The MGP stays the A2 entry condition. |
| E. A catch boundary is not an active panic (7.2) | Fixed in 7.2: `catch_depth` is recorded in thread state apart from `unwind_depth`; catch entry raises only `catch_depth`; `unwind_depth` rises only while a panic or its cleanup is active, so `thread::panicking()` is false inside a successful catch. Guards record `panicking()` at acquisition and poison only on the false-to-true transition, which covers all three probed cases (successful catch: no poison; locked before the panic: poison; locked during an outer panic's destructor: no poison). Both catch-boundary probes are in W-PANIC's first gate (7.2, 9.3). The contract is fixed now; the implementation stays in wave C. |
| F. One new slot invalidates every cached object (4.2, 8.4) | Fixed in 4.2, 8.1, and 8.4: a unit keys on its *used-slots hash*, the `(InstanceKeyHash, slot)` pairs its own emitted code uses, its own entries included. The table unit alone keys on the full manifest hash and rebuilds when the table grows. The complete manifest stays stored for restart recovery (8.4). Gate, owned by W-DRIVER: add one reachable generic instance and show unrelated objects are reused while only the table unit rebuilds. The same scenario joins the 9.3 scale gate from the MGP on. |
| G. Interfaces before the S3/S7 freeze (2.1, 2.8, 4.5) | Fixed in 2.1: `Region` gains `Placeholder(u32)` for the 5.5 proof (distinct from every region, never unifies, never stored); `AssocEq` stays under its original `Binder` (`AssocEq(Binder<AssocEqData>)`), matched under the binder in 2.4 step 1 and 2.5; the `dyn` principal trait ref is stored under its `Binder`, bindings included, for higher-ranked `Fn`. Disk forms preserve signature regions (8.4). Fixed in 2.8: the non-receiver `&Self` allowance is removed; `Self` outside the receiver is E0038 (probed, `Box<Self>` argument included), while the trait's own `dyn` type in an argument or return stays legal (probed). Fixed in 4.5: the closure value is exactly its captures under the plain struct layout (sizes 0 and 1 probed); the trampoline lives in the vtable and call metadata. `ty/mod.rs`, interning, and substitution are assigned to W-TRAITS-CORE in A1 (9.1, 9.3). |
| Before work starts: S4, S0, S1, S2 can start; keep S4 to file moves | Done in 9.2: S4 is moves only; the `Session`-per-crate and `CrateKey` behavior change moves to S6, whose row now states it. |
| Before work starts: fix G before the freeze; A, B, C, D, F before their owners start | Done in this revision: G is in 2.1/2.8/4.5 ahead of S3a/S7; A, B, C, D, F are contract text in 2.4/2.6, 6.3, 4.4, 2.13/9.3, and 4.2/8.4 ahead of A1. |
| Before work starts: keep the MGP small; compat paths until it runs through the daemon | Done in 9.3: the MGP is local types only (one generic Adt, whole trait inputs, one equality, inherent and trait method calls, one drop, plus the clause-filter shape), and its gate now reads "built and run through the daemon", with all compat paths kept until it passes that way. |
| Before work starts: cut broad parser work from S3 | Done in 9.2 (S3b row): AST shapes freeze in S3b; each syntax parser lands with its feature owner; unimplemented syntax is a clean reject with a stable code, never a parse panic. The syn count check moves to the package whose parser lands, starting with W-CORELANG. |
| Before work starts: fix E in the contract now, probes in W-PANIC's first gate | Done: see row E. Implementation stays in wave C. |
| Before work starts: keep fusion and instance sharing off | No change. 4.2 (no sharing in milestones 4 to 8) and 4.3 (start unfused) already state both cuts; round 2 changes nothing there. |
