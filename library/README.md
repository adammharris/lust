# Lust std in source: the feature ledger

Std is lust source in three shipped crates, plus adapter crates for
dependencies (docs/ARCH.md sections 3.1 and 3.6). This file is the
ledger: what exists, what is declared but has no body yet, and what
waits for a later wave. Keep it current when a row moves. The
machine-checked tables are in `src/ty/lang.rs`; the loader is
`src/stdload.rs`.

## How std loads in S5

- The driver pays for std only when user source can mention a source
  std fn (a byte scan for the triggers in `STD_FNS`). Normal compiles
  do not parse std at all.
- On a hit, the loader parses and checks the shipped module files as
  their own crates, once per daemon session (the result is cached in
  the session). A check failure in shipped source, a missing required
  lang item, or a registry row with no matching source fn is a
  compiler installation error, not a user diagnostic.
- Checked non-generic std fns are spliced into the user compile under
  mangled names, in a source range the checker knows belongs to the
  shipped crate. Intrinsic privilege keys on that provenance, never
  on names user code can write (section 3.1 item 1).
- Generic std rides the generic pipeline: the Option and Result
  methods are source (see below). String and Vec stay builtin until
  W-STD moves them.
- `LUST_STD_SRC=<dir>` makes the loader read module files from
  `<dir>/std/src/` instead of the copies built into the compiler
  (the section 3.8 override, for std authors). Std is otherwise
  immutable inside one session.

## Crates

Adapter crates in `deps/` follow `src/resolve/adapters.rs`: each has a
`Cargo.toml` that pins the exact upstream version, the adapter format,
the upstream features it implements, and its exact-layout types.

| Crate | State in S5 | Next owner |
|---|---|---|
| core | Skeleton: lib.rs, intrinsics.rs (signature mirror). No items. | W-STD |
| alloc | Skeleton: lib.rs only. String/Vec stay builtin. | W-STD |
| std | `process::exit` in source, over the `exit` intrinsic. The platform crate (`platform.rs` root, below). | W-STD, W-SHIM |
| deps/rustc-hash | Adapter for 2.1.2: `FxHasher`, `FxBuildHasher`, `FxSeededState`, and the map and set aliases over std's maps (deps/rustc-hash/README.md). | W-DEPS |
| deps/indexmap | Adapter for 2.14.0: `IndexMap` and `IndexSet` in source over the hashbrown 0.17 table (deps/indexmap/README.md). | W-DEPS |
| deps/smallvec | Adapter for 1.15.1: `SmallVec<A>` over a Vec with upstream's logical capacity and drop order (deps/smallvec/README.md). | W-DEPS |
| deps/memchr | Adapter for 2.8.2: byte and substring search in source (deps/memchr/README.md). | W-DEPS |
| deps/xxhash-rust | Adapter for 0.8.15: `xxh3` over the C core (deps/xxhash-rust/README.md). | W-DEPS |
| deps/ryu-js | Adapter for 1.0.2: `Buffer::format` for f64 over the runtime JS printer (deps/ryu-js/README.md). | W-DEPS |
| deps/num-traits | Adapter for 0.2.19: `ToPrimitive` with the f64 impl (deps/num-traits/README.md). | W-DEPS |
| deps/num-bigint | Adapter for 0.4.6: `BigInt` parse, print, pow, conversions (deps/num-bigint/README.md). | W-DEPS |
| deps/bumpalo | Adapter for 3.20.3: the Bump subset of leak_arena.rs with upstream's chunk bookkeeping (deps/bumpalo/README.md). | W-DEPS |
| deps/anyhow | Adapter for 1.0.104: `Error` over a boxed `dyn Error` of upstream's wrapper values, `Context`, `Chain`, and the macros, with upstream's texts (deps/anyhow/README.md). | W-DEPS |
| deps/bitflags | Adapter for 2.13.2: upstream's source, with a generic field type in place of the per-call `InternalBitFlags` (deps/bitflags/README.md). | W-DEPS |

## The std platform crate (W-SHIM)

`library/std/src/platform.rs` is a second std crate, loaded the other
way: the resolver adds it to the session as a lust-owned dependency
named `std` when a file can name a platform module (a byte scan for
`std::{` and `std::<module>` over `STD_PLATFORM_MODULES`, except
`std::env::args` and `std::process::exit`/`abort` alone;
`resolve::worklist::mentions_std_platform`). Then:

- A written `std::<module>::<item>...` path, a `use` of it, and an
  alias of the module (`use std::io; io::stdout()`) resolve into the
  crate's modules. For `io`, `fs`, `path`, and `ffi` every item path
  does (a name the crate lacks is an unresolved path); for `env` and
  `process` only items the crate defines do, and the others keep the
  compiler's std handling (`env::args`, `process::exit`).
- Its files have the `std` shipped-crate privilege (intrinsics) through
  the resolver's adapter record. Its types are foreign to user crates:
  the orphan rule and the inherent-impl rule apply as in rustc.
- No type of it answers layout queries (no exact-layout list).
- `write!` into an `io::Write` value passes `format_args!` as an
  `Arguments` value, which in lust is the formatted text (a
  `lust_String`). `io::Write::write_fmt` writes it with one
  `write_all`. A user writer type that relies on that default is
  rejected (L0641, check/platform.rs): std would call its `write` once
  per format piece.
- Unstable std items carry a `__` prefix (`ErrorKind::__Uncategorized`);
  `Debug` prints std's name. User code that names one is L0104
  (check/platform.rs `hidden_variant`).
- `OsStr` and `Path` are unsized newtypes (`struct Path { inner: OsStr }`
  over `[u8]`): the compiler lays them out as their field
  (`cgen::CTy::Unsized`, a fat value with the newtype's own glue), and
  shipped std source may turn `&[u8]` into `&OsStr` and `&OsStr` into
  `&Path` (check/mod.rs coercion). They are `?Sized` everywhere a
  `str` is.
- `process` is `process_os.rs` (`#[path]`): `process.rs` is the
  compiler's own std source for `exit`.

| Module | State | Test |
|---|---|---|
| `io` | `Error` (Os, Simple, SimpleMessage, Custom over `&str`/`String`), `ErrorKind` (all 44 kinds, std order, the Linux errno table), `Result`, `Write` (`write`, `flush`, `write_all`, `write_fmt`, `by_ref`) for `Vec<u8>`, `&mut W`, `Stdout`, `Stderr`, their locks, `Sink`; `stdout`, `stderr`, `sink` | tests/pass/std_io_error.rs, std_io_write.rs, tests/fail/std_io_*, tests/reject/std_io_write_user_type.rs |
| `ffi` | `OsStr` (`new`, `to_str`, `len`, `is_empty`, `as_encoded_bytes`, ASCII case, `to_os_string`, Debug, Eq, Ord), `OsString` (`new`, `push`, `into_string`, `clear`, `capacity`, Deref to `OsStr`, From `&str`/`String`). No `to_string_lossy` (std returns `Cow`), no `Hash` (no user `Hasher` bound yet) | tests/pass/std_ffi_osstr.rs |
| `path` | `Path` and `PathBuf`: std's Unix `Components` parser (front and back), `parent`, `file_name`, `file_stem`, `file_prefix`, `extension`, `join`, `push`, `pop`, `set_file_name`, `set_extension` (std's separator panic), `with_*`, `starts_with`, `ends_with`, `strip_prefix`, `ancestors`, `iter`, `display` (std's Utf8Chunks rules), component-wise `==`/`Ord` against `Path`, `PathBuf`, `str`, `String`, `OsStr`; `exists`, `is_file`, `is_dir`, `metadata`, `read_dir`, `canonicalize`. `next_back` is inherent (no user `DoubleEndedIterator` yet); no `Hash` | tests/pass/std_path.rs, std_path_user_trait.rs, tests/fail/std_path_*, tests/reject/std_path_* |
| `env` | `var`, `var_os`, `VarError`, `vars`, `vars_os`, `args_os`, `current_dir`, `set_current_dir`, `temp_dir`, `current_exe` | tests/pass/std_env.rs, tests/fail/std_env_* |
| `fs` | `read`, `read_to_string`, `write`, `create_dir`, `create_dir_all`, `remove_file`, `remove_dir`, `remove_dir_all`, `rename`, `canonicalize`, `exists`, `metadata`, `symlink_metadata` (`Metadata`, `FileType`, `Permissions` with std's Debug), `read_dir` (`ReadDir`, `DirEntry`). No `File`/`OpenOptions` yet | tests/pass/std_fs.rs, tests/fail/std_fs_*, tests/reject/std_fs_write_array.rs |
| `process` | `id`, `exit` | tests/pass/std_fs.rs (id), tests/fail/std_process_id_type.rs |

## Source std fns (`STD_FNS` in src/ty/lang.rs)

| Path | Body | Notes |
|---|---|---|
| `std::process::exit` | library/std/src/process.rs | Over intrinsic `exit` (`lust_exit`: flush, then libc exit). Test: tests/pass/std_process_exit.rs. |
| `std::process::abort` | Declared, no body | A call rejects with L0640 (declared surface, section 3.1). Body needs the abort runtime hook; W-STD. |

## Option and Result methods (library/core/src/{option,result}.rs, W-STD-A)

The enums stay compiler-known lang types; their inherent methods are
core's impl blocks (`impl<T> Option<T> { .. }`, `impl<T> Option<&T>`,
`impl<T, E> Option<Result<T, E>>`, and so on), closure methods
included. There is no builtin version left.

- Load: `STD_LANG_METHODS` (src/ty/lang.rs) lists the method names.
  A compile that names one after a `.` or `::` (or splices a std
  source module, whose bodies call them) splices both files whole.
  The splice text is constant inside a session, so the daemon's
  reused chunks and instances do not move. `lust check` never checks
  their templates (std load's tests do); a build checks one when mono
  makes its first instance. A program whose only generics are these
  methods skips the discovery recheck of bodies that name none.
- Scope: the methods see no user name (`STD_MODULE`; the resolver
  rewrite skips them), so a user `Result` alias or `struct E` cannot
  change them. A user type named `Option` or `Result` shadows std's,
  as in Rust.
- Check: an `Option`/`Result` receiver probes these impls like a
  generic user Adt's. Two impls that both fit an open receiver
  (`copied` on `Option<_>`) reject as ambiguous (rustc E0034).
- Panics: core's messages; `#[track_caller]` where core has it
  (unwrap, expect, unwrap_err, expect_err, unwrap_or_else), so a
  panic reports the caller's location.
- `const fn` exactly where core 1.99 has it stable; `consteval`
  evaluates the const ones by name.
- `as_deref` and `as_deref_mut` are core's `T: Deref` impl written
  once per std `Deref` type lust has (String, Vec, Box, `&T`, `&mut
  T`; no `Option<String>::as_deref_mut` yet): lust has no `Deref`
  impls for its builtin types. A user `Deref` type rejects, and so
  does an `Option<_>` whose payload is still open (rustc accepts it).
- Not here yet (a call rejects): `iter`,
  `iter_mut`, `into_iter`, `as_slice`, `as_mut_slice`, `as_pin_ref`,
  `as_pin_mut`, the `unsafe` unchecked unwraps, and path forms
  (`Option::map(x, f)`, `.map(Option::unwrap)`). `?` stays the
  compiler's desugaring.

## Std source modules (`STD_MODULES` in src/stdmods.rs, W-STD-C)

Whole std modules in source, generic code included, and overlays: a
source module that holds only some items of a std module whose other
items stay compiler-known (`core::marker::PhantomData` next to the
`Send`/`Sync` lang traits; a path walks into an overlay only for a name
it defines). When a compile can mention one (a row's trigger word, such
as `time` or `PhantomData`), the
driver routes it through the resolver and the loader splices each file
as a hidden inline module after the user text. The resolver binds the
hidden module nowhere and walks the row's std paths into it, so imports,
privacy, impls, and const items are the normal module machinery. Types
defined there are std types: user inherent impls and orphan impls on
them reject (L0616), and layout queries on them reject (L0652), because
std's niche fields (`Nanoseconds`) are plain integers here. Rules for
these files: stable items only, `const fn` exactly where std has it,
std's panic messages, `#[track_caller]` exactly where std has it, a
`//@ <std path>:L:C` marker (rustc's location) or `//@ never` on each
panic site outside a `#[track_caller]` fn (src/stdloc.rs; the std
platform crate follows the same rule), and `Self::` in associated const
values.

| Std paths | File | Items | Notes |
|---|---|---|---|
| `core::time` | library/core/src/time.rs | `Duration`, `TryFromFloatSecsError` | Every stable method and op; exact Debug (precision, `+`, width, fill, align through the `fmt_align` intrinsic). No `Sum` impls yet (user `Sum` impls are not supported). |
| `core::marker`, `std::marker` (overlay) | library/core/src/marker.rs | `PhantomData` | Zero-sized; acts as holding `T` for auto traits, unused-param checks, and borrowck variance (`Program::is_phantom_adt`); impls with no bounds on `T`. `Hash` in source (writes nothing); `Debug` is compiler glue (src/cgen/fmt.rs) for a `T` whose `type_name` lust prints. No `T: ?Sized`. |
| `core::ops`, `std::ops` (overlay) | library/core/src/ops.rs | `ControlFlow` | The stable methods and derives. `?` is the compiler's (`try_expr` in check, `try_into` in lower): `Break(b)` returns `Break(b)` unconverted. The operator traits, ranges, `Deref`, and the `Fn` traits stay compiler-known. |
| `core::cell`, `std::cell` (overlay) | library/core/src/cell.rs | `OnceCell`, `LazyCell` | Value in a plain `Option<T>`, written through `&self` only by the `once_init` / `once_take` builtins (std source only, L0642 elsewhere). `!Sync`, `Send` as std, invariant in `T`. `OnceCell::into_inner` is not `const` here. |
| `std::sync` (overlay) | library/std/src/sync.rs | `LazyLock` | Built on W-THREADS's thread-safe `OnceLock` (compiler-known, as `Mutex` and the rest of `std::sync`); `get_or_init` runs the init closure once and only it takes `F`. `static X: LazyLock<T> = LazyLock::new(|| ..)` works: the closure becomes a hidden fn (src/expand/lazy.rs) and a fn pointer const value. `LazyLock: Sync` is structural (std asks `F: Send`). A static inside a fn body does not see std source types yet (L0102). |
| `alloc::collections`, `std::collections` (overlay) | library/alloc/src/collections.rs | `BTreeMap`, `BTreeSet`, `VecDeque`; modules `btree_map` (`Entry`, `OccupiedEntry`, `VacantEntry`, iterator aliases), `btree_set`, `vec_deque` | Sorted `Vec` storage with std's observable behavior (order, drops, kept keys, bulk-build dedup, merge on append). Iterators are aliases of the builtin adapters (`Map<slice::Iter<..>, fn(..)>`), so every adapter works with std's item types. Keys compare with `<` and `==`; a key that reaches a written `PartialEq`/`PartialOrd`/`Ord` impl rejects (L0640, `check_std_order_keys`). `collect()` into `BTreeMap`/`BTreeSet` calls their `from_iter` (check/iter.rs), as a direct `BTreeMap::from_iter(..)` call does; `VecDeque::from_iter(..)` takes the `Vec` collect builtin. Not here yet: `Extend`, `Index`, `range`, `Hash`, ring-layout methods (`as_slices`, `make_contiguous`, `rotate_*`), `From<[_; N]>`. |
| `std::time` | library/std/src/time.rs | `Instant`, `SystemTime`, `UNIX_EPOCH`, `SystemTimeError`, re-exports of `core::time` | Clocks through `clock_now_raw` / `system_time_raw` (C in src/runtime/stdc.c). No `Error` impl yet. |
| `core::error`, `std::error` | library/core/src/error.rs | `Error` | Plain impls and bounds (W-STD-C phase 2). No `source`/`cause` yet: they name `dyn Error`, and a dyn object with std supertraits is L0702 (dyn.std). |
| `std::net` (overlay) | library/std/src/net.rs | `IpAddr`, `Ipv4Addr`, `Ipv6Addr`, `SocketAddr`, `SocketAddrV4`, `SocketAddrV6`, `AddrParseError` | Address values, text through `Formatter::pad`, std's parse accepts and rejects (W-STD-C phase 2). The socket types stay W-SHIM's. The unstable `ip` predicates are not here. |

## `std::mem` (compiler builtins, W-STD-C)

`swap`, `replace`, `take` (borrowck: the result holds what `*dest`
held, not the `&mut` borrow), `drop`, `forget`, `size_of`, `align_of`,
`size_of_val`, `align_of_val` (a literal's open type is read at the body
end), and `needs_drop` (a check-time constant; closures, iterator
adapters, and trait objects reject with L0641). `discriminant` and
`Discriminant<T>` are std source (library/core/src/mem.rs) over the
`discriminant_value` / `discriminant_kind` builtins (std source only,
L0642 elsewhere): Eq, Hash, and Debug as the enum's repr integer type;
a non-enum type at the call is rustc's `enum_intrinsics_non_enums`
(L0546); no layout queries. `ManuallyDrop` is std source too. Not here
yet: `transmute`.
`MaybeUninit<T>` is a synthetic Adt with the safe surface
(`uninit`, `zeroed`, `new`, `write`, `as_ptr`, `as_mut_ptr`;
the unsafe readers stay rejected).

## Intrinsics (`INTRINSICS` in src/ty/lang.rs)

Implemented (codegen emits them): `exit`; the platform crate's
`sys_write_std`, `sys_flush_std`, `sys_os_error_text`,
`sys_fmt_arguments_bytes`, the byte views (`sys_str_as_bytes`,
`sys_bytes_as_str`, `sys_utf8_*`, `sys_string_from_utf8_unchecked`),
and the syscalls of env, fs, and process (`sys_getenv`, `sys_environ`,
`sys_argv`, `sys_getcwd`, `sys_chdir`, `sys_readlink`, `sys_read_file`,
`sys_write_file`, `sys_path_op`, `sys_rename`, `sys_stat`,
`sys_realpath`, `sys_read_dir`, `sys_remove_dir_all`, `sys_getpid`; C in
src/runtime/sys.c); `clock_now_raw`, `system_time_raw`, and `fmt_align`
(W-STD-C, src/runtime/stdc.c); the adapter cores
`xxh3_64`/`xxh3_128` (xxhash-rust, C in src/runtime/deps.c) and
`ryu_js_fmt_f64` (ryu-js, the JS printer in src/runtime/float.c).
Adapter crates get their privilege from the resolver's record of their
files (`Program::shipped_crate_at`).

Registered with signature and privilege list, no body yet (a
privileged call rejects with L0640): the memory, bytes, ptr, float
text, panic, thread, sync, atomic, time, fd IO, and process groups of
section 3.2; the three specialization predicates of section 3.4; the
adapter cores `arena_alloc` (bumpalo) and `memchr`/`memrchr`/`memmem`
(memchr, whose adapter searches in source for now). A user call to any
intrinsic rejects with L0642.

Specialization that changes output (section 3.4 gate): none in source
yet, so no unfused difftest rows yet. Add one row here per predicate
use when W-STD writes it.

## Lang items (`LANG_ITEMS` in src/ty/lang.rs)

Resolved at load today: `option`, `result`, `string`, `vec` (builtin
defs; required, a load fails without them).

Declared in the table, no def yet: `box`, `rc`, `arc`,
`unsafe_cell`, `phantom_data`, the Range family, `iterator`,
`into_iterator`, `drop`, `deref`, `deref_mut`, the Fn family,
`sized`, `send`, `sync`, `panic`, `panic_bounds`, `formatter`,
`exchange_malloc`, `exchange_free`. W-STD marks the source def of
each with `#[lust_lang = "..."]` (alone on the line above the item
until the parser learns the attribute) and flips its row to
required in the same change.

## Builtin std surface (moves to source with W-STD)

These are compiler builtins today, not source std. Each keeps Rust
1.99 behavior (values, panics, drop order, layout) and moves to
source when the generic std pipeline can carry it.

| Surface | Where | Notes |
|---|---|---|
| Iterators over Vec, slices, arrays, ranges, Chars (21 kinds, adapters and consumers) | ty/iter.rs, check/iter.rs, lower/iter.rs | Expanded into IR after borrowck. Pull counts, Zip, and collect capacity follow core and alloc. |
| `vec::Drain`, `string::Drain` (`Vec::drain`, `String::drain`) and direct `next_back`/`size_hint`/`len` | ty/iter.rs kinds VecDrain/StringDrain, runtime/core.c `lust_vec_drain` | All RangeBounds argument forms with core's exact panic texts; a leaked Vec drain leaves the length at the drain start, a leaked String drain leaves the String whole. |
| `ops::Bound<T>`, `ops::RangeBounds`, the six range kinds as values, `Range` fields and `contains`, `Range::is_empty` | check/generics.rs (synthetic Adt), ty/iter.rs range kinds | RangeBounds and DoubleEndedIterator are lang traits with synthetic impls; the open-ended kinds are not iterators here, and `Bound::copied` is unstable in 1.99. |
| `sort`, `sort_unstable`, `binary_search` families | runtime/sort.h | C port of driftsort and ipnsort: same comparator calls and order of equal elements. |
| `Rc`, `rc::Weak`, `RefCell` (with `Ref`/`RefMut`), `Cell` | check/cells.rs, cgen.rs | Implicit weak count; borrow panics as Rust; `take`, `into_inner`, `unwrap_or_clone`, `new_cyclic`; region rules in borrowck/regions.rs. |
| `process::ExitCode` | check/process.rs | `main` may return it, or `Result<ExitCode, E>`. |
| `String::from_utf8`, `str::from_utf8`, `FromUtf8Error`, `Utf8Error` | check/utf8.rs, runtime core.c | The error types are synthetic std Adts (check/collect.rs), so derived Debug/Clone/Eq are the struct machinery. |
| `Box<[T]>` | cgen.rs `CTy::BoxSlice` | `into_boxed_slice`, `into_vec`, by-value iteration (`vec::IntoIter`), deref to `[T]`. No `Box<[T; N]>` coercion yet. |

Non-prelude std types (`Rc`, `Weak`, `RefCell`, `Cell`, `Ordering`,
`ExitCode`, `FromUtf8Error`, `Utf8Error`) need a `use` as in Rust
(`ty::lang::STD_IMPORTED_TYPES`); a full std path works without one.

## Rules for new source std fns (until W-RESOLVE)

1. Add the fn in the right `library/<crate>/src/<module>.rs`, in the
   supported subset, non-generic.
2. Add its `STD_FNS` row (path, mangled name, trigger substring).
3. Register each new intrinsic first: signature, C symbol, privilege
   list, and a difftest (section 3.2). Default answer for a new
   intrinsic is source, not a new row.
4. Add a tests/pass difftest that calls it, and update this ledger.
