# Adapter: bitflags 2.13.2

Lust adapter crate (docs/ARCH.md section 3.6). Upstream's source
(`#![forbid(unsafe_code)]`, edition 2021) with these changes, so the
generated types and every text they print and parse are upstream's.
Gate: `scripts/test-adapters.sh bitflags`.

## Changes from upstream

- Edition 2024, and no `serde`, `arbitrary`, `bytemuck`, or
  `example_generated` (the external/ modules are gone).
- The `struct` form of `bitflags!`: upstream declares a private
  `InternalBitFlags` type and all its impls inside
  `const _: () = { .. };`. Lust has no impls inside bodies yet (L0820)
  and a macro cannot make a fresh item name, so the public type's field
  is the generic `__private::Internal<Self, Bits>` (lust.rs), whose
  impls (Debug, Display, FromStr, Default, comparison, hashing, the hex
  forms) give the same results as upstream's `InternalBitFlags`. The
  public methods come from `__impl_public_bitflags_wrapped!`, upstream's
  `__impl_public_bitflags!` with the bits read through that field.
- The `impl` form's impls are at module level, not in a `const _`
  block: impls have no names, so the meaning is the same.
- `from_name` and `Flags::FLAGS` read each flag's name text from
  `__bitflags_flag_name_expr!` in place of consts in a module inside
  the fn (no items but types, fns, and consts in bodies yet). It gives
  the same text: the last `#[bitflags(flag_name = ..)]`, else the name.
- `::core::stringify!` and `::core::write!` in place of
  `$crate::__private::core::..!`: lust does not yet resolve a macro
  through another crate's re-export of `core`.

## Rejected (lust error, never a different answer)

- Upstream's inherent methods on the internal field type (`flags.0`
  in the defining module: `bits_mut`, `contains`, ...). L0104.
- Features `serde`, `arbitrary`, `bytemuck`: L0508.
