# Adapter: serde 1.0.228

Lust adapter crate (docs/ARCH.md section 3.6). Dev builds compile it in
place of the registry package serde 1.0.228; release builds use the real
crate through Cargo. Gate: `scripts/test-adapters.sh serde`.

## Implemented, same results as upstream

- The crate root: `de`, `ser`, `Serialize`, `Serializer`, `Deserialize`,
  `Deserializer`, and `forward_to_deserialize_any!`, re-exported from
  serde_core as upstream does (see library/deps/serde_core/README.md for
  what serde_core implements), and `serde_if_integer128!`.
- Features: `default`, `std`.

## Rejected (lust error, never a different answer)

- The `derive` feature (serde_derive is a proc macro crate), and the
  hidden `__private` module its generated code uses.
- Features: `alloc` without `std`, `rc`, `unstable`.
