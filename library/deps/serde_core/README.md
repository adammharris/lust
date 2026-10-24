# Adapter: serde_core 1.0.228

Lust adapter crate (docs/ARCH.md section 3.6). Dev builds compile it in
place of the registry package serde_core 1.0.228; release builds use the
real crate through Cargo. Gate: `scripts/test-adapters.sh serde_core`.

It is upstream's source, ported to edition 2024 and to what lust checks
today. Each change carries a `// lust:` comment at its site.

## Implemented, same results as upstream

- The data model traits: `Serialize`, `Serializer` and its compound
  traits, `Deserialize`, `DeserializeOwned`, `DeserializeSeed`,
  `Deserializer`, `Visitor`, `SeqAccess`, `MapAccess`, `EnumAccess`,
  `VariantAccess`, `IntoDeserializer`, the `Error` traits with their
  default messages, `Expected`, `Unexpected`, `IgnoredAny`,
  `ser::Impossible`, and `forward_to_deserialize_any!`.
- `de::value`: the primitive and string deserializers, `SeqDeserializer`,
  `SeqAccessDeserializer`, `MapAccessDeserializer`, `EnumAccessDeserializer`,
  and `value::Error`.
- The std impls lust has the types for. These include primitives and
  `NonZero*`, `char`, strings, `Option`, `Result`, tuples, arrays,
  `Vec`, `VecDeque`, `BTreeSet`, `HashSet`, `BTreeMap`, `HashMap`, `Box`,
  `Cell`, `RefCell`, `Mutex`, `RwLock`, `Reverse` and `PhantomData`. On
  the `Serialize` side there are also `Duration`, `SystemTime`, `Path`,
  `PathBuf`, `OsStr`, `OsString`, the IP and socket addresses, `Bound`
  and the atomics.
- Features: `default`, `std`, `result`.

Visitors that upstream defines inside fn bodies or macro arms live at
module level here. They are private, and their `expecting` texts are
upstream's.

## Rejected (lust error, never a different answer)

- No impls (lust has no such types): `CString`, `Wrapping`, `Saturating`,
  `BinaryHeap`, `LinkedList`, `Box<[T]>`, `Box<str>`, `Box<Path>`,
  `Box<OsStr>`, `&Path`, and `Range*` over a generic index.
- `Deserialize` not ported yet (fn-local impls, or region checks lust
  does not do yet): `Duration`, `SystemTime`, `OsString`, `Bound`, the IP
  and socket addresses, and `Cow`.
- `de::value::MapDeserializer` and the `IntoDeserializer` impls for
  `BTreeMap` and `HashMap`.
- `Display` for `dyn Expected` (the default `Error` messages format
  through a private wrapper instead).
- The hidden `Deserializer::__deserialize_content_v1` and
  `deserialize_in_place` overrides (serde's derive uses them; the trait
  default of `deserialize_in_place` holds).
- `Mutex<T>` and `RwLock<T>` take a sized `T`.
- Features: `alloc` without `std`, `rc`, `unstable`.
