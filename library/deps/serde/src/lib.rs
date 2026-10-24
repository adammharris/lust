//! Lust adapter: serde 1.0.228 without its `derive` feature. Upstream's
//! crate root re-exports serde_core's data model (the serde_core adapter
//! here), as below; its `__private` module and `private` items exist only
//! for serde_derive's generated code and are not ported.

#![allow(unknown_lints, bare_trait_objects, deprecated, mismatched_lifetime_syntaxes)]

pub use serde_core::{de, forward_to_deserialize_any, ser, Deserialize, Deserializer, Serialize, Serializer};

mod integer128;

#[macro_export]
#[doc(hidden)]
macro_rules! __require_serde_not_serde_core {
    () => {};
}
