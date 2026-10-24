// serde's crate root re-exports serde_core's data model: a Deserializer
// written with `serde::forward_to_deserialize_any!` and an enum read
// through `serde::de::value::StrDeserializer`, as fig's `de.rs` does.
use serde::de::{self, DeserializeSeed, EnumAccess, IntoDeserializer, VariantAccess, Visitor};
use serde::forward_to_deserialize_any;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

#[derive(Debug)]
struct Error(String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
impl de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(msg.to_string())
    }
}

struct Word<'a>(&'a str);
impl<'de> Deserializer<'de> for Word<'de> {
    type Error = Error;
    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        match self.0.parse::<i64>() {
            Ok(n) => v.visit_i64(n),
            Err(_) => v.visit_borrowed_str(self.0),
        }
    }
    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        v: V,
    ) -> Result<V::Value, Error> {
        v.visit_enum(Unit(self.0))
    }
    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

struct Unit<'a>(&'a str);
impl<'de> EnumAccess<'de> for Unit<'de> {
    type Error = Error;
    type Variant = Self;
    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self), Error> {
        let de = serde::de::value::StrDeserializer::<'_, Error>::new(self.0);
        Ok((seed.deserialize(de)?, self))
    }
}
impl<'de> VariantAccess<'de> for Unit<'de> {
    type Error = Error;
    fn unit_variant(self) -> Result<(), Error> {
        Ok(())
    }
    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, _seed: T) -> Result<T::Value, Error> {
        Err(de::Error::invalid_type(de::Unexpected::UnitVariant, &"newtype variant"))
    }
    fn tuple_variant<V: Visitor<'de>>(self, _len: usize, _v: V) -> Result<V::Value, Error> {
        Err(de::Error::invalid_type(de::Unexpected::UnitVariant, &"tuple variant"))
    }
    fn struct_variant<V: Visitor<'de>>(self, _f: &'static [&'static str], _v: V) -> Result<V::Value, Error> {
        Err(de::Error::invalid_type(de::Unexpected::UnitVariant, &"struct variant"))
    }
}

struct Upper;
impl Serialize for Upper {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str("UPPER")
    }
}

serde::serde_if_integer128! {
    fn wide() -> i128 {
        -1
    }
}

fn main() {
    println!("{:?}", i64::deserialize(Word("42")));
    println!("{:?}", String::deserialize(Word("text")));
    println!("{:?}", <&str>::deserialize(Word("borrow")));
    println!("{:?}", u8::deserialize(Word("300")).map_err(|e| e.0));
    println!("{:?}", Result::<u8, u8>::deserialize(Word("Ok")).map_err(|e| e.0));
    println!("{:?}", Result::<(), ()>::deserialize(Word("Err")));
    let sd: serde::de::value::StrDeserializer<'_, serde::de::value::Error> = "Ok".into_deserializer();
    println!("{:?}", String::deserialize(sd));
    let e: serde::de::value::Error = serde::ser::Error::custom("ser side");
    println!("{} {}", e, wide());
    let _ = Upper;
}
