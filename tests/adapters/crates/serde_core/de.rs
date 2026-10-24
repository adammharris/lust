// A Deserializer over a token tree, through serde_core's traits: the std
// impls (numbers with range checks, chars, strings, borrowed strs, options,
// tuples, collections, arrays, Result), the default `Error` messages
// (`invalid type`, `invalid value`, `invalid length`, `unknown variant`),
// `forward_to_deserialize_any!`, `IgnoredAny`, and `de::value`.
use serde_core::de::value::{Error as ValueError, StrDeserializer};
use serde_core::de::{
    self, DeserializeOwned, DeserializeSeed, Deserializer, EnumAccess, IgnoredAny, IntoDeserializer, MapAccess,
    SeqAccess, Unexpected, VariantAccess, Visitor,
};
use serde_core::{forward_to_deserialize_any, Deserialize};
use std::collections::{BTreeMap, HashMap, VecDeque};
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

enum Tok {
    Bool(bool),
    I64(i64),
    U64(u64),
    I128(i128),
    F64(f64),
    Str(&'static str),
    Bytes(&'static [u8]),
    Seq(Vec<Tok>),
    Map(Vec<(Tok, Tok)>),
    Null,
    Some(Box<Tok>),
    Unit,
    Variant(&'static str, Box<Tok>),
}

struct De<'a>(&'a Tok);

impl<'de> Deserializer<'de> for De<'de> {
    type Error = Error;
    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        match self.0 {
            Tok::Bool(b) => v.visit_bool(*b),
            Tok::I64(n) => v.visit_i64(*n),
            Tok::U64(n) => v.visit_u64(*n),
            Tok::I128(n) => v.visit_i128(*n),
            Tok::F64(n) => v.visit_f64(*n),
            Tok::Str(s) => v.visit_borrowed_str(s),
            Tok::Bytes(b) => v.visit_borrowed_bytes(b),
            Tok::Seq(items) => v.visit_seq(Seq { it: items.iter() }),
            Tok::Map(entries) => v.visit_map(Map { it: entries.iter(), value: None }),
            Tok::Null => v.visit_none(),
            Tok::Some(t) => v.visit_some(De(t)),
            Tok::Unit => v.visit_unit(),
            Tok::Variant(..) => v.visit_enum(Enum(self.0)),
        }
    }
    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        v: V,
    ) -> Result<V::Value, Error> {
        match self.0 {
            Tok::Variant(..) => v.visit_enum(Enum(self.0)),
            Tok::Str(s) => v.visit_enum(s.into_deserializer()),
            _ => self.deserialize_any(v),
        }
    }
    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

struct Seq<'a> {
    it: std::slice::Iter<'a, Tok>,
}
impl<'de> SeqAccess<'de> for Seq<'de> {
    type Error = Error;
    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>, Error> {
        match self.it.next() {
            Some(t) => seed.deserialize(De(t)).map(Some),
            None => Ok(None),
        }
    }
    fn size_hint(&self) -> Option<usize> {
        Some(self.it.len())
    }
}

struct Map<'a> {
    it: std::slice::Iter<'a, (Tok, Tok)>,
    value: Option<&'a Tok>,
}
impl<'de> MapAccess<'de> for Map<'de> {
    type Error = Error;
    fn next_key_seed<K: DeserializeSeed<'de>>(&mut self, seed: K) -> Result<Option<K::Value>, Error> {
        match self.it.next() {
            Some((k, v)) => {
                self.value = Some(v);
                seed.deserialize(De(k)).map(Some)
            }
            None => Ok(None),
        }
    }
    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> Result<V::Value, Error> {
        seed.deserialize(De(self.value.take().unwrap()))
    }
}

struct Enum<'a>(&'a Tok);
impl<'de> EnumAccess<'de> for Enum<'de> {
    type Error = Error;
    type Variant = De<'de>;
    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, De<'de>), Error> {
        let Tok::Variant(name, body) = self.0 else { unreachable!() };
        let key = seed.deserialize(StrDeserializer::<Error>::new(name))?;
        Ok((key, De(body)))
    }
}
impl<'de> VariantAccess<'de> for De<'de> {
    type Error = Error;
    fn unit_variant(self) -> Result<(), Error> {
        Ok(())
    }
    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> Result<T::Value, Error> {
        seed.deserialize(self)
    }
    fn tuple_variant<V: Visitor<'de>>(self, _len: usize, v: V) -> Result<V::Value, Error> {
        self.deserialize_any(v)
    }
    fn struct_variant<V: Visitor<'de>>(self, _fields: &'static [&'static str], v: V) -> Result<V::Value, Error> {
        self.deserialize_any(v)
    }
}

impl de::Error for ValueErrorShim {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        ValueErrorShim(msg.to_string())
    }
}
#[derive(Debug)]
struct ValueErrorShim(String);
impl fmt::Display for ValueErrorShim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ValueErrorShim {}

fn get<'de, T: Deserialize<'de>>(t: &'de Tok) -> Result<T, Error> {
    T::deserialize(De(t))
}

fn show<T: fmt::Debug>(what: &str, r: Result<T, Error>) {
    match r {
        Ok(v) => println!("{}: {:?}", what, v),
        Err(e) => println!("{}: error: {}", what, e),
    }
}

fn owned<T: DeserializeOwned + fmt::Debug>(t: &Tok) -> Result<T, Error> {
    T::deserialize(De(t))
}

// A visitor written by hand, as fig's `Value` deserializer does.
#[allow(dead_code)]
#[derive(Debug)]
enum Val {
    Int(i64),
    Text(String),
    List(Vec<Val>),
    Nothing,
}
impl<'de> Deserialize<'de> for Val {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Val, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = Val;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a val")
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Val, E> {
                Ok(Val::Int(v))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Val, E> {
                i64::try_from(v).map(Val::Int).map_err(|_| E::invalid_value(Unexpected::Unsigned(v), &self))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Val, E> {
                Ok(Val::Text(v.to_string()))
            }
            fn visit_unit<E: de::Error>(self) -> Result<Val, E> {
                Ok(Val::Nothing)
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Val, A::Error> {
                let mut out = Vec::new();
                while let Some(v) = seq.next_element()? {
                    out.push(v);
                }
                Ok(Val::List(out))
            }
        }
        d.deserialize_any(V)
    }
}

fn main() {
    show("bool", get::<bool>(&Tok::Bool(true)));
    show("bool from str", get::<bool>(&Tok::Str("t")));
    show("u8", get::<u8>(&Tok::U64(255)));
    show("u8 big", get::<u8>(&Tok::U64(256)));
    show("i8 low", get::<i8>(&Tok::I64(-129)));
    show("u32 neg", get::<u32>(&Tok::I64(-1)));
    show("i64", get::<i64>(&Tok::I64(-7)));
    show("u64 from i64", get::<u64>(&Tok::I64(7)));
    show("i128", get::<i128>(&Tok::I128(-5)));
    show("u16 from i128", get::<u16>(&Tok::I128(70000)));
    show("bool from i128", get::<bool>(&Tok::I128(5)));
    show("nonzero 0", get::<std::num::NonZeroU8>(&Tok::U64(0)));
    show("nonzero 9", get::<std::num::NonZeroU8>(&Tok::U64(9)));
    show("f32 from int", get::<f32>(&Tok::I64(3)));
    show("f64", get::<f64>(&Tok::F64(-2.5)));
    show("u8 from float", get::<u8>(&Tok::F64(1.5)));
    show("u8 from whole float", get::<u8>(&Tok::F64(2.0)));
    show("u8 from inf", get::<u8>(&Tok::F64(f64::INFINITY)));
    show("char", get::<char>(&Tok::Str("x")));
    show("char long", get::<char>(&Tok::Str("xy")));
    show("string", get::<String>(&Tok::Str("hello")));
    show("borrowed str", get::<&str>(&Tok::Str("borrowed")));
    show("borrowed bytes", get::<&[u8]>(&Tok::Bytes(b"ab")));
    show("string from int", get::<String>(&Tok::I64(1)));
    show("none", get::<Option<u8>>(&Tok::Null));
    show("some", get::<Option<u8>>(&Tok::Some(Box::new(Tok::U64(4)))));
    show("unit", get::<()>(&Tok::Unit));
    show("unit from seq", get::<()>(&Tok::Seq(vec![])));
    show("vec", get::<Vec<u16>>(&Tok::Seq(vec![Tok::U64(1), Tok::U64(2)])));
    show("vec bad", get::<Vec<u16>>(&Tok::Seq(vec![Tok::U64(1), Tok::Str("2")])));
    show("deque", get::<VecDeque<i32>>(&Tok::Seq(vec![Tok::I64(-1)])));
    show("tuple", get::<(u8, String)>(&Tok::Seq(vec![Tok::U64(1), Tok::Str("s")])));
    show("tuple short", get::<(u8, String)>(&Tok::Seq(vec![Tok::U64(1)])));
    show("array", get::<[u8; 3]>(&Tok::Seq(vec![Tok::U64(1), Tok::U64(2), Tok::U64(3)])));
    show("array short", get::<[u8; 3]>(&Tok::Seq(vec![Tok::U64(1)])));
    show("array empty", get::<[u8; 0]>(&Tok::Seq(vec![])));
    let m = Tok::Map(vec![(Tok::Str("b"), Tok::I64(2)), (Tok::Str("a"), Tok::I64(1))]);
    show("btreemap", get::<BTreeMap<String, i32>>(&m));
    show("hashmap", get::<HashMap<String, i64>>(&Tok::Map(vec![(Tok::Str("k"), Tok::I64(1))])));
    show("map from seq", get::<BTreeMap<String, i32>>(&Tok::Seq(vec![])));
    show("box", get::<Box<u8>>(&Tok::U64(8)));
    show("result ok", get::<Result<u8, String>>(&Tok::Variant("Ok", Box::new(Tok::U64(1)))));
    show("result err", get::<Result<u8, String>>(&Tok::Variant("Err", Box::new(Tok::Str("bad")))));
    show("result unknown", get::<Result<u8, String>>(&Tok::Variant("Maybe", Box::new(Tok::Unit))));
    show("ignored", get::<IgnoredAny>(&Tok::Seq(vec![Tok::U64(1), Tok::Map(vec![])])));
    show("val", get::<Val>(&Tok::Seq(vec![Tok::I64(1), Tok::Str("t"), Tok::Unit, Tok::Seq(vec![])])));
    show("val big", get::<Val>(&Tok::U64(u64::MAX)));
    show("val bool", get::<Val>(&Tok::Bool(false)));
    println!("{:?}", owned::<Vec<String>>(&Tok::Seq(vec![Tok::Str("o")])));
    let sd: StrDeserializer<ValueError> = "text".into_deserializer();
    println!("{:?}", String::deserialize(sd));
    let sd2 = StrDeserializer::<ValueError>::new("9");
    println!("{:?}", u8::deserialize(sd2).map_err(|e| e.to_string()));
    let ud = 5u32.into_deserializer();
    let r: Result<u64, ValueErrorShim> = u64::deserialize(ud);
    println!("{:?}", r);
    let vd = vec![1u8, 2].into_deserializer();
    let r: Result<Vec<u8>, ValueErrorShim> = Vec::<u8>::deserialize(vd);
    println!("{:?}", r);
    let e: ValueError = de::Error::invalid_length(3, &"two");
    println!("{}", e);
    let e: ValueError = de::Error::unknown_field("z", &["x", "y"]);
    println!("{}", e);
    let e: ValueError = de::Error::unknown_variant("C", &["A"]);
    println!("{}", e);
    let e: ValueError = de::Error::unknown_variant("C", &[]);
    println!("{}", e);
    let e: ValueError = de::Error::missing_field("q");
    println!("{}", e);
    let e: ValueError = de::Error::duplicate_field("q");
    println!("{}", e);
    for u in [
        Unexpected::Bool(true),
        Unexpected::Unsigned(1),
        Unexpected::Signed(-1),
        Unexpected::Float(1.0),
        Unexpected::Float(1e100),
        Unexpected::Float(f64::NAN),
        Unexpected::Char('c'),
        Unexpected::Str("s"),
        Unexpected::Bytes(b"b"),
        Unexpected::Unit,
        Unexpected::Option,
        Unexpected::NewtypeStruct,
        Unexpected::Seq,
        Unexpected::Map,
        Unexpected::Enum,
        Unexpected::UnitVariant,
        Unexpected::NewtypeVariant,
        Unexpected::TupleVariant,
        Unexpected::StructVariant,
        Unexpected::Other("other"),
    ] {
        println!("{}", u);
    }
}
