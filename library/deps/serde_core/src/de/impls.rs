use crate::lib::*;

use crate::de::{
    Deserialize, Deserializer, EnumAccess, Error, MapAccess, SeqAccess, Unexpected, VariantAccess,
    Visitor,
};
use crate::private;

#[cfg(any(feature = "std", feature = "alloc"))]
use crate::private::size_hint;

////////////////////////////////////////////////////////////////////////////////

struct UnitVisitor;

impl<'de> Visitor<'de> for UnitVisitor {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("unit")
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(())
    }
}

impl<'de> Deserialize<'de> for () {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_unit(UnitVisitor)
    }
}

#[cfg(feature = "unstable")]
impl<'de> Deserialize<'de> for ! {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Err(Error::custom("cannot deserialize `!`"))
    }
}

////////////////////////////////////////////////////////////////////////////////

struct BoolVisitor;

impl<'de> Visitor<'de> for BoolVisitor {
    type Value = bool;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a boolean")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v)
    }
}

impl<'de> Deserialize<'de> for bool {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bool(BoolVisitor)
    }
}

////////////////////////////////////////////////////////////////////////////////

// lust: impls inside fn bodies are not supported yet, so the visitors
// upstream defines inside each `deserialize` live at module level: here,
// one generic struct per kind with an impl for each `Value` type, and
// above each impl that uses one otherwise (`VecVisitor`).
struct PrimitiveVisitor<T>(PhantomData<T>);
struct NonZeroVisitor<T>(PhantomData<T>);
struct SeqVisitor<C> {
    marker: PhantomData<C>,
}
struct MapVisitor<C> {
    marker: PhantomData<C>,
}
struct TupleVisitor<T> {
    marker: PhantomData<T>,
}

macro_rules! impl_deserialize_num {
    ($primitive:ident, $nonzero:ident, $deserialize:ident $($method:ident!($($val:ident : $visit:ident)*);)*) => {
        impl_deserialize_num!($primitive, $deserialize $($method!($($val : $visit)*);)*);

        impl<'de> Deserialize<'de> for num::$nonzero {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.$deserialize(NonZeroVisitor::<num::$nonzero>(PhantomData))
            }
        }

        impl<'de> Visitor<'de> for NonZeroVisitor<num::$nonzero> {
            type Value = num::$nonzero;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str(concat!("a nonzero ", stringify!($primitive)))
            }

            $($($method!(nonzero $primitive $nonzero $val : $visit);)*)*
        }

        // lust: lust has no Saturating yet: `impl<'de> Deserialize<'de> for Saturating<$primitive>`
    };

    ($primitive:ident, $deserialize:ident $($method:ident!($($val:ident : $visit:ident)*);)*) => {
        impl<'de> Deserialize<'de> for $primitive {
            #[inline]
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.$deserialize(PrimitiveVisitor::<$primitive>(PhantomData))
            }
        }

        impl<'de> Visitor<'de> for PrimitiveVisitor<$primitive> {
            type Value = $primitive;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str(stringify!($primitive))
            }

            $($($method!(prim $primitive $val : $visit);)*)*
        }
    };
}

// lust: `Self::Value::new` and other paths through `Self::Value` are not
// supported yet in these impls, so the macros below take the primitive
// (`prim $primitive`) and nonzero type and name them directly.
macro_rules! num_self {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(v)
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Some(nonzero) = num::$nonzero::new(v) {
                Ok(nonzero)
            } else {
                Err(Error::invalid_value(Unexpected::Unsigned(0), &self))
            }
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Saturating(v))
        }
    };
}

macro_rules! num_as_self {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(v as Self::Value)
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Some(nonzero) = num::$nonzero::new(v as $primitive) {
                Ok(nonzero)
            } else {
                Err(Error::invalid_value(Unexpected::Unsigned(0), &self))
            }
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Saturating(v as $primitive))
        }
    };
}

macro_rules! num_as_copysign_self {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            #[cfg(not(feature = "std"))]
            {
                Ok(v as Self::Value)
            }

            #[cfg(feature = "std")]
            {
                // Preserve sign of NaN. The `as` produces a nondeterministic sign.
                let sign = if v.is_sign_positive() { 1.0 } else { -1.0 };
                Ok((v as Self::Value).copysign(sign))
            }
        }
    };
}

macro_rules! int_to_int {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            $primitive::try_from(v as i64)
                .map_err(|_| Error::invalid_value(Unexpected::Signed(v as i64), &self))
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Ok(v) = $primitive::try_from(v as i64) {
                if let Some(nonzero) = num::$nonzero::new(v) {
                    return Ok(nonzero);
                }
            }
            Err(Error::invalid_value(Unexpected::Signed(v as i64), &self))
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if (v as i64) < $primitive::MIN as i64 {
                Ok(Saturating($primitive::MIN))
            } else if ($primitive::MAX as i64) < v as i64 {
                Ok(Saturating($primitive::MAX))
            } else {
                Ok(Saturating(v as $primitive))
            }
        }
    };
}

macro_rules! int_to_uint {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if 0 <= v {
                #[allow(irrefutable_let_patterns)]
                if let Ok(v) = $primitive::try_from(v as u64) {
                    return Ok(v as Self::Value);
                }
            }
            Err(Error::invalid_value(Unexpected::Signed(v as i64), &self))
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if 0 < v {
                #[allow(irrefutable_let_patterns)]
                if let Ok(v) = $primitive::try_from(v as u64) {
                    if let Some(nonzero) = num::$nonzero::new(v) {
                        return Ok(nonzero);
                    }
                }
            }
            Err(Error::invalid_value(Unexpected::Signed(v as i64), &self))
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if v < 0 {
                Ok(Saturating(0))
            } else if ($primitive::MAX as u64) < v as u64 {
                Ok(Saturating($primitive::MAX))
            } else {
                Ok(Saturating(v as $primitive))
            }
        }
    };
}

macro_rules! uint_to_self {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        #[inline]
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            $primitive::try_from(v as u64)
                .map_err(|_| Error::invalid_value(Unexpected::Unsigned(v as u64), &self))
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Ok(v) = $primitive::try_from(v as u64) {
                if let Some(nonzero) = num::$nonzero::new(v) {
                    return Ok(nonzero);
                }
            }
            Err(Error::invalid_value(Unexpected::Unsigned(v as u64), &self))
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Ok(v) = $primitive::try_from(v as u64) {
                Ok(Saturating(v as $primitive))
            } else {
                Ok(Saturating($primitive::MAX))
            }
        }
    };
}

impl_deserialize_num! {
    i8, NonZeroI8, deserialize_i8
    num_self!(i8:visit_i8);
    int_to_int!(i16:visit_i16 i32:visit_i32 i64:visit_i64);
    uint_to_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    i16, NonZeroI16, deserialize_i16
    num_self!(i16:visit_i16);
    num_as_self!(i8:visit_i8);
    int_to_int!(i32:visit_i32 i64:visit_i64);
    uint_to_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    i32, NonZeroI32, deserialize_i32
    num_self!(i32:visit_i32);
    num_as_self!(i8:visit_i8 i16:visit_i16);
    int_to_int!(i64:visit_i64);
    uint_to_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    i64, NonZeroI64, deserialize_i64
    num_self!(i64:visit_i64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32);
    uint_to_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    isize, NonZeroIsize, deserialize_i64
    num_as_self!(i8:visit_i8 i16:visit_i16);
    int_to_int!(i32:visit_i32 i64:visit_i64);
    uint_to_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    u8, NonZeroU8, deserialize_u8
    num_self!(u8:visit_u8);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    uint_to_self!(u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    u16, NonZeroU16, deserialize_u16
    num_self!(u16:visit_u16);
    num_as_self!(u8:visit_u8);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    uint_to_self!(u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    u32, NonZeroU32, deserialize_u32
    num_self!(u32:visit_u32);
    num_as_self!(u8:visit_u8 u16:visit_u16);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    uint_to_self!(u64:visit_u64);
}

impl_deserialize_num! {
    u64, NonZeroU64, deserialize_u64
    num_self!(u64:visit_u64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
}

impl_deserialize_num! {
    usize, NonZeroUsize, deserialize_u64
    num_as_self!(u8:visit_u8 u16:visit_u16);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    uint_to_self!(u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    f32, deserialize_f32
    num_self!(f32:visit_f32);
    num_as_copysign_self!(f64:visit_f64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    f64, deserialize_f64
    num_self!(f64:visit_f64);
    num_as_copysign_self!(f32:visit_f32);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

macro_rules! num_128 {
    (prim $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if v as i128 >= $primitive::MIN as i128 && v as u128 <= $primitive::MAX as u128 {
                Ok(v as Self::Value)
            } else {
                Err(Error::invalid_value(
                    Unexpected::Other(stringify!($ty)),
                    &self,
                ))
            }
        }
    };

    (nonzero $primitive:ident $nonzero:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if v as i128 >= $primitive::MIN as i128 && v as u128 <= $primitive::MAX as u128 {
                if let Some(nonzero) = num::$nonzero::new(v as $primitive) {
                    Ok(nonzero)
                } else {
                    Err(Error::invalid_value(Unexpected::Unsigned(0), &self))
                }
            } else {
                Err(Error::invalid_value(
                    Unexpected::Other(stringify!($ty)),
                    &self,
                ))
            }
        }
    };

    (saturating $primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if (v as i128) < $primitive::MIN as i128 {
                Ok(Saturating($primitive::MIN))
            } else if ($primitive::MAX as u128) < v as u128 {
                Ok(Saturating($primitive::MAX))
            } else {
                Ok(Saturating(v as $primitive))
            }
        }
    };
}

impl_deserialize_num! {
    i128, NonZeroI128, deserialize_i128
    num_self!(i128:visit_i128);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
    num_128!(u128:visit_u128);
}

impl_deserialize_num! {
    u128, NonZeroU128, deserialize_u128
    num_self!(u128:visit_u128);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
    int_to_uint!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_128!(i128:visit_i128);
}

////////////////////////////////////////////////////////////////////////////////

struct CharVisitor;

impl<'de> Visitor<'de> for CharVisitor {
    type Value = char;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a character")
    }

    #[inline]
    fn visit_char<E>(self, v: char) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v)
    }

    #[inline]
    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        let mut iter = v.chars();
        match (iter.next(), iter.next()) {
            (Some(c), None) => Ok(c),
            _ => Err(Error::invalid_value(Unexpected::Str(v), &self)),
        }
    }
}

impl<'de> Deserialize<'de> for char {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_char(CharVisitor)
    }
}

////////////////////////////////////////////////////////////////////////////////

#[cfg(any(feature = "std", feature = "alloc"))]
struct StringVisitor;
#[cfg(any(feature = "std", feature = "alloc"))]
// lust: in-place deserialization is not ported (the trait default holds)
#[cfg(any())]
struct StringInPlaceVisitor<'a>(&'a mut String);

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'de> Visitor<'de> for StringVisitor {
    type Value = String;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v.to_owned())
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v)
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match str::from_utf8(v) {
            Ok(s) => Ok(s.to_owned()),
            Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match String::from_utf8(v) {
            Ok(s) => Ok(s),
            Err(e) => Err(Error::invalid_value(
                Unexpected::Bytes(&e.into_bytes()),
                &self,
            )),
        }
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
// lust: in-place deserialization is not ported (the trait default holds)
#[cfg(any())]
impl<'a, 'de> Visitor<'de> for StringInPlaceVisitor<'a> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        self.0.clear();
        self.0.push_str(v);
        Ok(())
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        *self.0 = v;
        Ok(())
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match str::from_utf8(v) {
            Ok(s) => {
                self.0.clear();
                self.0.push_str(s);
                Ok(())
            }
            Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match String::from_utf8(v) {
            Ok(s) => {
                *self.0 = s;
                Ok(())
            }
            Err(e) => Err(Error::invalid_value(
                Unexpected::Bytes(&e.into_bytes()),
                &self,
            )),
        }
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'de> Deserialize<'de> for String {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(StringVisitor)
    }

}

////////////////////////////////////////////////////////////////////////////////

struct StrVisitor;

impl<'a> Visitor<'a> for StrVisitor {
    type Value = &'a str;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a borrowed string")
    }

    fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v) // so easy
    }

    fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        str::from_utf8(v).map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for &'a str {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(StrVisitor)
    }
}

////////////////////////////////////////////////////////////////////////////////

struct BytesVisitor;

impl<'a> Visitor<'a> for BytesVisitor {
    type Value = &'a [u8];

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a borrowed byte array")
    }

    fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v)
    }

    fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(v.as_bytes())
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for &'a [u8] {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(BytesVisitor)
    }
}

////////////////////////////////////////////////////////////////////////////////

#[cfg(any(feature = "std", feature = "alloc"))]
// lust: lust has no CString yet
#[cfg(any())]
struct CStringVisitor;

#[cfg(any(feature = "std", feature = "alloc"))]
// lust: lust has no CString yet
#[cfg(any())]
impl<'de> Visitor<'de> for CStringVisitor {
    type Value = CString;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("byte array")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let capacity = size_hint::cautious::<u8>(seq.size_hint());
        let mut values = Vec::<u8>::with_capacity(capacity);

        while let Some(value) = tri!(seq.next_element()) {
            values.push(value);
        }

        CString::new(values).map_err(Error::custom)
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        CString::new(v).map_err(Error::custom)
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        CString::new(v).map_err(Error::custom)
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        CString::new(v).map_err(Error::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        CString::new(v).map_err(Error::custom)
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
// lust: lust has no CString yet
#[cfg(any())]
impl<'de> Deserialize<'de> for CString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_byte_buf(CStringVisitor)
    }
}

macro_rules! forwarded_impl {
    (
        $(#[$attr:meta])*
        ($($id:ident),*), $ty:ty, $func:expr
    ) => {
        $(#[$attr])*
        impl<'de $(, $id : Deserialize<'de>,)*> Deserialize<'de> for $ty {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Deserialize::deserialize(deserializer).map($func)
            }
        }
    }
}

forwarded_impl! {
    #[cfg(any(feature = "std", feature = "alloc"))]
    // lust: lust has no CString yet
    #[cfg(any())]
    (), Box<CStr>, CString::into_boxed_c_str
}

forwarded_impl! {
    (T), Reverse<T>, Reverse
}

////////////////////////////////////////////////////////////////////////////////

struct OptionVisitor<T> {
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for OptionVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Option<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("option")
    }

    #[inline]
    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(None)
    }

    #[inline]
    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(None)
    }

    #[inline]
    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        T::deserialize(deserializer).map(Some)
    }

    fn __private_visit_untagged_option<D>(self, deserializer: D) -> Result<Self::Value, ()>
    where
        D: Deserializer<'de>,
    {
        Ok(T::deserialize(deserializer).ok())
    }
}

impl<'de, T> Deserialize<'de> for Option<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_option(OptionVisitor {
            marker: PhantomData,
        })
    }

    // The Some variant's repr is opaque, so we can't play cute tricks with its
    // tag to have deserialize_in_place build the content in place unconditionally.
    //
    // FIXME: investigate whether branching on the old value being Some to
    // deserialize_in_place the value is profitable (probably data-dependent?)
}

////////////////////////////////////////////////////////////////////////////////

struct PhantomDataVisitor<T: ?Sized> {
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for PhantomDataVisitor<T>
where
    T: ?Sized,
{
    type Value = PhantomData<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("unit")
    }

    #[inline]
    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(PhantomData)
    }
}

impl<'de, T> Deserialize<'de> for PhantomData<T>
where
    T: ?Sized,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let visitor = PhantomDataVisitor {
            marker: PhantomData,
        };
        deserializer.deserialize_unit_struct("PhantomData", visitor)
    }
}

////////////////////////////////////////////////////////////////////////////////

macro_rules! seq_impl {
    (
        $(#[$attr:meta])*
        $ty:ident <T $(: $tbound1:ident $(+ $tbound2:ident)*)* $(, $typaram:ident : $bound1:ident $(+ $bound2:ident)*)*>,
        $access:ident,
        $clear:expr,
        $with_capacity:expr,
        $reserve:expr,
        $insert:expr
    ) => {
        $(#[$attr])*
        impl<'de, T $(, $typaram)*> Visitor<'de> for SeqVisitor<$ty<T $(, $typaram)*>>
        where
            T: Deserialize<'de> $(+ $tbound1 $(+ $tbound2)*)*,
            $($typaram: $bound1 $(+ $bound2)*,)*
        {
            type Value = $ty<T $(, $typaram)*>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            #[inline]
            fn visit_seq<A>(self, mut $access: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = $with_capacity;

                while let Some(value) = tri!($access.next_element()) {
                    $insert(&mut values, value);
                }

                Ok(values)
            }
        }

        $(#[$attr])*
        impl<'de, T $(, $typaram)*> Deserialize<'de> for $ty<T $(, $typaram)*>
        where
            T: Deserialize<'de> $(+ $tbound1 $(+ $tbound2)*)*,
            $($typaram: $bound1 $(+ $bound2)*,)*
        {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let visitor = SeqVisitor::<$ty<T $(, $typaram)*>> { marker: PhantomData };
                deserializer.deserialize_seq(visitor)
            }

        }
    }
}

// Dummy impl of reserve
#[cfg(any(feature = "std", feature = "alloc"))]
fn nop_reserve<T>(_seq: T, _n: usize) {}

// lust: lust has no BinaryHeap yet: the seq_impl expansion for BinaryHeap

seq_impl!(
    #[cfg(any(feature = "std", feature = "alloc"))]
    BTreeSet<T: Eq + Ord>,
    seq,
    BTreeSet::clear,
    BTreeSet::new(),
    nop_reserve,
    BTreeSet::insert
);

// lust: lust has no LinkedList yet: the seq_impl expansion for LinkedList

seq_impl!(
    #[cfg(feature = "std")]
    HashSet<T: Eq + Hash, S: BuildHasher + Default>,
    seq,
    HashSet::clear,
    HashSet::with_capacity_and_hasher(size_hint::cautious::<T>(seq.size_hint()), S::default()),
    HashSet::reserve,
    HashSet::insert
);

seq_impl!(
    #[cfg(any(feature = "std", feature = "alloc"))]
    VecDeque<T>,
    seq,
    VecDeque::clear,
    VecDeque::with_capacity(size_hint::cautious::<T>(seq.size_hint())),
    VecDeque::reserve,
    VecDeque::push_back
);

////////////////////////////////////////////////////////////////////////////////

#[cfg(any(feature = "std", feature = "alloc"))]
struct VecVisitor<T> {
    marker: PhantomData<T>,
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'de, T> Visitor<'de> for VecVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let capacity = size_hint::cautious::<T>(seq.size_hint());
        let mut values = Vec::<T>::with_capacity(capacity);

        while let Some(value) = tri!(seq.next_element()) {
            values.push(value);
        }

        Ok(values)
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'de, T> Deserialize<'de> for Vec<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let visitor = VecVisitor {
            marker: PhantomData,
        };
        deserializer.deserialize_seq(visitor)
    }

}

////////////////////////////////////////////////////////////////////////////////

struct ArrayVisitor<A> {
    marker: PhantomData<A>,
}
// lust: in-place deserialization is not ported (the trait default holds)
#[cfg(any())]
struct ArrayInPlaceVisitor<'a, A: 'a>(&'a mut A);

impl<A> ArrayVisitor<A> {
    fn new() -> Self {
        ArrayVisitor {
            marker: PhantomData,
        }
    }
}

impl<'de, T> Visitor<'de> for ArrayVisitor<[T; 0]> {
    type Value = [T; 0];

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("an empty array")
    }

    #[inline]
    fn visit_seq<A>(self, _: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        Ok([])
    }
}

// Does not require T: Deserialize<'de>.
impl<'de, T> Deserialize<'de> for [T; 0] {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_tuple(0, ArrayVisitor::<[T; 0]>::new())
    }
}

macro_rules! array_impls {
    ($($len:expr => ($($n:tt)+))+) => {
        $(
            impl<'de, T> Visitor<'de> for ArrayVisitor<[T; $len]>
            where
                T: Deserialize<'de>,
            {
                type Value = [T; $len];

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str(concat!("an array of length ", $len))
                }

                #[inline]
                fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where
                    A: SeqAccess<'de>,
                {
                    Ok([$(
                        match tri!(seq.next_element()) {
                            Some(val) => val,
                            None => return Err(Error::invalid_length($n, &self)),
                        }
                    ),+])
                }
            }

            // lust: in-place deserialization is not ported (the trait default holds)
            #[cfg(any())]
            impl<'a, 'de, T> Visitor<'de> for ArrayInPlaceVisitor<'a, [T; $len]>
            where
                T: Deserialize<'de>,
            {
                type Value = ();

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str(concat!("an array of length ", $len))
                }

                #[inline]
                fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where
                    A: SeqAccess<'de>,
                {
                    let mut fail_idx = None;
                    for (idx, dest) in self.0[..].iter_mut().enumerate() {
                        if tri!(seq.next_element_seed(InPlaceSeed(dest))).is_none() {
                            fail_idx = Some(idx);
                            break;
                        }
                    }
                    if let Some(idx) = fail_idx {
                        return Err(Error::invalid_length(idx, &self));
                    }
                    Ok(())
                }
            }

            impl<'de, T> Deserialize<'de> for [T; $len]
            where
                T: Deserialize<'de>,
            {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_tuple($len, ArrayVisitor::<[T; $len]>::new())
                }

            }
        )+
    }
}

array_impls! {
    1 => (0)
    2 => (0 1)
    3 => (0 1 2)
    4 => (0 1 2 3)
    5 => (0 1 2 3 4)
    6 => (0 1 2 3 4 5)
    7 => (0 1 2 3 4 5 6)
    8 => (0 1 2 3 4 5 6 7)
    9 => (0 1 2 3 4 5 6 7 8)
    10 => (0 1 2 3 4 5 6 7 8 9)
    11 => (0 1 2 3 4 5 6 7 8 9 10)
    12 => (0 1 2 3 4 5 6 7 8 9 10 11)
    13 => (0 1 2 3 4 5 6 7 8 9 10 11 12)
    14 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13)
    15 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14)
    16 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)
    17 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16)
    18 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)
    19 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18)
    20 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19)
    21 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20)
    22 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21)
    23 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22)
    24 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23)
    25 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24)
    26 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25)
    27 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26)
    28 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27)
    29 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28)
    30 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29)
    31 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30)
    32 => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31)
}

////////////////////////////////////////////////////////////////////////////////

macro_rules! tuple_impls {
    ($($len:tt => ($($n:tt $name:ident)+))+) => {
        $(
            impl<'de, $($name),+> Deserialize<'de> for ($($name,)+)
            where
                $($name: Deserialize<'de>,)+
            {
                tuple_impl_body!($len => ($($n $name)+));
            }

            tuple_visitor!($len => ($($n $name)+));
        )+
    };
}

// lust: the visitor that upstream's `tuple_impl_body` defines inside
// `deserialize`, at item level (see `PrimitiveVisitor`).
macro_rules! tuple_visitor {
    ($len:tt => ($($n:tt $name:ident)+)) => {
        impl<'de, $($name: Deserialize<'de>),+> Visitor<'de> for TupleVisitor<($($name,)+)> {
            type Value = ($($name,)+);

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str(concat!("a tuple of size ", $len))
            }

            #[inline]
            #[allow(non_snake_case)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                $(
                    let $name = match tri!(seq.next_element()) {
                        Some(value) => value,
                        None => return Err(Error::invalid_length($n, &self)),
                    };
                )+

                Ok(($($name,)+))
            }
        }
    };
}

macro_rules! tuple_impl_body {
    ($len:tt => ($($n:tt $name:ident)+)) => {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_tuple($len, TupleVisitor::<Self> { marker: PhantomData })
        }

    };
}

impl<'de, T> Deserialize<'de> for (T,)
where
    T: Deserialize<'de>,
{
    tuple_impl_body!(1 => (0 T));
}

tuple_visitor!(1 => (0 T));

tuple_impls! {
    2  => (0 T0 1 T1)
    3  => (0 T0 1 T1 2 T2)
    4  => (0 T0 1 T1 2 T2 3 T3)
    5  => (0 T0 1 T1 2 T2 3 T3 4 T4)
    6  => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5)
    7  => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6)
    8  => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7)
    9  => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8)
    10 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9)
    11 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10)
    12 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11)
    13 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12)
    14 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13)
    15 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14)
    16 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15)
}

////////////////////////////////////////////////////////////////////////////////

macro_rules! map_impl {
    (
        $(#[$attr:meta])*
        $ty:ident <K $(: $kbound1:ident $(+ $kbound2:ident)*)*, V $(, $typaram:ident : $bound1:ident $(+ $bound2:ident)*)*>,
        $access:ident,
        $with_capacity:expr,
    ) => {
        $(#[$attr])*
        impl<'de, K, V $(, $typaram)*> Visitor<'de> for MapVisitor<$ty<K, V $(, $typaram)*>>
        where
            K: Deserialize<'de> $(+ $kbound1 $(+ $kbound2)*)*,
            V: Deserialize<'de>,
            $($typaram: $bound1 $(+ $bound2)*),*
        {
            type Value = $ty<K, V $(, $typaram)*>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a map")
            }

            #[inline]
            fn visit_map<A>(self, mut $access: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = $with_capacity;

                while let Some((key, value)) = tri!($access.next_entry()) {
                    values.insert(key, value);
                }

                Ok(values)
            }
        }

        $(#[$attr])*
        impl<'de, K, V $(, $typaram)*> Deserialize<'de> for $ty<K, V $(, $typaram)*>
        where
            K: Deserialize<'de> $(+ $kbound1 $(+ $kbound2)*)*,
            V: Deserialize<'de>,
            $($typaram: $bound1 $(+ $bound2)*),*
        {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let visitor = MapVisitor::<$ty<K, V $(, $typaram)*>> { marker: PhantomData };
                deserializer.deserialize_map(visitor)
            }
        }
    }
}

map_impl! {
    #[cfg(any(feature = "std", feature = "alloc"))]
    BTreeMap<K: Ord, V>,
    map,
    BTreeMap::new(),
}

map_impl! {
    #[cfg(feature = "std")]
    HashMap<K: Eq + Hash, V, S: BuildHasher + Default>,
    map,
    HashMap::with_capacity_and_hasher(size_hint::cautious::<(K, V)>(map.size_hint()), S::default()),
}

////////////////////////////////////////////////////////////////////////////////

macro_rules! parse_ip_impl {
    ($ty:ty, $expecting:expr, $size:tt) => {
        impl<'de> Deserialize<'de> for $ty {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                if deserializer.is_human_readable() {
                    deserializer.deserialize_str(FromStrVisitor::new($expecting))
                } else {
                    <[u8; $size]>::deserialize(deserializer).map(<$ty>::from)
                }
            }
        }
    };
}

macro_rules! variant_identifier {
    (
        $name_kind:ident ($($variant:ident; $bytes:expr; $index:expr),*)
        $expecting_message:expr,
        $variants_name:ident
    ) => {
        enum $name_kind {
            $($variant),*
        }

        static $variants_name: &[&str] = &[$(stringify!($variant)),*];

        impl<'de> Deserialize<'de> for $name_kind {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct KindVisitor;

                impl<'de> Visitor<'de> for KindVisitor {
                    type Value = $name_kind;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str($expecting_message)
                    }

                    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
                    where
                        E: Error,
                    {
                        match value {
                            $(
                                $index => Ok($name_kind :: $variant),
                            )*
                            _ => Err(Error::invalid_value(Unexpected::Unsigned(value), &self),),
                        }
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
                    where
                        E: Error,
                    {
                        match value {
                            $(
                                stringify!($variant) => Ok($name_kind :: $variant),
                            )*
                            _ => Err(Error::unknown_variant(value, $variants_name)),
                        }
                    }

                    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
                    where
                        E: Error,
                    {
                        match value {
                            $(
                                $bytes => Ok($name_kind :: $variant),
                            )*
                            _ => {
                                match str::from_utf8(value) {
                                    Ok(value) => Err(Error::unknown_variant(value, $variants_name)),
                                    Err(_) => Err(Error::invalid_value(Unexpected::Bytes(value), &self)),
                                }
                            }
                        }
                    }
                }

                deserializer.deserialize_identifier(KindVisitor)
            }
        }
    }
}

macro_rules! deserialize_enum {
    (
        $name:ident $name_kind:ident ($($variant:ident; $bytes:expr; $index:expr),*)
        $expecting_message:expr,
        $deserializer:expr
    ) => {
        variant_identifier! {
            $name_kind ($($variant; $bytes; $index),*)
            $expecting_message,
            VARIANTS
        }

        struct EnumVisitor;
        impl<'de> Visitor<'de> for EnumVisitor {
            type Value = $name;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str(concat!("a ", stringify!($name)))
            }


            fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
            where
                A: EnumAccess<'de>,
            {
                match tri!(data.variant()) {
                    $(
                        ($name_kind :: $variant, v) => v.newtype_variant().map($name :: $variant),
                    )*
                }
            }
        }
        $deserializer.deserialize_enum(stringify!($name), VARIANTS, EnumVisitor)
    }
}

// lust: not ported yet (fn-local impls): `impl<'de> Deserialize<'de> for net::IpAddr`

// lust: not ported yet (fn-local impls): the parse_ip_impl expansion for net::Ipv4Addr

// lust: not ported yet (fn-local impls): the parse_ip_impl expansion for net::Ipv6Addr

macro_rules! parse_socket_impl {
    (
        $ty:ty, $expecting:tt,
        $new:expr,
    ) => {
        impl<'de> Deserialize<'de> for $ty {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                if deserializer.is_human_readable() {
                    deserializer.deserialize_str(FromStrVisitor::new($expecting))
                } else {
                    <(_, u16)>::deserialize(deserializer).map($new)
                }
            }
        }
    };
}

// lust: not ported yet (fn-local impls): `impl<'de> Deserialize<'de> for net::SocketAddr`

// lust: not ported yet (fn-local impls): the parse_socket_impl expansion for net::SocketAddrV4

// lust: not ported yet (fn-local impls): the parse_socket_impl expansion for net::SocketAddrV6

////////////////////////////////////////////////////////////////////////////////

// lust: lust has no `Path::new` of a `str` yet: `struct PathVisitor;`

// lust: lust has no `Path::new` of a `str` yet: `impl<'a> Visitor<'a> for PathVisitor`

// lust: lust has no `Path::new` of a `str` yet: `impl<'de: 'a, 'a> Deserialize<'de> for &'a Path`

#[cfg(feature = "std")]
struct PathBufVisitor;

#[cfg(feature = "std")]
impl<'de> Visitor<'de> for PathBufVisitor {
    type Value = PathBuf;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("path string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(From::from(v))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(From::from(v))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        str::from_utf8(v)
            .map(From::from)
            .map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        String::from_utf8(v)
            .map(From::from)
            .map_err(|e| Error::invalid_value(Unexpected::Bytes(&e.into_bytes()), &self))
    }
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for PathBuf {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(PathBufVisitor)
    }
}

// lust: lust has no PathBuf::into_boxed_path yet: the forwarded_impl expansion for Box

////////////////////////////////////////////////////////////////////////////////

// If this were outside of the serde crate, it would just use:
//
//    #[derive(Deserialize)]
//    #[serde(variant_identifier)]
#[cfg(all(feature = "std", any(unix, windows)))]
// lust: not ported yet (fn-local impls): the variant_identifier expansion for OsStringKind

// lust: not ported yet (fn-local impls): `struct OsStringVisitor;`

// lust: not ported yet (fn-local impls): `impl<'de> Visitor<'de> for OsStringVisitor`

// lust: not ported yet (fn-local impls): `impl<'de> Deserialize<'de> for OsString`

////////////////////////////////////////////////////////////////////////////////

forwarded_impl! {
    #[cfg(any(feature = "std", feature = "alloc"))]
    (T), Box<T>, Box::new
}

// lust: lust has no Vec::into_boxed_slice yet: the forwarded_impl expansion for Box

// lust: lust has no String::into_boxed_str yet: the forwarded_impl expansion for Box

// lust: lust has no OsString::into_boxed_os_str yet: the forwarded_impl expansion for Box

// lust: not ported yet: its `T::Owned: Deserialize<'de>` where-clause carries a lifetime lust's region check does not track yet: `impl<'de, 'a, T> Deserialize<'de> for Cow<'a, T>`

////////////////////////////////////////////////////////////////////////////////

/// This impl requires the [`"rc"`] Cargo feature of Serde. The resulting
/// `Weak<T>` has a reference count of 0 and cannot be upgraded.
///
/// [`"rc"`]: https://serde.rs/feature-flags.html#-features-rc
#[cfg(all(feature = "rc", any(feature = "std", feature = "alloc")))]
impl<'de, T> Deserialize<'de> for RcWeak<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        tri!(Option::<T>::deserialize(deserializer));
        Ok(RcWeak::new())
    }
}

/// This impl requires the [`"rc"`] Cargo feature of Serde. The resulting
/// `Weak<T>` has a reference count of 0 and cannot be upgraded.
///
/// [`"rc"`]: https://serde.rs/feature-flags.html#-features-rc
#[cfg(all(feature = "rc", any(feature = "std", feature = "alloc")))]
impl<'de, T> Deserialize<'de> for ArcWeak<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        tri!(Option::<T>::deserialize(deserializer));
        Ok(ArcWeak::new())
    }
}

////////////////////////////////////////////////////////////////////////////////

macro_rules! box_forwarded_impl {
    (
        $(#[$attr:meta])*
        $t:ident
    ) => {
        $(#[$attr])*
        impl<'de, T> Deserialize<'de> for $t<T>
        where
            T: ?Sized,
            Box<T>: Deserialize<'de>,
        {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Box::deserialize(deserializer).map(Into::into)
            }
        }
    };
}

box_forwarded_impl! {
    /// This impl requires the [`"rc"`] Cargo feature of Serde.
    ///
    /// Deserializing a data structure containing `Rc` will not attempt to
    /// deduplicate `Rc` references to the same data. Every deserialized `Rc`
    /// will end up with a strong count of 1.
    ///
    /// [`"rc"`]: https://serde.rs/feature-flags.html#-features-rc
    #[cfg(all(feature = "rc", any(feature = "std", feature = "alloc")))]
    Rc
}

box_forwarded_impl! {
    /// This impl requires the [`"rc"`] Cargo feature of Serde.
    ///
    /// Deserializing a data structure containing `Arc` will not attempt to
    /// deduplicate `Arc` references to the same data. Every deserialized `Arc`
    /// will end up with a strong count of 1.
    ///
    /// [`"rc"`]: https://serde.rs/feature-flags.html#-features-rc
    #[cfg(all(feature = "rc", any(feature = "std", feature = "alloc")))]
    Arc
}

////////////////////////////////////////////////////////////////////////////////

impl<'de, T> Deserialize<'de> for Cell<T>
where
    T: Deserialize<'de> + Copy,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // lust: std fns as values are not supported yet; upstream maps
        // `Cell::new`.
        T::deserialize(deserializer).map(|value| Cell::new(value))
    }
}

forwarded_impl! {
    (T), RefCell<T>, |value| RefCell::new(value) // lust: upstream passes `RefCell::new`
}

forwarded_impl! {
    #[cfg(feature = "std")]
    (T), Mutex<T>, |value| Mutex::new(value) // lust: upstream passes `Mutex::new`
}

forwarded_impl! {
    #[cfg(feature = "std")]
    (T), RwLock<T>, |value| RwLock::new(value) // lust: upstream passes `RwLock::new`
}

////////////////////////////////////////////////////////////////////////////////

// This is a cleaned-up version of the impl generated by:
//
//     #[derive(Deserialize)]
//     #[serde(deny_unknown_fields)]
//     struct Duration {
//         secs: u64,
//         nanos: u32,
//     }
// lust: not ported yet (fn-local impls): `impl<'de> Deserialize<'de> for Duration`

////////////////////////////////////////////////////////////////////////////////

// lust: not ported yet (fn-local impls): `impl<'de> Deserialize<'de> for SystemTime`

////////////////////////////////////////////////////////////////////////////////

// Similar to:
//
//     #[derive(Deserialize)]
//     #[serde(deny_unknown_fields)]
//     struct Range<Idx> {
//         start: Idx,
//         end: Idx,
//     }
// lust: `Range` over a generic index is not supported yet: `impl<'de, Idx> Deserialize<'de> for Range<Idx>`

// lust: `Range` over a generic index is not supported yet: `impl<'de, Idx> Deserialize<'de> for RangeInclusive<Idx>`

// lust: `Range` over a generic index is not supported yet: `mod range`

////////////////////////////////////////////////////////////////////////////////

// Similar to:
//
//     #[derive(Deserialize)]
//     #[serde(deny_unknown_fields)]
//     struct RangeFrom<Idx> {
//         start: Idx,
//     }
// lust: `Range` over a generic index is not supported yet: `impl<'de, Idx> Deserialize<'de> for RangeFrom<Idx>`

// lust: `Range` over a generic index is not supported yet: `mod range_from`

////////////////////////////////////////////////////////////////////////////////

// Similar to:
//
//     #[derive(Deserialize)]
//     #[serde(deny_unknown_fields)]
//     struct RangeTo<Idx> {
//         end: Idx,
//     }
// lust: `Range` over a generic index is not supported yet: `impl<'de, Idx> Deserialize<'de> for RangeTo<Idx>`

// lust: `Range` over a generic index is not supported yet: `mod range_to`

////////////////////////////////////////////////////////////////////////////////

// lust: not ported yet (fn-local impls): `impl<'de, T> Deserialize<'de> for Bound<T>`

////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "result")]
impl<'de, T, E> Deserialize<'de> for Result<T, E>
where
    T: Deserialize<'de>,
    E: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_enum("Result", result::VARIANTS, result::ResultVisitor(PhantomData))
    }
}

// lust: the items upstream defines inside `Result`'s `deserialize`, at
// module level (an impl there that names the fn's own `Field` enum does
// not resolve when the impl is instantiated yet).
#[cfg(feature = "result")]
mod result {
    use super::*;

    // If this were outside of the serde crate, it would just use:
    //
    //    #[derive(Deserialize)]
    //    #[serde(variant_identifier)]
    pub enum Field {
        Ok,
        Err,
    }

    impl<'de> Deserialize<'de> for Field {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(FieldVisitor)
        }
    }

    struct FieldVisitor;

    impl<'de> Visitor<'de> for FieldVisitor {
        type Value = Field;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("`Ok` or `Err`")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: Error,
        {
            match value {
                0 => Ok(Field::Ok),
                1 => Ok(Field::Err),
                _ => Err(Error::invalid_value(Unexpected::Unsigned(value), &self)),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: Error,
        {
            match value {
                "Ok" => Ok(Field::Ok),
                "Err" => Ok(Field::Err),
                _ => Err(Error::unknown_variant(value, VARIANTS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: Error,
        {
            match value {
                b"Ok" => Ok(Field::Ok),
                b"Err" => Ok(Field::Err),
                _ => match str::from_utf8(value) {
                    Ok(value) => Err(Error::unknown_variant(value, VARIANTS)),
                    Err(_) => {
                        Err(Error::invalid_value(Unexpected::Bytes(value), &self))
                    }
                },
            }
        }
    }

    pub struct ResultVisitor<T, E>(pub PhantomData<Result<T, E>>);

    impl<'de, T, E> Visitor<'de> for ResultVisitor<T, E>
    where
        T: Deserialize<'de>,
        E: Deserialize<'de>,
    {
        type Value = Result<T, E>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("enum Result")
        }

        fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
        where
            A: EnumAccess<'de>,
        {
            match tri!(data.variant()) {
                (Field::Ok, v) => v.newtype_variant().map(Ok),
                (Field::Err, v) => v.newtype_variant().map(Err),
            }
        }
    }

    pub const VARIANTS: &[&str] = &["Ok", "Err"];
}

////////////////////////////////////////////////////////////////////////////////

// lust: lust has no Wrapping yet: `impl<'de, T> Deserialize<'de> for Wrapping<T>`

#[cfg(feature = "std")]
macro_rules! atomic_impl {
    ($($ty:ident $size:expr)*) => {
        $(
            #[cfg(target_has_atomic = $size)]
            impl<'de> Deserialize<'de> for $ty {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    // lust: upstream maps `Self::new` (a fn value); `Self` on a
                    // std atomic is not resolved yet.
                    Deserialize::deserialize(deserializer).map(|value| $ty::new(value))
                }
            }
        )*
    };
}

#[cfg(feature = "std")]
atomic_impl! {
    AtomicBool "8"
    AtomicI8 "8"
    AtomicI16 "16"
    AtomicI32 "32"
    AtomicIsize "ptr"
    AtomicU8 "8"
    AtomicU16 "16"
    AtomicU32 "32"
    AtomicUsize "ptr"
}

#[cfg(feature = "std")]
atomic_impl! {
    AtomicI64 "64"
    AtomicU64 "64"
}

struct FromStrVisitor<T> {
    expecting: &'static str,
    ty: PhantomData<T>,
}

impl<T> FromStrVisitor<T> {
    fn new(expecting: &'static str) -> Self {
        FromStrVisitor {
            expecting,
            ty: PhantomData,
        }
    }
}

impl<'de, T> Visitor<'de> for FromStrVisitor<T>
where
    T: str::FromStr,
    T::Err: fmt::Display,
{
    type Value = T;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(self.expecting)
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        s.parse().map_err(Error::custom)
    }
}
