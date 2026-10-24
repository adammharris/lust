// `T: DeserializeOwned` and `T: for<'de> Deserialize<'de>` passed on to a
// `DeserializeOwned` callee, and called with two inputs of different lifetimes.
use std::fmt;
pub trait Error: Sized + fmt::Debug + fmt::Display { fn custom<T: fmt::Display>(msg: T) -> Self; }
pub trait Visitor<'de>: Sized {
    type Value;
    fn visit_i64<E: Error>(self, v: i64) -> Result<Self::Value, E> { let _ = v; Err(E::custom("i64")) }
    fn visit_str<E: Error>(self, v: &str) -> Result<Self::Value, E> { let _ = v; Err(E::custom("str")) }
    fn visit_borrowed_str<E: Error>(self, v: &'de str) -> Result<Self::Value, E> { self.visit_str(v) }
}
pub trait Deserializer<'de>: Sized {
    type Error: Error;
    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error>;
}
pub trait Deserialize<'de>: Sized {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error>;
}
pub trait DeserializeOwned: for<'de> Deserialize<'de> {}
impl<T> DeserializeOwned for T where T: for<'de> Deserialize<'de> {}

#[derive(Debug)] struct E(String);
impl fmt::Display for E { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(&self.0) } }
impl Error for E { fn custom<T: fmt::Display>(m: T) -> Self { E(m.to_string()) } }

struct Src<'a>(&'a str);
impl<'de> Deserializer<'de> for Src<'de> {
    type Error = E;
    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, E> {
        match self.0.parse::<i64>() { Ok(n) => v.visit_i64(n), Err(_) => v.visit_borrowed_str(self.0) }
    }
}
struct IV;
impl<'de> Visitor<'de> for IV { type Value = i64; fn visit_i64<E2: Error>(self, v: i64) -> Result<i64, E2> { Ok(v) } }
impl<'de> Deserialize<'de> for i64 { fn deserialize<D: Deserializer<'de>>(d: D) -> Result<i64, D::Error> { d.deserialize_any(IV) } }
struct SV;
impl<'de> Visitor<'de> for SV { type Value = &'de str; fn visit_borrowed_str<E2: Error>(self, v: &'de str) -> Result<&'de str, E2> { Ok(v) } }
impl<'de: 'a, 'a> Deserialize<'de> for &'a str { fn deserialize<D: Deserializer<'de>>(d: D) -> Result<&'a str, D::Error> { d.deserialize_any(SV) } }
fn from_str<'a, T: Deserialize<'a>>(s: &'a str) -> Result<T, E> { T::deserialize(Src(s)) }
fn owned<T: DeserializeOwned>(s: &str) -> Result<T, E> { T::deserialize(Src(s)) }
fn pass<T: DeserializeOwned>(s: &str) -> Result<T, E> { owned::<T>(s) }
fn pass2<T: for<'de> Deserialize<'de>>(s: &str) -> Result<T, E> { owned::<T>(s) }
fn main1() { let s = String::from("5"); println!("{:?} {:?}", pass::<i64>(&s), pass2::<i64>(&s)); }
fn twice<T: for<'de> Deserialize<'de>>(a: &str, b: &str) -> (Result<T, E>, Result<T, E>) { (T::deserialize(Src(a)), T::deserialize(Src(b))) }
fn main() { main1(); let x = String::from("1"); let r = { let y = String::from("2"); twice::<i64>(&x, &y) }; println!("{:?}", r); }
