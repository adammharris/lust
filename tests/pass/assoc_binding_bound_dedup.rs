// Two associated types tied by a binding, each with the same bound
// (serde's `type SerializeSeq: SerializeSeq<Error = Self::Error>` with
// `type Error: Error` in both traits): the param env proves `S::Error:
// Error` twice, and that is one piece of evidence, not an ambiguity.
use std::fmt::Display;
pub trait Error: Sized + std::error::Error {
    fn custom<T: Display>(msg: T) -> Self;
}
pub trait SerializeSeq {
    type Ok;
    type Error: Error;
    fn end(self) -> Result<Self::Ok, Self::Error>;
}
pub trait Serializer: Sized {
    type Ok;
    type Error: Error;
    type SerializeSeq: SerializeSeq<Ok = Self::Ok, Error = Self::Error>;
    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error>;
    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error>;
}
pub trait Serialize {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>;
}
impl Serialize for bool {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bool(*self)
    }
}
fn fail<S: Serializer>() -> S::Error {
    <S::Error as Error>::custom("no")
}
#[derive(Debug)]
struct E(String);
impl std::fmt::Display for E {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { f.write_str(&self.0) }
}
impl std::error::Error for E {}
impl Error for E {
    fn custom<T: Display>(msg: T) -> Self { E(msg.to_string()) }
}
struct Out;
impl SerializeSeq for Out {
    type Ok = String;
    type Error = E;
    fn end(self) -> Result<String, E> { Ok("]".into()) }
}
struct Ser;
impl Serializer for Ser {
    type Ok = String;
    type Error = E;
    type SerializeSeq = Out;
    fn serialize_bool(self, v: bool) -> Result<String, E> { Ok(v.to_string()) }
    fn serialize_seq(self, _: Option<usize>) -> Result<Out, E> { Ok(Out) }
}
fn main() {
    println!("{:?} {}", true.serialize(Ser), fail::<Ser>());
    println!("{:?}", Ser.serialize_seq(None).and_then(|s| s.end()));
}
