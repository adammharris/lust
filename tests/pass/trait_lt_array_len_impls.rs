// Impls of a lifetime trait for one generic struct at different array
// lengths (serde's `ArrayVisitor<[T; N]>`) are different impls: a call
// through `[T; 0]` selects only its own.
use std::marker::PhantomData;
trait Visitor<'de>: Sized {
    type Value;
    fn visit(self, s: &'de str) -> Self::Value;
}
trait Deserializer<'de>: Sized {
    fn tuple<V: Visitor<'de>>(self, len: usize, v: V) -> V::Value;
}
struct AV<A> {
    marker: PhantomData<A>,
}
impl<A> AV<A> {
    fn new() -> Self { AV { marker: PhantomData } }
}
impl<'de, T> Visitor<'de> for AV<[T; 0]> {
    type Value = [T; 0];
    fn visit(self, _: &'de str) -> [T; 0] { [] }
}
impl<'de, T: From<&'de str>> Visitor<'de> for AV<[T; 1]> {
    type Value = [T; 1];
    fn visit(self, s: &'de str) -> [T; 1] { [T::from(s)] }
}
trait Deserialize<'de>: Sized {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Self;
}
impl<'de, T> Deserialize<'de> for [T; 0] {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Self { d.tuple(0, AV::<[T; 0]>::new()) }
}
impl<'de, T: From<&'de str>> Deserialize<'de> for [T; 1] {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Self { d.tuple(1, AV::<[T; 1]>::new()) }
}
struct S<'a>(&'a str);
impl<'de> Deserializer<'de> for S<'de> {
    fn tuple<V: Visitor<'de>>(self, _: usize, v: V) -> V::Value { v.visit(self.0) }
}
fn main() {
    let s = String::from("x");
    let a: [u8; 0] = Deserialize::deserialize(S(&s));
    let b: [String; 1] = Deserialize::deserialize(S(&s));
    let c: [&str; 1] = Deserialize::deserialize(S(&s));
    println!("{:?} {:?} {:?}", a, b, c);
}
