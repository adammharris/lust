// An impl whose trait lifetime `'de` its Self type does not name, fixed by
// `T: IntoDe<'de>` with `T` from `I: Iterator<Item = T>` (serde's
// SeqDeserializer): a call through the `&mut A` blanket impl and one of the
// impl's own methods read `'de` from the caller's matching bound.
trait IntoDe<'de> { fn get(self) -> usize; }
impl<'de> IntoDe<'de> for u8 { fn get(self) -> usize { self as usize } }
trait SeqAccess<'de> { fn next(&mut self) -> Option<usize>; }
impl<'de, 'a, A: SeqAccess<'de> + ?Sized> SeqAccess<'de> for &'a mut A {
    fn next(&mut self) -> Option<usize> { (**self).next() }
}
trait Visitor<'de>: Sized {
    type Value;
    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Option<Self::Value>;
}
struct Seq<I> { iter: I }
impl<'de, I, T> SeqAccess<'de> for Seq<I> where I: Iterator<Item = T>, T: IntoDe<'de> {
    fn next(&mut self) -> Option<usize> { self.iter.next().map(|t| t.get()) }
}
trait Deserializer<'de>: Sized { fn any<V: Visitor<'de>>(self, v: V) -> Option<V::Value>; fn other<V: Visitor<'de>>(self, v: V) -> Option<V::Value>; }
impl<'de, I, T> Deserializer<'de> for Seq<I> where I: Iterator<Item = T>, T: IntoDe<'de> {
    fn any<V: Visitor<'de>>(mut self, v: V) -> Option<V::Value> {
        let out = v.visit_seq(&mut self);
        out
    }
    fn other<V: Visitor<'de>>(self, v: V) -> Option<V::Value> { self.any(v) }
}
struct Count;
impl<'de> Visitor<'de> for Count {
    type Value = usize;
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Option<usize> { let mut n = 0; while let Some(x) = seq.next() { n += x; } Some(n) }
}
fn main() {
    let d = Seq { iter: vec![1u8, 2].into_iter() };
    println!("{:?}", d.other(Count));
}
