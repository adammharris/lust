// As trait_lt_where_binding_param, returning the items at the caller's `'de`.
trait IntoDe<'de> { fn s(self) -> &'de str; }
impl<'de> IntoDe<'de> for &'de str { fn s(self) -> &'de str { self } }
trait SeqAccess<'de> { fn next(&mut self) -> Option<&'de str>; }
impl<'de, 'a, A: SeqAccess<'de> + ?Sized> SeqAccess<'de> for &'a mut A {
    fn next(&mut self) -> Option<&'de str> { (**self).next() }
}
struct Seq<I> { iter: I }
impl<'de, I, T> SeqAccess<'de> for Seq<I> where I: Iterator<Item = T>, T: IntoDe<'de> {
    fn next(&mut self) -> Option<&'de str> { self.iter.next().map(|t| t.s()) }
}
fn first<'de, A: SeqAccess<'de>>(mut a: A) -> Option<&'de str> { a.next() }
fn ok<'de, I: Iterator<Item = T>, T: IntoDe<'de>>(s: Seq<I>) -> Option<&'de str> {
    let mut s = s;
    first(&mut s)
}
fn main() {
    let owned = String::from("x");
    let v = vec![owned.as_str()];
    println!("{:?}", ok(Seq { iter: v.into_iter() }));
}
