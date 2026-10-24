// expect: L0733
// rustc: lifetime may not live long enough (`self.grab()` in the impl's own
// method borrows for the impl's `'de`).
trait IntoDe<'de> { fn s(self) -> &'de str; }
impl<'de> IntoDe<'de> for &'de str { fn s(self) -> &'de str { self } }
trait Grab<'de>: Sized {
    fn grab(self) -> Option<&'de str>;
    fn leak(self) -> Option<&'static str>;
}
struct Seq<I> { iter: I }
impl<'de, I, T> Grab<'de> for Seq<I> where I: Iterator<Item = T>, T: IntoDe<'de> {
    fn grab(mut self) -> Option<&'de str> { self.iter.next().map(|t| t.s()) }
    fn leak(self) -> Option<&'static str> { self.grab() }
}
fn main() {}
