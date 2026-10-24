// expect: L0733
// rustc: lifetime may not live long enough: `T::D` is a
// `Deserializer<'de>`, not a `Deserializer<'static>`.
trait Deserializer<'de> { fn take(self) -> &'de str; }
trait IntoDe<'de> { type D: Deserializer<'de>; fn into_de(self) -> Self::D; }
fn take_static<D: Deserializer<'static>>(d: D) -> &'static str { d.take() }
fn bad<'de, T: IntoDe<'de>>(t: T) -> &'static str { take_static(t.into_de()) }
fn main() {}
