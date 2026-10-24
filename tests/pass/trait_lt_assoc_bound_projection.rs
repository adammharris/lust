// A projection (`<T as IntoDe<'de>>::D`) bounded by a lifetime trait in
// its trait (`type D: Deserializer<'de>`) implements it with the outer
// trait's lifetimes, read off T's bound (serde's `into_deserializer`).
trait Deserializer<'de> { fn take(self) -> &'de str; }
trait IntoDe<'de> { type D: Deserializer<'de>; fn into_de(self) -> Self::D; }
struct StrDe<'a>(&'a str);
impl<'de> Deserializer<'de> for StrDe<'de> { fn take(self) -> &'de str { self.0 } }
impl<'de> IntoDe<'de> for &'de str { type D = StrDe<'de>; fn into_de(self) -> StrDe<'de> { StrDe(self) } }
trait Seed<'de> { type Value; fn deserialize<D: Deserializer<'de>>(self, d: D) -> Self::Value; }
struct Grab;
impl<'de> Seed<'de> for Grab { type Value = &'de str; fn deserialize<D: Deserializer<'de>>(self, d: D) -> &'de str { d.take() } }
fn go<'de, T: IntoDe<'de>, S: Seed<'de>>(t: T, s: S) -> S::Value { s.deserialize(t.into_de()) }
fn main() {
    let owned = String::from("hi");
    println!("{}", go(owned.as_str(), Grab));
}
