// ARCH 2.8: a dyn type binds its trait's associated type, and a call
// through it returns the bound type.
trait Source {
    type Item;
    fn get(&self) -> Self::Item;
}
struct S;
impl Source for S {
    type Item = u8;
    fn get(&self) -> u8 {
        4
    }
}
fn main() {
    let s = S;
    let d: &dyn Source<Item = u8> = &s;
    println!("{}", d.get());
}
