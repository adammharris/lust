// A `&dyn Source<Item = u8>`: the binding fixes the object's associated
// type, and the method through the vtable returns it.
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
