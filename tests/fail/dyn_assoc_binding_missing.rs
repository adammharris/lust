// expect: L0110
// rustc E0191: a dyn type fixes every associated type of its trait.
trait Rule {
    type Out;
    fn m(&self) -> Self::Out;
}
struct Lit(u8);
impl Rule for Lit {
    type Out = u8;
    fn m(&self) -> u8 {
        self.0
    }
}
fn show(r: &dyn Rule) {
    let _ = r;
}
fn main() {
    show(&Lit(3));
}
