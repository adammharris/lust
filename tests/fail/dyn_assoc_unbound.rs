// expect: L0110
// rustc E0191: a dyn type must bind every associated type of its trait.
trait Tr { type Out; fn get(&self) -> Self::Out; }
fn f(_x: &dyn Tr) {}
fn main() {}
