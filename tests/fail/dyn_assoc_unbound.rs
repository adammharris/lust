// expect: L0110
// ARCH 2.8, rustc E0191: a dyn type must bind every associated type.
trait Tr { type Out; fn get(&self) -> Self::Out; }
fn f(_x: &dyn Tr) {}
fn main() {}
