// expect: L0106
// rustc E0719: a dyn type binds each associated type once.
trait Rule { type Out; fn get(&self) -> Self::Out; }
fn f(_r: &dyn Rule<Out = u8, Out = u8>) {}
fn main() {}
