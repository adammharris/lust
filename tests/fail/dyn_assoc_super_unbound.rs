// expect: L0110
// rustc E0191: a supertrait's associated type needs a binding too.
trait Base { type Out; fn get(&self) -> Self::Out; }
trait Sub: Base { fn name(&self) -> &'static str; }
fn f(_r: &dyn Sub) {}
fn main() {}
