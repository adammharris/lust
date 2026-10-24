// expect: L0110
// rustc E0308: an upcast keeps the binding; u8 is not u16.
trait Rule { type Out; fn get(&self) -> Option<Self::Out>; }
trait Sub: Rule {}
fn upcast(b: Box<dyn Sub<Out = u8>>) -> Box<dyn Rule<Out = u16>> { b }
fn main() {}
