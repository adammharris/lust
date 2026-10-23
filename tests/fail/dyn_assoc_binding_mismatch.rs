// expect: L0110
// rustc E0308: dyn types that differ in a binding are different types.
trait Rule {
    type Out;
    fn get(&self) -> Self::Out;
}
struct Len;
impl Rule for Len {
    type Out = usize;
    fn get(&self) -> usize { 3 }
}
fn main() { let a: Box<dyn Rule<Out = usize>> = Box::new(Len); let _b: Box<dyn Rule<Out = u8>> = a; }
