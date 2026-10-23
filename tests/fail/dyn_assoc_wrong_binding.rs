// expect: L0612
// rustc E0271: `<Len as Rule>::Out` is usize, not the String the dyn type binds.
trait Rule {
    type Out;
    fn get(&self) -> Self::Out;
}
struct Len;
impl Rule for Len {
    type Out = usize;
    fn get(&self) -> usize { 3 }
}
fn main() { let b: Box<dyn Rule<Out = String>> = Box::new(Len); println!("{}", b.get()); }
