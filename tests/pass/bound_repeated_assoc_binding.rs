// A generic bound may repeat a binding (rustc E0719 is for dyn and impl Trait).
trait Rule {
    type Out;
    fn get(&self) -> Self::Out;
}
struct Len;
impl Rule for Len {
    type Out = usize;
    fn get(&self) -> usize { 3 }
}
fn f<T: Rule<Out = u8, Out = u8>>(_t: T) {}
fn main() { println!("ok"); }
