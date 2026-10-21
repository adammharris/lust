// expect: L0612
// rustc E0271: `Lit`'s `Out` is `u8`, so it is no `dyn Rule<Out = String>`.
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
fn main() {
    let r: Box<dyn Rule<Out = String>> = Box::new(Lit(3));
    println!("{}", r.m());
}
