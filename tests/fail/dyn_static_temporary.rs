// expect: L0306
// rustc E0716: `String::from(..)` is no constant, so its temporary is
// dropped at the end of the statement, while the `&'static dyn` holds it.
trait T {
    fn read(&self) -> usize;
}
impl T for String {
    fn read(&self) -> usize {
        self.len()
    }
}
fn main() {
    let d: &'static dyn T = &String::from("abc");
    println!("{}", d.read());
}
