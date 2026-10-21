// `#[diagnostic::...]` attributes only shape rustc's error messages, so
// they are accepted and ignored (serde writes them on its traits).
#[diagnostic::on_unimplemented(message = "the trait `Shape` is not implemented for `{Self}`", note = "add an impl")]
trait Shape {
    fn sides(&self) -> u32;
}
struct Square;
#[diagnostic::do_not_recommend]
impl Shape for Square {
    fn sides(&self) -> u32 {
        4
    }
}
fn main() {
    println!("{}", Square.sides());
}
