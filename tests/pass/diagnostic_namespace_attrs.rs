// `#[diagnostic::..]` attributes only shape rustc's messages (serde's
// `on_unimplemented` and `do_not_recommend`); an unknown one is a warning.
#[diagnostic::on_unimplemented(message = "`{Self}` cannot be shown", label = "not showable")]
trait Show {
    fn show(&self) -> String;
}
#[diagnostic::do_not_recommend]
impl Show for u8 {
    fn show(&self) -> String { format!("u8 {}", self) }
}
#[allow(unknown_or_malformed_diagnostic_attributes)]
#[diagnostic::not_a_real_one]
fn main() {
    println!("{}", 7u8.show());
}
