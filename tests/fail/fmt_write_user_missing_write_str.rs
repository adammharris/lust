// expect: L0110
// rustc E0046: `write_str` is the one method `fmt::Write` requires.
use std::fmt;
struct S;
impl fmt::Write for S {
    fn write_char(&mut self, _: char) -> fmt::Result {
        Ok(())
    }
}
fn main() {
    let _ = S;
}
