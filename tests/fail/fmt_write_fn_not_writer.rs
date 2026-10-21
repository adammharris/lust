// expect: L0612
// rustc E0277: `fmt::write` needs a `fmt::Write` writer; a u8 is none.
use std::fmt;
fn main() {
    let mut n = 5u8;
    let _ = fmt::write(&mut n, format_args!("{}", 1));
}
