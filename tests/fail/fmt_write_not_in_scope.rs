// expect: L0104
// rustc E0599: `write_fmt` on `String` needs `fmt::Write` in scope.
fn main() { let mut s = String::new(); s.write_fmt(format_args!("x")).unwrap(); println!("{s}"); }
