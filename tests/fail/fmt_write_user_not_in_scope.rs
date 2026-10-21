// expect: L0104
// rustc E0599: a user writer's `write_str` comes from fmt::Write, which
// main's module does not import.
mod w {
    use std::fmt::{self, Write};
    pub struct S(pub String);
    impl Write for S {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.0.push_str(s);
            Ok(())
        }
    }
}
fn main() {
    let mut s = w::S(String::new());
    s.write_str("a").unwrap();
    println!("{}", s.0);
}
