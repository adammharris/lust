// expect: L0001
// rustc: an element macro that expands to nothing (no cfg) is an error.
macro_rules! nothing { () => {}; }
fn main() { let a = [1, nothing!(), 3]; println!("{a:?}"); }
