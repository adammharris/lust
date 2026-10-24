// expect: L0307
// ARCH 2.8, rustc E0515: the dyn reference would point at a dead local.
trait Tr { fn m(&self) -> u8; }
struct S;
impl Tr for S { fn m(&self) -> u8 { 1 } }
fn mk() -> &'static dyn Tr { let s = S; &s }
fn main() { println!("{}", mk().m()); }
