// rustc promotes `&S { n: 5 }` to a 'static constant, so it is a
// `&'static dyn T`; the borrow checker proves it (once a reject).
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
fn main() { let d: &'static dyn T = &S { n: 5 }; println!("{}", d.read()); }
