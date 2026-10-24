// expect: L0306
// rustc E0597: a `&'static dyn T` parameter needs a 'static reference.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
fn show(d: &'static dyn T) -> u32 { d.read() }
fn main() { let s = S { n: 1 }; println!("{}", show(&s)); }
