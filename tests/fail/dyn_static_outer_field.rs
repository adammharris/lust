// expect: L0306
// rustc E0597: a `&'static dyn T` field needs a 'static reference.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
struct H { x: &'static dyn T }
fn main() { let s = S { n: 1 }; let h = H { x: &s }; println!("{}", h.x.read()); }
