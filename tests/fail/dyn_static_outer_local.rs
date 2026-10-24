// expect: L0306
// rustc E0597: `&'static dyn T` needs a reference that lives for 'static; `&s` does not.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
fn main() { let s = S { n: 8 }; let d: &'static dyn T = &s; println!("{}", d.read()); }
