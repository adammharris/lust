// expect: L0306
// rustc E0597: a `&'static dyn T` element needs a 'static reference.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
fn main() { let s = S { n: 1 }; let v: Vec<&'static dyn T> = vec![&s]; println!("{}", v[0].read()); }
