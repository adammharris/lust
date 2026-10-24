// expect: L0306
// rustc E0597: a field of a local is no `'static` place.
trait L { fn n(&self) -> usize; }
struct J;
impl L for J { fn n(&self) -> usize { 1 } }
struct H { j: J }
fn take(l: &'static dyn L) -> usize { l.n() }
fn main() { let h = H { j: J }; println!("{}", take(&h.j)); }
