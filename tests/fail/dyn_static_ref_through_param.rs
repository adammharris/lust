// expect: L0733
// rustc E0521: `&**b` borrows through a parameter's lifetime, not `'static`.
trait L { fn n(&self) -> usize; }
struct J;
impl L for J { fn n(&self) -> usize { 1 } }
fn take(l: &'static dyn L) -> usize { l.n() }
fn f(b: &Box<dyn L>) -> usize { take(&**b) }
fn main() { println!("{}", f(&(Box::new(J) as Box<dyn L>))); }
