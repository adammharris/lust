// expect: L0306
// rustc E0597: `&*a` borrows a local `Arc`, which does not live for `'static`.
use std::sync::Arc;
trait L { fn n(&self) -> usize; }
struct J;
impl L for J { fn n(&self) -> usize { 1 } }
fn take(l: &'static dyn L) -> usize { l.n() }
fn main() { let a: Arc<dyn L> = Arc::new(J); println!("{}", take(&*a)); }
