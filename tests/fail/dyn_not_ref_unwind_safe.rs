// expect: L0612
// rustc E0277: a plain `dyn Tr` is not `RefUnwindSafe`.
use std::panic::RefUnwindSafe;
fn needs_ref<T: RefUnwindSafe + ?Sized>(_t: &T) {}
trait Tr { fn f(&self); }
fn g(x: &dyn Tr) { needs_ref(x) }
fn main() {}
