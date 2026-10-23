// expect: L0612
// rustc E0310: an associated type whose bound is not `'static`.
trait B {}
trait F { type Bits: B; }
fn need<T: 'static>() {}
#[allow(dead_code)]
fn f<X: F>() { need::<X::Bits>(); }
fn main() {}
