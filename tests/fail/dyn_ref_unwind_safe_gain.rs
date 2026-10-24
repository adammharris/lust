// expect: L0110
// rustc E0308: a dyn value without `RefUnwindSafe` cannot gain it.
use std::panic::RefUnwindSafe;
fn main() {
    let a: Box<dyn Fn() -> i32 + Send> = Box::new(|| 1);
    let _b: Box<dyn Fn() -> i32 + Send + RefUnwindSafe> = a;
}
