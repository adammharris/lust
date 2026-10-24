// expect: L0612
// rustc E0277: a closure over a `Cell` is not `RefUnwindSafe`.
use std::cell::Cell;
use std::panic::RefUnwindSafe;
fn main() {
    let c = Cell::new(1);
    let _b: Box<dyn Fn() -> i32 + RefUnwindSafe> = Box::new(move || c.get());
}
