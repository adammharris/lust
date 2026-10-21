// expect: L0612
// rustc E0277: a closure that captures a `Cell` by reference is not
// `RefUnwindSafe`, so it is no `dyn Fn() + RefUnwindSafe`.
use std::cell::Cell;
use std::panic::RefUnwindSafe;
fn main() {
    let c = Cell::new(1u8);
    let f: Box<dyn Fn() -> u8 + RefUnwindSafe + '_> = Box::new(|| c.get());
    println!("{}", f());
}
