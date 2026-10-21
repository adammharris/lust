// expect: L0612
// rustc E0277: `RefCell` is not `RefUnwindSafe`, so `S` cannot implement
// a trait that requires it.
use std::cell::RefCell;
use std::panic::RefUnwindSafe;
trait Lang: RefUnwindSafe {
    fn n(&self) -> u8;
}
struct S {
    c: RefCell<u8>,
}
impl Lang for S {
    fn n(&self) -> u8 {
        *self.c.borrow()
    }
}
fn main() {
    println!("{}", S { c: RefCell::new(1) }.n());
}
