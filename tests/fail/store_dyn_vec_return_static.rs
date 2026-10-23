// expect: L0705
// rustc: lifetime may not live long enough. The pushed `&'a dyn Error` makes
// the Vec's references `'a`, not the `'static` the return type asks.
use std::error::Error;
fn f<'a>(x: &'a (dyn Error + 'static)) -> Vec<&'static dyn Error> {
    let mut v = Vec::new();
    v.push(x);
    v
}
fn main() {}
