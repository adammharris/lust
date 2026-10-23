// expect: L0733
// rustc E0521: the stored object's lifetime `'a` must outlive the Vec's
// `'static` object lifetime (only the reference's own lifetime may shorten).
use std::error::Error;
fn f<'a, 'b>(x: &'b (dyn Error + 'a), v: &mut Vec<&'b (dyn Error + 'static)>) {
    v.push(x);
}
fn main() {}
