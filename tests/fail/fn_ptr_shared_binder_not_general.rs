// expect: L0110
// rustc E0308 (one type is more general than the other): a fn that takes
// `&'static` inputs is no pointer whose binder lifetime is any lifetime.
use std::borrow::Cow;
type TextFn = for<'s> fn(&'s [u8], &'s [u8]) -> Cow<'s, [u8]>;
fn stat(a: &'static [u8], _b: &'static [u8]) -> Cow<'static, [u8]> {
    Cow::Borrowed(a)
}
fn main() {
    let f: TextFn = stat;
    println!("{:?}", f(b"a", b"b"));
}
