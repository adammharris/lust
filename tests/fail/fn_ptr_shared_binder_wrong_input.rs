// expect: L0110
// rustc: lifetime may not live long enough. A fn whose output borrows
// from its second input is not a `for<'a, 'b> fn(&'a, &'b) -> &'a`.
type Pick = for<'a, 'b> fn(&'a [u8], &'b [u8]) -> &'a [u8];
fn second<'a, 'b>(_a: &'a [u8], b: &'b [u8]) -> &'b [u8] {
    b
}
fn main() {
    let p: Pick = second;
    println!("{:?}", p(b"x", b"y"));
}
