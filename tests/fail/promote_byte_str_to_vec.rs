// expect: L0307
// rustc E0515: a method call is no constant, so `&[b"a".to_vec()]` is a
// temporary of the function, not promoted.
fn samples() -> &'static [Vec<u8>] {
    &[b"a".to_vec()]
}
fn main() {
    println!("{:?}", samples());
}
