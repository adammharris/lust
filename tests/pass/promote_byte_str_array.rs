// `&[b"a\n"]` is a constant: rustc promotes the array of byte strings
// to `'static`, as it does `&["sp"]`.
fn samples() -> &'static [&'static [u8]] {
    &[b"a\n"]
}
fn two() -> &'static [&'static [u8]] {
    &[b"a", b"bc"]
}
fn nested() -> &'static [(&'static [u8], u8)] {
    &[(b"x", 1), (b"yz", 2)]
}
fn main() {
    println!("{:?} {:?} {:?}", samples(), two(), nested());
}
