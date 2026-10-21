// expect: L0110
// rustc E0277: core has no `PartialEq<Vec<U>>` for `[T; N]`.
fn main() {
    let v = vec![1u8, 2];
    assert_eq!([1u8, 2], v);
}
