// expect: L0113
// rustc E0277: `u8: PartialEq<String>` does not hold, so the sequences
// cannot be compared.
fn main() {
    let owned = vec![String::from("a")];
    let bytes = [1u8];
    println!("{}", bytes == owned[..]);
}
