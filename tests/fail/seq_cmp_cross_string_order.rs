// expect: L0113
// rustc E0308: core has no `PartialOrd` between sequences of two string
// types (only `PartialEq`), so `<` wants the same type on both sides.
fn main() {
    let owned = vec![String::from("a")];
    let strs = vec!["a"];
    println!("{}", strs < owned);
}
