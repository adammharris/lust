// `Vec<Range<i32>>` is Debug: each element prints as core's range text
// (cgen's `dbg_cty` range mark; once a reject).
fn main() {
    println!("{:?}", vec![1..2]);
}
