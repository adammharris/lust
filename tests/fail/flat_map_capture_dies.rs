// expect: L0306
// rustc E0597: the closure's captured `s` dies before the iterator runs.
fn main() {
    let out: Vec<char>;
    let it;
    {
        let s = String::from("ab");
        it = (0..2).flat_map(|_| s.chars());
    }
    out = it.collect();
    println!("{:?}", out);
}
