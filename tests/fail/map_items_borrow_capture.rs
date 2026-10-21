// expect: L0306
// rustc E0597: the map's items are `&s`, which dies first.
fn main() {
    let mut out: Vec<&String> = Vec::new();
    {
        let s = String::from("x");
        out.extend([1, 2].iter().map(|_| &s));
    }
    println!("{:?}", out);
}
