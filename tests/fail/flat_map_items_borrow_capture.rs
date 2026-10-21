// expect: L0306
// rustc E0597: the items hold a borrow of `s`, which dies first.
fn main() {
    let mut out: Vec<(&u8, &String)> = Vec::new();
    let v = vec![vec![1u8], vec![2]];
    {
        let s = String::from("x");
        out.extend(v.iter().flat_map(|l| l.iter().map(|d| (d, &s))));
    }
    println!("{:?}", out);
}
