// expect: L0202
// rustc E0106: an elided output next to a binder used twice has no one input lifetime.
fn main() {
    let _g: for<'a> fn(&'a str, &'a str, &str) -> &str;
}
