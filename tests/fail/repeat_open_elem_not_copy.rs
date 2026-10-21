// expect: L0110
// rustc E0277: the open `Option<?T>` of `[None; 3]` becomes `Option<String>`,
// which is not Copy.
fn main() {
    let mut out = [None; 3];
    out[0] = Some(String::new());
    println!("{:?}", out);
}
