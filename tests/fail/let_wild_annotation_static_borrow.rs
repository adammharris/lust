// expect: L0306
// rustc E0716: the annotation asks the temporary `String` to live for
// `'static`, though `_` binds nothing.
fn main() {
    let _: &'static str = &String::from("x");
    println!("ok");
}
