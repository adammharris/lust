// expect: L0203
// rustc E0597: `T = &'static str` makes the argument a `&'static str`, so
// `&s` must live for `'static`. lust keeps rejecting a written lifetime
// where a value carries it.
fn keep<T>(x: T) -> T {
    x
}
fn main() {
    let s = String::from("x");
    let r = keep::<&'static str>(&s);
    println!("{r}");
}
