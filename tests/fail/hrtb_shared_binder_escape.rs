// expect: L0306
// rustc E0597: the result borrows both inputs of a shared binder, so it cannot outlive `t`.
fn longest<'a>(a: &'a str, b: &'a str) -> &'a str { if a.len() >= b.len() { a } else { b } }
fn main() {
    let f: for<'a> fn(&'a str, &'a str) -> &'a str = longest;
    let s = String::from("hello");
    let r;
    {
        let t = String::from("hi");
        r = f(&s, &t);
    }
    println!("{r}");
}
