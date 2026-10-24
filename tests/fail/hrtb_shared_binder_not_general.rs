// expect: L0110
// rustc E0308: `longest` ties both inputs to the output; the pointer type keeps them apart.
fn longest<'a>(a: &'a str, b: &'a str) -> &'a str { if a.len() >= b.len() { a } else { b } }
fn main() {
    let g: for<'a, 'b> fn(&'a str, &'b str) -> &'a str = longest;
    println!("{}", g("a", "b"));
}
