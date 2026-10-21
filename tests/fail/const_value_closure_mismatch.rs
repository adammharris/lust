// expect: L0110
// rustc E0308: the closure's body gives a `u8` where its fn pointer type
// in the const value returns `bool`.
struct T {
    f: fn(u8) -> bool,
}
const X: T = T { f: |b| b + 1 };
fn main() {
    println!("{}", (X.f)(2));
}
