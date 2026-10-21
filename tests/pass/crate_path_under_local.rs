// `crate::f` under a local `f` names the crate-root fn.
fn f() -> i32 { 1 }
fn main() {
    let f = || 5;
    println!("{} {}", f(), crate::f());
}
