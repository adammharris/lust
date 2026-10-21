// `super::f` names the crate-root `f`, not the module's own `f`.
fn f() -> i32 { 1 }
mod m {
    fn f() -> i32 { 2 }
    pub fn p() -> i32 { f() * 10 + super::f() }
}
fn main() { println!("{}", m::p()); }
