// `#[macro_export(local_inner_macros)]`: a single-segment macro call in the
// expansion (`inner!`) resolves as `$crate::inner!`, so it works where the
// caller's module has no `inner` in scope (serde's
// `forward_to_deserialize_any!` and its helper macros).
mod m {
    #[macro_export(local_inner_macros)]
    macro_rules! outer {
        ($x:expr) => { inner!($x) };
    }
    #[macro_export]
    macro_rules! inner {
        ($x:expr) => { $x * 2 };
    }
}
mod user {
    pub fn f() -> i32 { crate::outer!(21) }
}
fn main() { println!("{}", user::f()); }
