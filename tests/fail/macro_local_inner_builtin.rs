// expect: L0802
// rustc: cannot find `concat` in `$crate` (E0433): under
// local_inner_macros a builtin macro call resolves through `$crate` too.
#[macro_export(local_inner_macros)]
macro_rules! joined {
    ($a:expr, $b:expr) => { concat!($a, $b) };
}
fn main() { println!("{}", joined!("a", "b")); }
