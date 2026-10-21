// expect: L0506
// rustc E0603: module `a`'s `use std::cell;` is a private import, so a
// path through it from outside `a` does not resolve.
mod a {
    #[allow(unused_imports)]
    use std::cell;
}
use a::cell::Cell;
fn main() {
    println!("{}", Cell::new(1).get());
}
