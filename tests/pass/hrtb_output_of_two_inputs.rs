// The output takes one of two input lifetimes of a `for<..>` fn pointer
// type, which elision cannot say: each binder lifetime is its own group
// of slots (`FnSig::binders`).
fn ap(f: for<'a, 'b> fn(&'a u8, &'b u8) -> &'b u8) -> u8 { *f(&1, &2) }
fn s<'x, 'y>(_a: &'x u8, b: &'y u8) -> &'y u8 { b }
fn main() { println!("{}", ap(s)); }
