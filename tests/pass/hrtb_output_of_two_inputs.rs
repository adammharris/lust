// The output takes one of two input lifetimes, which elision cannot say:
// the binder stays written (`FnSig::binders`, parser/hrtb.rs).
fn ap(f: for<'a, 'b> fn(&'a u8, &'b u8) -> &'b u8) -> u8 { *f(&1, &2) }
fn s<'x, 'y>(_a: &'x u8, b: &'y u8) -> &'y u8 { b }
fn main() { println!("{}", ap(s)); }
