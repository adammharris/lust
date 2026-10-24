// expect: L0306
// rustc E0597: a generic callee's `T::Out` with `Out = &'a str` borrows the argument.
trait Tr<'a> { type Out; fn get(&self, s: &'a str) -> Self::Out; }
struct S;
impl<'a> Tr<'a> for S { type Out = &'a str; fn get(&self, s: &'a str) -> &'a str { &s[1..] } }
struct N;
impl<'a> Tr<'a> for N { type Out = usize; fn get(&self, s: &'a str) -> usize { s.len() } }
fn use_it<'a, T: Tr<'a>>(t: &T, s: &'a str) -> T::Out { t.get(s) }
fn main() { let r; { let x = String::from("hello"); r = use_it(&S, &x); } println!("{}", r); }
