// `derive(Clone, Copy)` on a non-generic type clones by copy, as rustc
// derives it: a field's written `Clone` (generic, or with a side
// effect) is not called.
use std::marker::PhantomData;
struct In<P, B>(B, PhantomData<P>);
impl<P, B: Copy> Clone for In<P, B> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P, B: Copy> Copy for In<P, B> {}
#[derive(Clone, Copy)]
struct Pub(In<Pub, u8>);

#[derive(Copy)]
struct F(u8);
impl Clone for F {
    fn clone(&self) -> Self {
        println!("F::clone");
        F(self.0 + 1)
    }
}
#[derive(Clone, Copy)]
struct Outer(F);

fn main() {
    let a = Pub(In(3, PhantomData));
    let b = a;
    println!("{}", (a.0).0 + (b.clone().0).0);
    let o = Outer(F(1));
    println!("outer {}", o.clone().0 .0);
}
