// `PhantomData<T>` takes an unsized `T` (`str`, `[u8]`, `dyn Fn()`), with
// its derives and `Hash`, as in core.
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
#[derive(Clone, Copy, Debug, Default, PartialEq)]
struct W<T: ?Sized> {
    n: u8,
    p: PhantomData<T>,
}
fn size<T: ?Sized>(_: PhantomData<T>) -> usize {
    std::mem::size_of::<PhantomData<T>>()
}
fn main() {
    let a: PhantomData<str> = PhantomData;
    let b = a;
    println!("{} {}", a == b, size(a.clone()));
    let w: W<[u8]> = W { n: 3, p: PhantomData };
    println!("{} {}", w.n, size(w.p));
    let d: PhantomData<dyn Fn()> = Default::default();
    let mut h = DefaultHasher::new();
    d.hash(&mut h);
    println!("{} {:?}", size(d), PhantomData::<i32>);
}
