// expect: L0733
// rustc E0521: `first`'s output borrows its argument, so `T` holds the
// borrow of `v` and cannot go into a `'static` field.
struct V(Vec<u8>);
fn first(v: &V) -> &[u8] {
    &v.0[..1]
}
struct Obj<'v> {
    v: &'v V,
}
impl<'v> Obj<'v> {
    fn one<T>(&self, f: impl Fn(&'v V) -> T) -> T {
        f(self.v)
    }
}
struct D {
    open: &'static [u8],
}
fn delims(v: &V) -> D {
    let o = Obj { v };
    D { open: o.one(first) }
}
fn main() {
    let v = V(b"hi".to_vec());
    println!("{:?}", delims(&v).open);
}
