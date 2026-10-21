// A fn item whose output is `'static` data (`&'static [u8]`), passed for
// an `impl Fn(&'v V, &str) -> Result<T, _>` bound: `T` holds nothing of
// the arguments, so it may go into a `'static` field.
struct V(Vec<u8>);
fn bytes(v: &V, _p: &str) -> Result<&'static [u8], String> {
    Ok(Box::leak(v.0.clone().into_boxed_slice()))
}
fn name(v: &V) -> (&'static str, usize) {
    (if v.0.is_empty() { "empty" } else { "full" }, v.0.len())
}
struct Obj<'v> {
    v: &'v V,
}
fn object<'v>(v: &'v V) -> Obj<'v> {
    Obj { v }
}
impl<'v> Obj<'v> {
    fn req<T>(&self, f: impl Fn(&'v V, &str) -> Result<T, String>) -> Result<T, String> {
        f(self.v, "p")
    }
    fn one<T>(&self, f: impl Fn(&'v V) -> T) -> T {
        f(self.v)
    }
}
#[derive(Debug)]
struct D {
    open: &'static [u8],
    label: &'static str,
}
fn delims(v: &V) -> Result<D, String> {
    let o = object(v);
    let d = D { open: o.req(bytes)?, label: o.one(name).0 };
    Ok(d)
}
fn main() {
    let v = V(b"hi".to_vec());
    println!("{:?}", delims(&v));
}
