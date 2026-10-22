// A turbofish type may write `'static` for a param the callee's signature
// never uses (`assert_debug::<View<'static>>()`, as twig's api_surface
// test pins its public types): no value carries the lifetime.
#[derive(Debug)]
struct View<'a> {
    text: &'a str,
}
fn assert_debug<T: std::fmt::Debug>() {}
fn assert_static<T: 'static>() {}
fn size<T>() -> usize {
    std::mem::size_of::<T>()
}
fn main() {
    assert_debug::<View<'static>>();
    assert_static::<&'static str>();
    println!("{}", size::<&'static [u8]>() == size::<&[u8]>());
    println!("{}", View { text: "x" }.text);
}
