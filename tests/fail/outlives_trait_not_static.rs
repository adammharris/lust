// expect: L0617
// rustc E0310: `T: Tr` with a `Tr` that is not `'static` implies nothing.
// must still reject: Tr is not 'static
trait Tr {}
struct Need<B: 'static>(Option<&'static B>);
struct Has<T: Tr> { inner: Need<T> }
fn main() {}
