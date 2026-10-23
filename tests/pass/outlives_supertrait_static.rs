// `T: Tr` with `trait Tr: 'static` implies `T: 'static`, in a struct's
// field types and for an associated type bounded by a static trait.
trait Tr: 'static {}
struct Need<B: 'static>(Option<&'static B>);
struct Has<T: Tr> { inner: Need<T> }
fn f<T: Tr>(_: Need<T>) {}
impl Tr for u8 {}
fn main() { let h = Has::<u8> { inner: Need(None) }; f(h.inner); println!("ok"); }
