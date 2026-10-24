// expect: L0612
// rustc: the trait bound `T: IntoDe<E>` is not satisfied (E0277): the
// binding normalizes to `Seq<vec::IntoIter<T>, E>`, whose `De` impl needs it.
use std::marker::PhantomData;
trait De { type Error; }
trait IntoDe<E> { type D: De<Error = E>; }
struct Seq<I, E> { iter: I, e: PhantomData<E> }
impl<I, T, E> De for Seq<I, E> where I: Iterator<Item = T>, T: IntoDe<E> { type Error = E; }
impl<T, E> IntoDe<E> for Vec<T> {
    type D = Seq<<Self as IntoIterator>::IntoIter, E>;
}
fn main() {}
