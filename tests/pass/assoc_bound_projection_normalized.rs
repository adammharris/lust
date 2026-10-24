// An associated type's binding names a projection (`Seq<<Self as
// IntoIterator>::IntoIter, E>`, serde's `IntoDeserializer` for `Vec<T>`):
// the trait's bound on it (`D: De<Error = E>`) and the struct's own
// `where I: Iterator` hold for the type it normalizes to.
use std::collections::BTreeMap;
use std::marker::PhantomData;
trait De {
    type Error;
    fn go(self) -> usize;
}
trait IntoDe<E> {
    type D: De<Error = E>;
    fn into_de(self) -> Self::D;
}
struct Seq<I, E> {
    iter: I,
    e: PhantomData<E>,
}
impl<I, T, E> De for Seq<I, E>
where
    I: Iterator<Item = T>,
    T: IntoDe<E>,
{
    type Error = E;
    fn go(self) -> usize { self.iter.count() }
}
struct U;
impl De for U {
    type Error = ();
    fn go(self) -> usize { 0 }
}
impl IntoDe<()> for u8 {
    type D = U;
    fn into_de(self) -> U { U }
}
impl<T, E> IntoDe<E> for Vec<T>
where
    T: IntoDe<E>,
{
    type D = Seq<<Self as IntoIterator>::IntoIter, E>;
    fn into_de(self) -> Self::D { Seq { iter: self.into_iter(), e: PhantomData } }
}
struct Map<I> where I: Iterator { iter: I, last: Option<I::Item> }
trait IntoM {
    type D;
    fn into_m(self) -> Self::D;
}
impl<T> IntoM for Vec<T> {
    type D = Map<<Self as IntoIterator>::IntoIter>;
    fn into_m(self) -> Self::D { Map { iter: self.into_iter(), last: None } }
}
impl<K: Ord, V> IntoM for BTreeMap<K, V> {
    type D = Map<<Self as IntoIterator>::IntoIter>;
    fn into_m(self) -> Self::D { Map { iter: self.into_iter(), last: None } }
}
fn main() {
    let v: Vec<u8> = vec![1, 2, 3];
    println!("{}", IntoDe::<()>::into_de(v).go());
    let mut m = BTreeMap::new();
    m.insert(1, 'a');
    let mut d = m.into_m();
    d.last = d.iter.next();
    println!("{:?}", d.last);
    let mut e = vec![2].into_m();
    println!("{:?} {:?}", e.iter.next(), e.last);
}
