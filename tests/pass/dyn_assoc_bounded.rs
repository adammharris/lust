// An associated type with bounds, used through a generic `R: Rule + ?Sized`
// at a dyn type.
trait Rule { type Out: Clone + std::fmt::Debug; fn get(&self) -> Self::Out; }
struct Len;
impl Rule for Len { type Out = usize; fn get(&self) -> usize { 3 } }
fn twice<R: Rule + ?Sized>(r: &R) -> (R::Out, R::Out) { let v = r.get(); (v.clone(), v) }
fn main() { let b: Box<dyn Rule<Out = usize>> = Box::new(Len); println!("{:?}", twice(&*b)); }
