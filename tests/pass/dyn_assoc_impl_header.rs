// Impl headers over dyn bindings (`impl<O> X for Vec<Box<dyn Rule<Out = O>>>`
// constrains O; two impls that differ by the binding), `&mut dyn`, and an
// upcast that keeps the binding.
trait Rule { type Out; fn get(&mut self) -> Option<Self::Out>; }
type BoxRule<O> = Box<dyn Rule<Out = O>>;
trait ChoiceList { type Out; fn first(&mut self) -> Option<Self::Out>; }
impl<O> ChoiceList for Vec<BoxRule<O>> {
    type Out = O;
    fn first(&mut self) -> Option<O> {
        for r in self.iter_mut() { if let Some(v) = r.get() { return Some(v); } }
        None
    }
}
trait Named { fn name(&self) -> String; }
impl Named for Box<dyn Rule<Out = u8>> { fn name(&self) -> String { "u8 rule".into() } }
impl Named for Box<dyn Rule<Out = String>> { fn name(&self) -> String { "string rule".into() } }
struct Count(u8);
impl Rule for Count { type Out = u8; fn get(&mut self) -> Option<u8> { self.0 += 1; (self.0 > 2).then_some(self.0) } }
struct Never;
impl Rule for Never { type Out = u8; fn get(&mut self) -> Option<u8> { None } }
struct S;
impl Rule for S { type Out = String; fn get(&mut self) -> Option<String> { Some("s".into()) } }
trait Sub: Rule { fn tag(&self) -> u32; }
impl Sub for Count { fn tag(&self) -> u32 { 7 } }
fn upcast(b: Box<dyn Sub<Out = u8>>) -> Box<dyn Rule<Out = u8>> { b }
fn by_mut(r: &mut dyn Rule<Out = u8>) -> Option<u8> { r.get() }
fn main() {
    let mut v: Vec<BoxRule<u8>> = vec![Box::new(Never), Box::new(Count(0))];
    println!("{:?} {:?} {:?}", v.first(), v.first(), v.first());
    let a: Box<dyn Rule<Out = u8>> = Box::new(Never);
    let b: Box<dyn Rule<Out = String>> = Box::new(S);
    println!("{} {}", a.name(), b.name());
    let s: Box<dyn Sub<Out = u8>> = Box::new(Count(5));
    println!("{}", s.tag());
    let mut u = upcast(s);
    println!("{:?}", u.get());
    let mut c = Count(9);
    println!("{:?}", by_mut(&mut c));
}
