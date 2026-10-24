// A supertrait's associated type: bound on the dyn type (`dyn Sub<Out = usize>`)
// or fixed by the supertrait bound (`trait Sub2: Base<Out = usize>`).
trait Base { type Out; fn get(&self) -> Self::Out; }
trait Sub: Base { fn name(&self) -> &'static str; }
trait Sub2: Base<Out = usize> { fn tag(&self) -> u8; }
struct Len;
impl Base for Len { type Out = usize; fn get(&self) -> usize { 3 } }
impl Sub for Len { fn name(&self) -> &'static str { "len" } }
impl Sub2 for Len { fn tag(&self) -> u8 { 9 } }
fn main() {
    let b: Box<dyn Sub<Out = usize>> = Box::new(Len);
    println!("{} {}", b.get(), b.name());
    let c: Box<dyn Sub2> = Box::new(Len);
    let n: usize = c.get();
    println!("{} {}", n, c.tag());
    let d: Box<dyn Base<Out = _>> = Box::new(Len);
    let m: usize = d.get();
    println!("{m}");
}
