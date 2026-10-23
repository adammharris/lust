// A shared borrow of a place coerced to `&'static dyn Tr`: the borrow checker
// proves its lifetime (`&**held` with `held: &'static Arc<dyn Tr>`, as
// fig-core's `register_arc`; fields and `Box`/`Rc` derefs behind `&'static`).
use std::rc::Rc;
use std::sync::Arc;
trait L {
    fn n(&self) -> usize;
}
struct J(usize);
impl L for J {
    fn n(&self) -> usize {
        self.0
    }
}
struct H {
    b: Box<dyn L>,
    pair: (u8, Box<dyn L>),
}
fn take(l: &'static dyn L) -> usize {
    l.n()
}
fn reg(lang: Arc<dyn L>) -> usize {
    let held: &'static Arc<dyn L> = Box::leak(Box::new(lang));
    take(&**held)
}
fn main() {
    println!("{}", reg(Arc::new(J(1))));
    let h: &'static H = Box::leak(Box::new(H { b: Box::new(J(2)), pair: (0, Box::new(J(3))) }));
    let r: &'static Rc<dyn L> = Box::leak(Box::new(Rc::new(J(4)) as Rc<dyn L>));
    println!("{} {} {}", take(&*h.b), take(&*h.pair.1), take(&**r));
}
