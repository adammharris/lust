// A `&'static dyn Tr` from a reference the borrow checker proves
// `'static`: a reborrow through `Arc`'s Deref behind a leaked `&'static`
// (fig-core's `register_arc`), a `&'static` local, and `Box::leak`.
use std::fmt::Debug;
use std::sync::Arc;
trait Language {
    fn name(&self) -> &str;
}
struct J;
impl Language for J {
    fn name(&self) -> &str {
        "json"
    }
}
fn register_with(lang: &'static dyn Language) -> usize {
    lang.name().len()
}
fn register_arc(lang: Arc<dyn Language>) -> usize {
    let held: &'static Arc<dyn Language> = Box::leak(Box::new(lang));
    register_with(&**held)
}
fn keep(r: &'static J) -> &'static dyn Language {
    r
}
static S: J = J;
fn main() {
    println!("{}", register_arc(Arc::new(J)));
    let r: &'static u8 = Box::leak(Box::new(1u8));
    let d: &'static dyn Debug = r;
    let e: &'static dyn Debug = Box::leak(Box::new(String::from("e")));
    let s: &'static (dyn Debug + Send) = &7u32;
    println!("{:?} {:?} {:?} {}", d, e, s, keep(&S).name());
}
