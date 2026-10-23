// `dyn Fn(..) + Send + Sync + RefUnwindSafe` and a trait with `RefUnwindSafe` as a
// supertrait, as fig's `Language`: impls meet the bound, the dyn types have it, and
// `catch_unwind` takes a closure over them.
use std::panic::{RefUnwindSafe, UnwindSafe, catch_unwind};
type Parse = Box<dyn Fn(&str) -> usize + Send + Sync + RefUnwindSafe>;
trait Language: Send + Sync + RefUnwindSafe {
    fn name(&self) -> String;
}
struct Json;
impl Language for Json {
    fn name(&self) -> String { "json".into() }
}
struct Runtime {
    parse: Parse,
    lang: Box<dyn Language>,
}
impl Language for Runtime {
    fn name(&self) -> String { format!("rt:{}:{}", self.lang.name(), (self.parse)("abc")) }
}
fn needs_ref<T: RefUnwindSafe + ?Sized>(_t: &T) -> bool { true }
fn needs_uw<T: UnwindSafe>(_t: T) -> bool { true }
fn main() {
    let p: Parse = Box::new(|s: &str| s.len());
    let r = Runtime { parse: p, lang: Box::new(Json) };
    println!("{}", r.name());
    println!("{} {}", needs_ref(&r), needs_uw(&r));
    let d: &dyn Language = &r;
    println!("{}", needs_ref(d));
    let n = catch_unwind(|| r.name().len());
    println!("{:?}", n);
    let e: Box<dyn Fn() -> u8 + UnwindSafe> = Box::new(|| 4);
    println!("{}", e());
    let f: Box<dyn Fn() -> u8 + Send> = Box::new(|| 5);
    println!("{}", f());
}
