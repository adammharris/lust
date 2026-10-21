// std's `UnwindSafe` and `RefUnwindSafe` are auto traits: after the
// principal of a dyn type, and as supertraits of a trait a plain struct
// implements (by structure), with `dyn` coercions that drop them.
use std::panic::{RefUnwindSafe, UnwindSafe};
type F = Box<dyn Fn(u8) -> u8 + Send + Sync + RefUnwindSafe>;
trait Lang: Send + Sync + RefUnwindSafe {
    fn name(&self) -> &str;
}
struct R {
    n: String,
    v: Vec<u8>,
}
impl Lang for R {
    fn name(&self) -> &str {
        &self.n
    }
}
fn needs_ref_unwind<T: RefUnwindSafe + ?Sized>(_: &T) -> bool {
    true
}
fn main() {
    let f: F = Box::new(|x| x + 1);
    println!("{}", f(1));
    let g: Box<dyn Fn(u8) -> u8 + Send> = f;
    println!("{}", g(2));
    let r = R { n: "x".into(), v: vec![] };
    println!("{} {}", r.name(), r.v.len());
    let l: &dyn Lang = &r;
    println!("{} {}", l.name(), needs_ref_unwind(l));
    let u: Box<dyn Fn() -> u8 + UnwindSafe> = Box::new(|| 3);
    println!("{}", u());
    let caught = std::panic::catch_unwind(|| l.name().len());
    println!("{:?}", caught);
}
