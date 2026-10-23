// A trait with `Send + Sync + RefUnwindSafe` supertraits and a plain impl.
use std::panic::RefUnwindSafe;
trait L: Send + Sync + RefUnwindSafe { fn n(&self) -> u8; }
struct J;
impl L for J { fn n(&self) -> u8 { 1 } }
fn main() { println!("{}", J.n()); }
