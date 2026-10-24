// expect: L0612
// rustc: `u8` is not an iterator (E0277): the struct's `where I: Iterator`
// holds for the type the projection normalizes to, which is not one.
struct Map<I> where I: Iterator { iter: I }
trait Tr { type O; }
impl Tr for u8 { type O = u8; }
trait IntoM { type D; }
impl IntoM for u16 { type D = Map<<u8 as Tr>::O>; }
fn main() {}
