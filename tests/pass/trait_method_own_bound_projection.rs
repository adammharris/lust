// `T::Item` of a method's own bound in a trait declaration.
pub trait D { fn any<V: Iterator>(self, v: V) -> Option<V::Item>; }
trait Tr2 { type O; }
pub trait D5 { fn any<V: Tr2>(self, v: V) -> V::O; }
fn main() {}
