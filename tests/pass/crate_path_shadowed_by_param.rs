// `self::N` and `crate::N` name the module const, and `crate::T` the
// struct, under generic params of the same name: the paths read the
// crate-root items through their `crate$` alias, never the params.
const N: usize = 7;
struct T;
impl T {
    fn id() -> u32 {
        1
    }
}
trait Id {
    fn id() -> u32;
}
impl Id for u8 {
    fn id() -> u32 {
        8
    }
}
fn f<const N: usize>() -> usize {
    self::N + crate::N + N * 100
}
fn g<T: Id>() -> u32 {
    crate::T::id() * 10 + T::id()
}
fn main() {
    println!("{} {}", f::<3>(), g::<u8>());
}
