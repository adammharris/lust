// expect: L0110
// rustc E0207: `U` occurs nowhere in the header (`dyn Other<u8>` names no param).
trait Other<O> {
    fn get(&self) -> O;
}
trait Tr {
    fn m(&self) -> u8;
}
impl<U> Tr for dyn Other<u8> {
    fn m(&self) -> u8 {
        self.get()
    }
}
fn main() {}
