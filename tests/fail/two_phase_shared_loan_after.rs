// expect: L0303
// rustc E0502: the shared borrow of `self.v` is used after the call, so it
// is live at the `&mut self` activation.
struct P {
    v: usize,
}
impl P {
    fn walk(&mut self, x: usize) -> usize {
        self.v += x;
        self.v
    }
    fn go(&mut self) -> usize {
        let c = &self.v;
        let n = self.walk(*c);
        n + *c
    }
}
fn main() {
    let mut p = P { v: 1 };
    println!("{}", p.go());
}
