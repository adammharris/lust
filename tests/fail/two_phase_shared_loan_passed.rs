// expect: L0303
// rustc E0502: the shared borrow of `self.v` is passed into the call, so it
// is live at the `&mut self` activation.
struct P {
    v: usize,
}
impl P {
    fn walk2(&mut self, c: &usize) -> usize {
        self.v += 1;
        *c
    }
    fn go(&mut self) -> usize {
        let c = &self.v;
        self.walk2(c)
    }
}
fn main() {
    let mut p = P { v: 1 };
    println!("{}", p.go());
}
