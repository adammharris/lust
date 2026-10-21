// capability: rejected: `dyn` for traits whose supertraits have associated types, or with std supertraits other than `Debug` and `Display`
// expect: L0702

trait Base {
    type O;
    fn o(&self) -> Self::O;
}

trait T: Base {
    fn f(&self) -> u32;
}

fn g(x: &dyn T<O = u8>) -> u32 {
    x.f()
}

fn main() {}
