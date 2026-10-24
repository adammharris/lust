// capability: rejected: `dyn` for traits with std supertraits other than `Debug` and `Display`
// expect: L0702

trait T: PartialEq<u32> {
    fn f(&self) -> u32;
}

impl T for u32 {
    fn f(&self) -> u32 {
        1
    }
}

fn main() {
    let a: &dyn T = &1u32;
    println!("{}", a.f());
}
