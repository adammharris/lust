// A fn pointer const whose value is an inherent method path (`Lit::name`),
// its `self` the first param and its `&'static str` output kept.
#[derive(Clone, Copy)]
enum Lit {
    A,
    B,
}
impl Lit {
    fn name(self) -> &'static str {
        match self {
            Lit::A => "a",
            Lit::B => "b",
        }
    }
    fn code(&self, k: u8) -> u8 {
        match self {
            Lit::A => k,
            Lit::B => k + 1,
        }
    }
}
const _: fn(Lit) -> &'static str = Lit::name;
const N: fn(Lit) -> &'static str = Lit::name;
const C: fn(&Lit, u8) -> u8 = Lit::code;
static S: fn(Lit) -> &'static str = Lit::name;
fn keep() -> &'static str {
    N(Lit::B)
}
fn main() {
    println!("{} {} {} {}", N(Lit::A), keep(), C(&Lit::B, 3), S(Lit::B));
}
