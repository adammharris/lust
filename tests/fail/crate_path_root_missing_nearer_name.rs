// expect: L0101
// rustc E0425: `crate::g` names the crate root, which has no `g`; the
// nearer `m::g` does not answer for it.
mod m {
    pub fn g(x: u8) -> u8 {
        x
    }
    pub fn f(x: u8) -> u8 {
        crate::g(x)
    }
}
fn main() {
    println!("{}", m::f(1));
}
