// A `crate::` path to a crate-root item whose name a nearer item, import,
// local, or generic param also binds: the path still names the root item.
fn f(x: u8) -> u8 {
    x + 1
}
struct S(u8);
impl S {
    fn new() -> S {
        S(10)
    }
}
enum E {
    A,
    B(u8),
}
const N: usize = 3;

mod m {
    pub fn f(_: u8, x: u8) -> u8 {
        crate::f(x) * 2
    }
    struct S;
    enum E {
        Z,
    }
    pub fn s() -> u8 {
        let _ = (S, E::Z);
        crate::S::new().0 + crate::S(1).0
    }
    pub fn e() -> u8 {
        match crate::E::B(4) {
            crate::E::A => 0,
            crate::E::B(n) => n,
        }
    }
}

mod n {
    use super::f as g;
    pub fn f(x: u8) -> u8 {
        g(x) + crate::f(x)
    }
}

fn generic_n<const N: usize>() -> usize {
    N + crate::N
}

fn main() {
    let f = 100u8;
    println!("{} {} {} {} {} {}", m::f(0, 1), m::s(), m::e(), n::f(2), crate::f(f), generic_n::<5>());
    let _ = E::A;
}
