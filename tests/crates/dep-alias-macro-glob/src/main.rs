use std::fmt::Write as _;
use util as u;
use u::*;
#[derive(Clone, Copy)]
enum K {
    A,
    B(i64),
}

fn is_b(k: K) -> bool {
    matches!(k, K::B(_))
}

fn show(k: K) -> String {
    let mut s = String::new();
    write!(s, "{}", is_b(k) as i64).unwrap();
    s
}

fn main() {
    let n = util::helper();
    println!("{} {} {}", is_b(K::B(n)), is_b(K::A), show(K::B(1)));
}
