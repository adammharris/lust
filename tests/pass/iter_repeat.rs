// `std::iter::repeat` and `repeat_with` (as fig-yaml's `repeat(b'\n').take(n)`):
// items, Debug, size hints, adapters, `next_back`, and `TrustedLen` capacities.
use std::iter::{repeat, repeat_with, Repeat};
fn main() {
    let mut v: Vec<u8> = vec![1];
    v.extend(std::iter::repeat(b'\n').take(3));
    println!("{:?}", v);
    let s: String = repeat("ab").take(3).collect();
    println!("{s}");
    let r: Repeat<i32> = repeat(7);
    println!("{:?} {:?}", r.clone(), r.size_hint());
    let mut n = 0;
    let w: Vec<i32> = repeat_with(|| { n += 2; n }).take(4).collect();
    println!("{:?} {:?}", w, repeat_with(|| 1).size_hint());
    println!("{:?}", repeat_with(|| 1u8));
    let z: Vec<(i32, char)> = repeat(0).zip("xyz".chars()).collect();
    println!("{:?} {:?}", z, repeat(5).nth(100));
    let mut b = repeat('q');
    println!("{:?} {:?}", b.next_back(), core::iter::repeat(1).skip(2).step_by(3).take(2).collect::<Vec<_>>());
    println!("{}", "ab".repeat(2));
    let a: Vec<i32> = repeat(1).take(3).collect();
    let b: Vec<u8> = repeat_with(|| 2).take(5).collect();
    println!("{} {}", a.capacity(), b.capacity());
}
