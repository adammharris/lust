// std::iter::repeat: clones of one element, endless, through take, zip,
// nth, rev, and its derived Debug.
use std::iter;
fn main() {
    let mut v = vec![1u8];
    v.extend(std::iter::repeat(b'\n').take(2));
    println!("{:?}", v);
    let s: String = iter::repeat("ab").take(3).collect();
    println!("{s}");
    let pairs: Vec<(u32, char)> = (1..4).zip(iter::repeat('x')).collect();
    println!("{:?}", pairs);
    let mut r = iter::repeat(String::from("w"));
    println!("{:?} {:?} {:?}", r.nth(5), r.size_hint(), r.next_back());
    println!("{:?}", iter::repeat(7).rev().take(2).collect::<Vec<_>>());
    println!("{:?}", iter::repeat(vec![1, 2]));
}
