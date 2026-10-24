// expect: L0733
// rustc: a `Vec` the closure returns holds a borrow of `v`.
fn f(v: &Vec<u8>) -> Vec<&'static u8> { (0..1).flat_map(|_| vec![&v[0]]).collect() }
fn main() { println!("{:?}", f(&vec![1])); }
