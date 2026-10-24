// expect: L0733
// rustc: the items borrow `v`, which is not `'static`.
fn f(v: &Vec<Vec<u8>>) -> Vec<&'static u8> { v.iter().flat_map(|x| x.iter()).collect() }
fn main() { println!("{:?}", f(&vec![vec![1]])); }
