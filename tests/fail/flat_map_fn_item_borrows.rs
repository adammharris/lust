// expect: L0733
// rustc: a fn item callable's output borrows its input; the items borrow `v`.
fn g(x: &Vec<u8>) -> std::slice::Iter<'_, u8> { x.iter() }
fn f(v: &Vec<Vec<u8>>) -> Vec<&'static u8> { v.iter().flat_map(g).collect() }
fn main() { println!("{:?}", f(&vec![vec![1]])); }
