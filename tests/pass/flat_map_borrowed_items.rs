// `flat_map` items that borrow the source, a capture, or through a fn item keep
// those loans.
fn f<'a>(v: &'a Vec<Vec<u8>>) -> Vec<&'a u8> { v.iter().flat_map(|x| x.iter()).collect() }
fn g(names: &[&'static str]) -> Vec<char> { let suffix = String::from("!"); names.iter().flat_map(|n| n.chars().chain(suffix.chars())).collect() }
fn main() { let v = vec![vec![1u8, 2], vec![3]]; println!("{:?} {:?}", f(&v), g(&["ab", "c"])); }
