// expect: L0733
// rustc: lifetime may not live long enough (the items borrow `ls`).
fn f(ls: &[Vec<u8>]) -> Vec<&'static u8> {
    ls.iter().flat_map(|l| l.iter().map(|d| d)).collect()
}
fn main() {
    println!("{:?}", f(&[vec![1]]));
}
