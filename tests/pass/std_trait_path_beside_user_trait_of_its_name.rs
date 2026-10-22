// A full std path names std's trait, never a user trait of the same name:
// with a root `trait From`, `std::convert::From::from` is std's (rustc),
// while a bare `From` is the user's.
#[allow(dead_code)]
trait From<T> {
    fn from(t: T) -> Self;
}
impl From<u8> for i64 {
    fn from(_t: u8) -> i64 {
        -1
    }
}
fn main() {
    let a: i64 = std::convert::From::from(7u8);
    let b: i64 = <i64 as From<u8>>::from(7u8);
    let c: i64 = <i64 as std::convert::From<u8>>::from(7u8);
    let d = <i64 as std::convert::From<u8>>::from;
    println!("{} {} {} {}", a, b, c, d(8));
}
