// expect: L0110
// rustc E0277: a fn item is no fn pointer (`FnPtr` is not implemented).
fn one(x: u8) -> u8 {
    x + 1
}
fn main() {
    let f: fn(u8) -> u8 = one;
    println!("{}", std::ptr::fn_addr_eq(f, one));
}
