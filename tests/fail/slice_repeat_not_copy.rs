// expect: L0110
// rustc E0277: `<[T]>::repeat` needs `T: Copy`.
fn main() {
    let v = vec![String::from("a")];
    println!("{:?}", v.repeat(2));
}
