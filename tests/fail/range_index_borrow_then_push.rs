// expect: L0303
// rustc E0499: the subslice still borrows `v` mutably at the push.
fn main() {
    let mut v = vec![1u8, 2, 3];
    let w = &mut v[0..2];
    v.push(4);
    w[0] = 9;
    println!("{:?}", v);
}
