// expect: L0306
// rustc E0597: the subslice borrows `v`, which dies first.
fn main() {
    let w: &mut [u8];
    {
        let mut v = vec![1u8, 2, 3];
        w = &mut v[0..2];
    }
    w[0] = 1;
}
