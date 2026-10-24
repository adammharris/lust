// expect: L0112
// rustc: the trait bound `NoClone: Clone` is not satisfied (E0277).
struct NoClone(u8);
fn main() {
    let a = [NoClone(1)];
    let s: &[NoClone] = &a;
    let v = Some(s).map(<[NoClone]>::to_vec);
    println!("{}", v.map_or(0, |v| v.len()));
}
