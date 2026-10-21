// `[None; N]` and `[None; 3]` start as `Option<?T>`: a later use fixes the
// element type, and the repeat needs Copy of that type, not of the open one.
#[derive(Clone, Copy, Debug)]
struct D {
    a: u8,
}
fn table<const N: usize>(names: [&str; N]) -> [Option<D>; N] {
    let mut out = [None; N];
    for (slot, n) in out.iter_mut().zip(names) {
        if n.len() > 1 {
            *slot = Some(D { a: n.len() as u8 });
        }
    }
    out
}
fn main() {
    println!("{:?}", table(["x", "yy", "zzz"]));
    let mut fixed = [None; 3];
    fixed[1] = Some(7u16);
    println!("{fixed:?}");
}
