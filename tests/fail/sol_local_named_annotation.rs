// expect: L0306
// Sol review probe `local_named_annotation`; rustc: E0597 `x` does not live long enough
fn bad<'a>() {
    let x = 1;
    let _: &'a i32 = &x;
}
fn main() { bad(); }
