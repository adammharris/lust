// expect: L0306
// rustc E0597: the output of a `for<'a, 'b> fn(&'a, &'b) -> &'a` call
// borrows its first argument, which dies before the use.
type Pick = for<'a, 'b> fn(&'a [u8], &'b [u8]) -> &'a [u8];
fn first<'a>(a: &'a [u8], _b: &[u8]) -> &'a [u8] {
    a
}
fn main() {
    let p: Pick = first;
    let other = vec![1u8];
    let kept = {
        let mine = vec![9u8];
        p(&mine, &other)
    };
    println!("{kept:?}");
}
