// expect: L0306
// rustc E0597: `Cow<'s, _>` shares `'s` with the input slice, which dies first.
use std::borrow::Cow;
struct Ctx<'s> { src: &'s [u8] }
type TextFn = for<'c, 's> fn(&'c mut Ctx<'s>, &'s [u8]) -> Cow<'s, [u8]>;
fn pick<'s>(cx: &mut Ctx<'s>, _raw: &'s [u8]) -> Cow<'s, [u8]> { Cow::Borrowed(cx.src) }
fn main() {
    let f: TextFn = pick;
    let src = vec![1u8, 2];
    let out;
    {
        let raw = vec![3u8];
        let mut cx = Ctx { src: &src };
        out = f(&mut cx, &raw);
    }
    println!("{:?}", out);
}
