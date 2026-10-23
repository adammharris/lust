// A `for<..>` binder elision cannot write, as fig's grammar kit has it: one
// lifetime in two inputs and the output, through an alias, a struct field, fn
// item coercions, calls through the pointer, and an array of pointers.
use std::borrow::Cow;
struct Ctx<'s, 't> {
    src: &'s [u8],
    log: &'t mut Vec<String>,
}
type Result<T> = std::result::Result<T, String>;
type TextFn = for<'c, 's, 't> fn(&'c mut Ctx<'s, 't>, &'s [u8], usize) -> Result<Cow<'s, [u8]>>;
#[derive(Clone, Copy, Default)]
struct Opts {
    text: Option<TextFn>,
}
fn unquote<'s>(cx: &mut Ctx<'s, '_>, raw: &'s [u8], at: usize) -> Result<Cow<'s, [u8]>> {
    cx.log.push(format!("unquote at {at}"));
    if raw.len() >= 2 && raw[0] == b'"' {
        Ok(Cow::Borrowed(&raw[1..raw.len() - 1]))
    } else if raw.is_empty() {
        Err("empty".to_string())
    } else {
        Ok(Cow::Owned(raw.iter().map(|b| b.wrapping_sub(32)).collect()))
    }
}
fn whole<'s>(cx: &mut Ctx<'s, '_>, _raw: &'s [u8], _at: usize) -> Result<Cow<'s, [u8]>> {
    Ok(Cow::Borrowed(cx.src))
}
fn make<'s>(cx: &mut Ctx<'s, '_>, opts: Opts, raw: &'s [u8], at: usize) -> Result<Cow<'s, [u8]>> {
    match opts.text {
        Some(f) => f(cx, raw, at),
        None => Ok(Cow::Borrowed(raw)),
    }
}
fn main() {
    let src = b"\"hi\" there".to_vec();
    let mut log = Vec::new();
    let mut cx = Ctx { src: &src, log: &mut log };
    let o = Opts { text: Some(unquote) };
    let a = make(&mut cx, o, &src[0..4], 0).unwrap();
    let b = make(&mut cx, o, &src[5..], 5).unwrap();
    let c = make(&mut cx, Opts::default(), &src[5..], 5).unwrap();
    let d = make(&mut cx, Opts { text: Some(whole) }, &src[..1], 0).unwrap();
    let e = make(&mut cx, o, &src[0..0], 0);
    println!("{:?} {:?} {:?} {:?} {:?}", a, b, c, d, e);
    let fs: [TextFn; 2] = [unquote, whole];
    for f in fs {
        println!("{:?}", f(&mut cx, &src[0..4], 1));
    }
    println!("{:?}", log);
}
