// A `for<..>` fn pointer whose binder lifetime sits in two inputs and the
// output (fig's `TextFn`): each call takes the lifetime fresh, and the
// output borrows exactly from the inputs that write it.
use std::borrow::Cow;

struct Ctx<'s, 't> {
    src: &'s [u8],
    log: &'t mut Vec<String>,
}

type TextFn = for<'c, 's, 't> fn(&'c mut Ctx<'s, 't>, &'s [u8], usize) -> Result<Cow<'s, [u8]>, String>;
type Pick = for<'a, 'b> fn(&'a [u8], &'b [u8]) -> &'a [u8];

#[derive(Debug, Clone, Copy, Default)]
struct Opts {
    text: Option<TextFn>,
}

fn borrowed<'s>(cx: &mut Ctx<'s, '_>, raw: &'s [u8], at: usize) -> Result<Cow<'s, [u8]>, String> {
    cx.log.push(format!("borrowed at {at}"));
    Ok(Cow::Borrowed(&raw[1..]))
}

fn whole<'s>(cx: &mut Ctx<'s, '_>, _raw: &'s [u8], _at: usize) -> Result<Cow<'s, [u8]>, String> {
    Ok(Cow::Borrowed(cx.src))
}

fn upper(_cx: &mut Ctx<'_, '_>, raw: &[u8], _at: usize) -> Result<Cow<'static, [u8]>, String> {
    Ok(Cow::Owned(raw.iter().map(|b| b.to_ascii_uppercase()).collect()))
}

fn first<'a>(a: &'a [u8], _b: &[u8]) -> &'a [u8] {
    a
}

fn make<'s>(cx: &mut Ctx<'s, '_>, opts: Opts, raw: &'s [u8], at: usize) -> Result<Cow<'s, [u8]>, String> {
    let text: Cow<'s, [u8]> = match opts.text {
        Some(f) => f(cx, raw, at)?,
        None => Cow::Borrowed(raw),
    };
    cx.log.push(format!("made {}", text.len()));
    Ok(text)
}

fn main() {
    let src = b"hello world".to_vec();
    let mut log = Vec::new();
    let mut cx = Ctx { src: &src, log: &mut log };
    let fs: [Option<TextFn>; 4] = [None, Some(borrowed), Some(whole), Some(upper)];
    let mut outs = Vec::new();
    for (i, f) in fs.into_iter().enumerate() {
        let opts = Opts { text: f };
        outs.push(make(&mut cx, opts, &src[6..], i).unwrap());
    }
    for o in &outs {
        println!("{}", String::from_utf8_lossy(o));
    }
    println!("{}", Opts::default().text.is_none());
    let pick: Pick = first;
    let kept = {
        let other = vec![9u8];
        pick(&src[..5], &other)
    };
    println!("{kept:?}");
    drop(outs);
    println!("{log:?}");
}
