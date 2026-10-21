// Debug of a range inside another type: a derived field, `Option`,
// `Vec`, a tuple, a reference, a `Result`, a manual impl's builder
// field, every range kind, and the caller's width and `#` on the bounds.
use std::fmt;
use std::ops::{Range, RangeInclusive};
#[derive(Debug)]
struct C {
    r: Range<usize>,
    o: Option<Range<usize>>,
}
#[derive(Debug, Clone)]
enum E {
    Span(Range<u8>),
    Both { a: RangeInclusive<i32>, b: std::ops::RangeFrom<u8> },
}
struct M {
    span: Option<Range<usize>>,
}
impl fmt::Debug for M {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("M").field("span", &self.span).finish()
    }
}
fn main() {
    let c = C { r: 1..3, o: Some(4..6) };
    println!("{:?} {:?}", c, C { r: 0..0, o: None });
    println!("{:#?}", c);
    let r: Option<Range<usize>> = Some(1..2);
    println!("{:?} {:?}", r, None::<Range<usize>>);
    let v: Vec<Range<u32>> = vec![0..1, 2..5];
    println!("{:?} {:?}", v, (1..2, 'x'));
    println!("{:?}", &(3..4));
    let res: Result<Range<i8>, String> = Ok(-1..1);
    println!("{:?}", res);
    println!("{:?}", M { span: Some(7..9) });
    let mut inc = 2..=2;
    println!("{:?}", E::Both { a: inc.clone(), b: 9.. });
    inc.next();
    println!("{:?} {:?}", E::Span(1..2), Some(inc));
    let tos: Option<std::ops::RangeToInclusive<u8>> = Some(..=3);
    let to: Option<std::ops::RangeTo<u8>> = Some(..4);
    let full: Option<std::ops::RangeFull> = Some(..);
    println!("{:?} {:?} {:?}", tos, to, full);
    println!("[{:5?}] [{:#x?}]", Some(1..2), Some(10..11));
}
