// A constructor whose input is a projection over a type the output fixes
// (`Cow::Owned` takes `<B as ToOwned>::Owned`) as a fn value, and
// `<[u8]>::to_vec` as one.
use std::borrow::Cow;
fn main() {
    let r: Result<Vec<u8>, ()> = Ok(vec![1]);
    let c: Result<Cow<'static, [u8]>, ()> = r.map(Cow::Owned);
    println!("{:?}", c);
    let s: Option<Cow<'static, str>> = Some(String::from("s")).map(Cow::Owned);
    println!("{:?}", s);
    let o: Option<&[u8]> = Some(b"ab");
    let v: Option<Vec<u8>> = o.map(<[u8]>::to_vec);
    let w: Vec<Vec<u8>> = vec![&b"c"[..], b"de"].into_iter().map(<[u8]>::to_vec).collect();
    let n: Vec<Vec<String>> = vec![&[String::from("x")][..]].into_iter().map(<[String]>::to_vec).collect();
    println!("{:?} {:?} {:?}", v, w, n);
}
