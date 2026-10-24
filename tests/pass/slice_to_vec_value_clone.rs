// Elements that own heap data: the copies are deep, and outlive the source.
#[derive(Clone, Debug)]
struct S(String);
fn main() {
    let a = vec![S("x".into()), S("y".into())];
    let r: Result<&[S], ()> = Ok(&a[..]);
    let v = r.map(<[S]>::to_vec).unwrap();
    drop(a);
    println!("{:?}", v);
}
