// `<[T]>::to_vec` as a fn value (fig's `.map(<[u8]>::to_vec)`), cloning
// each element.
fn main() {
    let a: &[u8] = &[1, 2];
    let r: Result<&[u8], ()> = Ok(a);
    let v = r.map(<[u8]>::to_vec);
    println!("{:?}", v);
    let l = Some(a).map(<[u8]>::len);
    println!("{:?}", l);
    let w: Vec<Vec<u8>> = vec![a].into_iter().map(<[u8]>::to_vec).collect();
    println!("{:?} {:?}", w, Some("s").map(str::to_owned));
    let x = Some(a).map(|s| s.to_vec());
    println!("{:?}", x);
}
