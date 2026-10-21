// `assert_eq!` compares `*left == *right` with core's asymmetric
// PartialEq impls across slices, arrays and Vecs, as `==` does: a Vec or
// slice field against a byte string is the common test shape.
struct Matcher {
    kind_name: Vec<u8>,
    open: &'static [u8],
}

fn main() {
    let v: Vec<u8> = b"ab".to_vec();
    let s: &[u8] = &v;
    let m = Matcher { kind_name: b"heading".to_vec(), open: b"*" };
    assert_eq!(v, b"ab");
    assert_eq!(v, *b"ab");
    assert_eq!(s, b"ab");
    assert_eq!(b"ab", s);
    assert_eq!(v, s);
    assert_eq!(&v, b"ab");
    assert_eq!(m.kind_name, b"heading");
    assert_eq!(m.open, b"*");
    assert_ne!(m.kind_name, b"para");
    assert_eq!(vec![1u16, 2], [1, 2]);
    assert_eq!(Vec::<u8>::new(), b"");
    let words = vec!["a", "b"];
    assert_eq!(words, ["a", "b"]);
    println!("ok");
    // A failing one reports both sides with Debug, as rustc does.
    assert_eq!(b"xy".to_vec(), b"xz", "bytes {}", 1);
}
