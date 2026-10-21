// `[u8]`'s to_ascii_lowercase / to_ascii_uppercase (a new Vec) and
// make_ascii_* (in place, also on a Vec and an array), and
// `<[T]>::repeat` for a Copy element.
const E: &[u8] = b"ab";
fn main() {
    let s = b"HeLLo, World 9";
    let lo: Vec<u8> = s[1..].to_ascii_lowercase();
    let up = s.to_ascii_uppercase();
    println!("{:?} {:?}", String::from_utf8(lo).unwrap(), String::from_utf8(up.clone()).unwrap());
    println!("{}", up.capacity() >= up.len());
    let mut v = b"MiXeD \xff".to_vec();
    v.make_ascii_lowercase();
    println!("{:?}", v);
    v[..2].make_ascii_uppercase();
    println!("{:?}", v);
    let mut a = *b"aBc";
    a.make_ascii_uppercase();
    println!("{:?}", a);
    println!("{:?} {:?}", E.repeat(2), E.repeat(0));
    let w: Vec<u16> = [1u16, 2].repeat(3);
    println!("{:?}", w);
    let units: Vec<()> = [(), ()].repeat(2);
    println!("{}", units.len());
    let empty: Vec<u8> = Vec::new();
    println!("{:?}", empty.repeat(usize::MAX));
}
