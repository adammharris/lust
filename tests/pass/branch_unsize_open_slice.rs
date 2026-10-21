// A branch result coerces to an expected `&[?T]` whose element is still
// open (`Vec::new()` then `extend_from_slice`): byte strings of two lengths
// unsize one by one, where joining `&[u8; 2]` and `&[u8; 3]` would fail.
fn main() {
    let c = std::env::args().count() > 5;
    let mut out = Vec::new();
    out.extend_from_slice(if c { b"{\n  [" } else { b"{[" });
    out.extend_from_slice(match out.len() { 0 => b"zero", 2 => b"tw", _ => b"many" });
    let v = vec![7u8, 8];
    out.extend_from_slice(if c { b"ab" } else { &v });
    if let Some(&last) = out.last() {
        out.push(last);
    }
    let mut words = Vec::new();
    words.extend_from_slice(if c { &["a", "b"][..] } else { &["c"] });
    println!("{out:?} {words:?}");
}
