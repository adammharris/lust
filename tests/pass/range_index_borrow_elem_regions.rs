// A range index of a `Vec<C<'s>>` field behind `&mut self` makes a bare
// slice temporary; borrowing or indexing it keeps its pointer apart from
// the elements' `'s` (it asked `'self: 's`).
struct C<'s> {
    end: usize,
    label: &'s [u8],
}
struct P<'s> {
    stack: Vec<C<'s>>,
}
impl<'s> P<'s> {
    fn ext(&mut self, m: usize, idx: usize) {
        for c in self.stack[1..m].iter_mut() {
            c.end = idx;
        }
        let v = &mut self.stack[0..1];
        v[0].end += 1;
        let first = &self.stack[..1];
        let _ = &first[0];
    }
}
fn tail<'s>(v: &mut [C<'s>]) -> usize {
    let w = &mut v[1..];
    w[0].end += 10;
    w.len()
}
fn main() {
    let s = b"xy".to_vec();
    let mut p = P { stack: vec![C { end: 0, label: &s }, C { end: 0, label: &s }, C { end: 0, label: &s[1..] }] };
    p.ext(3, 5);
    let n = tail(&mut p.stack);
    let ends: Vec<usize> = p.stack.iter().map(|c| c.end).collect();
    println!("{ends:?} {n} {}", p.stack[2].label.len());
}
