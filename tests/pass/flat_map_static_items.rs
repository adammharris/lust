// The items of a `flat_map` (or `map(..).flatten()`) whose closure maps to
// `&'static str` fields hold no loan of the iterators they come from.
struct D {
    name: &'static str,
    n: u8,
}
fn names(ls: &[Vec<D>]) -> Vec<&'static str> {
    ls.iter().flat_map(|l| l.iter().map(|d| d.name)).collect()
}
fn flat(ls: &[Vec<D>]) -> Vec<&'static str> {
    ls.iter().map(|l| l.iter().map(|d| d.name)).flatten().collect()
}
fn nested(ls: &[Vec<D>]) -> Vec<usize> {
    let mut out = Vec::new();
    for m in ls.iter().map(|l| l.iter().map(|d| d.name)) {
        out.extend(m.map(str::len));
    }
    out
}
fn borrowed<'a>(ls: &'a [Vec<D>]) -> Vec<&'a u8> {
    ls.iter().flat_map(|l| l.iter().map(|d| &d.n)).collect()
}
fn main() {
    let ls = [vec![D { name: "a", n: 1 }, D { name: "bb", n: 2 }], vec![D { name: "ccc", n: 3 }]];
    println!("{:?} {:?} {:?} {:?}", names(&ls), flat(&ls), nested(&ls), borrowed(&ls));
}
