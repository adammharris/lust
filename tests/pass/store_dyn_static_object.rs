// A builtin store of a `&'a (dyn Tr + 'static)` relates the reference and
// the object lifetime one by one: `v.push(x)` and `v.insert(0, x)` no
// longer ask `'a: 'static` (a dyn whose trait args hold no region is a
// plain stored value). The neighbours (VecDeque, HashMap, Option::insert,
// a `dyn Debug + Send + Sync`) store the same way.
use std::collections::{HashMap, VecDeque};
use std::error::Error;
use std::fmt::Debug;

fn push<'a>(x: &'a (dyn Error + 'static)) -> usize {
    let mut rest = Vec::new();
    rest.push(x);
    rest.len()
}

fn push_annot<'a>(x: &'a (dyn Error + 'static)) -> usize {
    let mut rest: Vec<&'a (dyn Error + 'static)> = Vec::new();
    rest.push(x);
    rest.len()
}

fn deque<'a>(x: &'a (dyn Error + 'static)) -> usize {
    let mut q = VecDeque::new();
    q.push_back(x);
    q.push_front(x);
    q.len()
}

fn insert<'a>(x: &'a (dyn Error + 'static)) -> usize {
    let mut v = Vec::new();
    v.insert(0, x);
    v.insert(0, x);
    v.len()
}

fn map<'a>(x: &'a (dyn Error + 'static)) -> usize {
    let mut m = HashMap::new();
    m.insert(1u8, x);
    m.insert(2u8, x);
    m.len()
}

fn opt<'a>(x: &'a (dyn Error + 'static)) -> String {
    let mut o = None;
    let r = o.insert(x);
    r.to_string()
}

fn debug_send<'a>(x: &'a (dyn Debug + Send + Sync + 'static)) -> String {
    let mut v = Vec::new();
    v.push(x);
    let mut q = VecDeque::new();
    q.push_back(x);
    let mut m = HashMap::new();
    m.insert("k", x);
    let mut o = None;
    o.insert(x);
    format!("{:?} {} {} {}", v, q.len(), m.len(), o.is_some())
}

// The stored reference keeps its own lifetime: the Vec borrows `x` only.
fn keep<'a>(x: &'a (dyn Error + 'static)) -> Vec<&'a (dyn Error + 'static)> {
    let mut v = Vec::new();
    v.push(x);
    v
}

#[derive(Debug)]
struct E;
impl std::fmt::Display for E {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "e")
    }
}
impl Error for E {}

fn main() {
    let e = E;
    println!("{} {} {} {} {} {}", push(&e), push_annot(&e), deque(&e), insert(&e), map(&e), opt(&e));
    let n = 7u32;
    println!("{}", debug_send(&n));
    println!("{}", keep(&e).len());
}
