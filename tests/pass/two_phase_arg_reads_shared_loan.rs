// A two-phase `&mut self` receiver whose argument reads through a shared
// borrow of `self` (`self.walk(*c)`): the argument is read before the
// activation, so the shared loan is over by then, as in rustc.
enum K {
    Leaf,
    Group(usize),
}
struct T {
    ks: Vec<K>,
}
impl T {
    fn node(&self, i: usize) -> &K {
        &self.ks[i]
    }
}
struct P {
    t: T,
    n: u32,
    v: usize,
}
impl P {
    fn walk(&mut self, i: usize) -> u32 {
        match &self.t.node(i) {
            K::Leaf => {
                self.n += 1;
                self.n
            }
            K::Group(c) => self.walk(*c),
        }
    }
    fn bump(&mut self, by: usize) -> usize {
        self.v += by;
        self.v
    }
    fn twice(&mut self) -> usize {
        let c = &self.v;
        let a = self.bump(*c);
        let d = &self.v;
        a + self.bump(*d + 1)
    }
}
fn main() {
    let mut p = P { t: T { ks: vec![K::Leaf, K::Group(0), K::Group(1)] }, n: 0, v: 1 };
    println!("{} {}", p.walk(2), p.twice());
}
