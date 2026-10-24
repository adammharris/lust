// Fn item values in const and static items: a free fn returning `&'static str`,
// and `Type::method` paths (by-value and `&self` receivers), as fig-core's
// `const _: fn(Literal) -> &'static str = Literal::name;`.
#[derive(Clone, Copy)]
enum Literal { A, B }
impl Literal {
    fn name(self) -> &'static str { match self { Literal::A => "a", Literal::B => "b" } }
    fn name_ref(&self) -> &'static str { self.name() }
    fn pair(self) -> (u8, Option<&'static str>) { (1, Some(self.name())) }
}
fn free(l: Literal) -> &'static str { l.name() }
const F: fn(Literal) -> &'static str = free;
const G: fn(Literal) -> &'static str = Literal::name;
const _: fn(Literal) -> &'static str = Literal::name;
const R: fn(&Literal) -> &'static str = Literal::name_ref;
const P: fn(Literal) -> (u8, Option<&'static str>) = Literal::pair;
static S: fn(Literal) -> &'static str = Literal::name;
static T: [(&str, fn(Literal) -> &'static str); 1] = [("x", free)];
fn main() {
    println!("{} {} {} {:?}", F(Literal::A), G(Literal::B), R(&Literal::A), P(Literal::B));
    println!("{} {} {}", S(Literal::A), T[0].0, (T[0].1)(Literal::B));
}
