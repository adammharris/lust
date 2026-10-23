// expect: L0110
// rustc E0308: `Literal::name` returns `&str`, not `u8`.
#[derive(Clone, Copy)]
enum Literal { A, B }
impl Literal {
    fn name(self) -> &'static str { match self { Literal::A => "a", Literal::B => "b" } }
    fn name_ref(&self) -> &'static str { self.name() }
    fn pair(self) -> (u8, Option<&'static str>) { (1, Some(self.name())) }
}
const F: fn(Literal) -> u8 = Literal::name;
fn main() {}
