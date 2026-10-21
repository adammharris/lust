// An impl parameter used only inside a dyn type of the header is
// constrained: in a binding (`Vec<Box<dyn Rule<Out = O>>>`, fig-kit's
// `ChoiceList`) and in the principal's trait args (`dyn Other<O>`).
trait Rule {
    type Out;
    fn m(&self, x: u8) -> Option<Self::Out>;
}
trait ChoiceList {
    type Out;
    fn first(&self, x: u8) -> Option<Self::Out>;
}
impl<O> ChoiceList for Vec<Box<dyn Rule<Out = O>>> {
    type Out = O;
    fn first(&self, x: u8) -> Option<O> {
        self.iter().find_map(|r| r.m(x))
    }
}
trait Other<O> {
    fn make(&self) -> O;
}
trait Twice {
    fn twice(&self) -> String;
}
impl<O: std::fmt::Debug> Twice for dyn Other<O> {
    fn twice(&self) -> String {
        format!("{:?}{:?}", self.make(), self.make())
    }
}
struct Eq(u8);
impl Rule for Eq {
    type Out = u8;
    fn m(&self, x: u8) -> Option<u8> {
        (x == self.0).then_some(x * 10)
    }
}
struct Seven;
impl Other<u8> for Seven {
    fn make(&self) -> u8 {
        7
    }
}
fn main() {
    let rules: Vec<Box<dyn Rule<Out = u8>>> = vec![Box::new(Eq(1)), Box::new(Eq(2))];
    println!("{:?} {:?}", rules.first(2), rules.first(3));
    let o: &dyn Other<u8> = &Seven;
    println!("{}", o.twice());
}
