// `dyn Trait<Assoc = T>` of a crate trait (fig-kit's `BoxRule<O>`): the
// binding fixes the object's associated type, a method through the
// vtable returns it, a blanket impl over `R: Rule + ?Sized` reads it, and
// a combinator holds boxed rules of one answer.
trait Rule {
    type Out;
    fn m(&self, x: u8) -> Option<Self::Out>;
}

trait Matches {
    fn matches(&self, x: u8) -> bool;
}

impl<R: Rule + ?Sized> Matches for R {
    fn matches(&self, x: u8) -> bool {
        self.m(x).is_some()
    }
}

type BoxRule<O> = Box<dyn Rule<Out = O>>;

trait RuleExt: Rule + Sized + 'static {
    fn boxed(self) -> BoxRule<Self::Out> {
        Box::new(self)
    }
}

impl<R: Rule + Sized + 'static> RuleExt for R {}

struct Lit(u8);
impl Rule for Lit {
    type Out = u8;
    fn m(&self, x: u8) -> Option<u8> {
        (x == self.0).then_some(x)
    }
}

struct Named(&'static str);
impl Rule for Named {
    type Out = String;
    fn m(&self, x: u8) -> Option<String> {
        (x as usize == self.0.len()).then(|| self.0.to_string())
    }
}

struct Alt<O>(Vec<BoxRule<O>>);
impl<O: 'static> Rule for Alt<O> {
    type Out = O;
    fn m(&self, x: u8) -> Option<O> {
        self.0.iter().find_map(|r| r.m(x))
    }
}

fn first<O>(rules: &[BoxRule<O>], x: u8) -> Option<O> {
    rules.iter().find_map(|r| r.m(x))
}

fn main() {
    let r: BoxRule<u8> = Box::new(Lit(3));
    println!("{:?} {:?}", r.m(3), r.m(4));
    println!("{}", r.matches(3));
    let alt = Alt(vec![Lit(1).boxed(), Box::new(Lit(2))]);
    println!("{:?} {:?}", alt.m(2), alt.m(5));
    let names: Vec<BoxRule<String>> = vec![Named("ab").boxed(), Box::new(Named("xyz"))];
    println!("{:?} {:?}", first(&names, 3), first(&names, 4));
    let nested: BoxRule<u8> = alt.boxed();
    println!("{:?}", nested.m(1));
}
