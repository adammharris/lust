// `Box<dyn Rule<Out = O>>` as fig's grammar kit uses it: a forwarding
// `impl Rule for Box<R>`, a provided `boxed` that returns
// `Box<dyn Rule<Out = Self::Out>>`, a generic rule over a fn pointer, and
// calls through `&dyn`, a slice of boxes and a generic `R: Rule`.
trait Rule {
    type Out;
    fn match_(&self, input: &str) -> Option<Self::Out>;
}

impl<R: Rule + ?Sized> Rule for Box<R> {
    type Out = R::Out;
    fn match_(&self, input: &str) -> Option<R::Out> {
        (**self).match_(input)
    }
}

type BoxRule<O> = Box<dyn Rule<Out = O>>;

trait RuleExt: Rule + Sized + 'static {
    fn boxed(self) -> BoxRule<Self::Out> {
        Box::new(self)
    }
}
impl<R: Rule + 'static> RuleExt for R {}

struct Len;
impl Rule for Len {
    type Out = usize;
    fn match_(&self, input: &str) -> Option<usize> {
        if input.is_empty() { None } else { Some(input.len()) }
    }
}

struct Word(&'static str);
impl Rule for Word {
    type Out = String;
    fn match_(&self, input: &str) -> Option<String> {
        input.starts_with(self.0).then(|| self.0.to_string())
    }
}

struct Map<R: Rule, U> {
    r: R,
    f: fn(R::Out) -> U,
}
impl<R: Rule, U> Rule for Map<R, U> {
    type Out = U;
    fn match_(&self, input: &str) -> Option<U> {
        self.r.match_(input).map(self.f)
    }
}

fn times_ten(s: String) -> usize {
    s.len() * 10
}

fn first<O>(rules: &[BoxRule<O>], input: &str) -> Option<O> {
    for r in rules {
        if let Some(v) = r.match_(input) {
            return Some(v);
        }
    }
    None
}

fn via_ref(r: &dyn Rule<Out = usize>, s: &str) -> usize {
    r.match_(s).unwrap_or(0)
}

fn generic<R: Rule>(r: &R, s: &str) -> Option<R::Out> {
    r.match_(s)
}

fn main() {
    let a: BoxRule<usize> = Box::new(Len);
    let b = Map { r: Word("ab"), f: times_ten }.boxed();
    let rules = vec![b, a];
    println!("{:?}", first(&rules, "abc"));
    println!("{:?}", first(&rules, "xyz"));
    println!("{:?}", first(&rules, ""));
    println!("{}", via_ref(&Len, "hello"));
    let w: BoxRule<String> = Box::new(Word("he"));
    println!("{:?}", generic(&w, "hello"));
    let o: Option<String> = w.match_("hey");
    println!("{:?}", o);
}
