// Associated types of lifetime traits through generic fns and trait methods,
// and a higher-ranked bound passed on (`T: DeserializeOwned`, `for<'de>`).
trait Tr<'a> { type Out; fn get(&self, s: &'a str) -> Self::Out; }
struct S;
impl<'a> Tr<'a> for S { type Out = &'a str; fn get(&self, s: &'a str) -> &'a str { &s[1..] } }
struct N;
impl<'a> Tr<'a> for N { type Out = usize; fn get(&self, s: &'a str) -> usize { s.len() } }
fn use_it<'a, T: Tr<'a>>(t: &T, s: &'a str) -> T::Out { t.get(s) }
fn main1() { let x = String::from("hello"); println!("{} {}", use_it(&S, &x), use_it(&N, &x)); }

fn main() { main1(); }
