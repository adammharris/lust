// `flat_map` items hold what the closure returns, not the outer iterator's loan:
// over `&[&'static dyn L]`, `l.n().iter().copied()` yields `&'static str` items, as
// fig-core's `all_dialects`.
trait L { fn n(&self) -> &[&'static str]; fn s(&self) -> &'static str; }
struct J;
impl L for J { fn n(&self) -> &[&'static str] { &["j", "k"] } fn s(&self) -> &'static str { "s" } }
static JJ: J = J;
fn f(ls: &[&'static dyn L]) -> Vec<&'static str> { ls.iter().flat_map(|l| l.n().iter().copied()).collect() }
fn main0() { let v: [&'static dyn L; 1] = [&JJ]; println!("{:?}", f(&v)); }
fn g(ls: &[&'static dyn L]) -> Vec<&'static str> { ls.iter().copied().flat_map(|l| l.n().iter().copied()).collect() }
fn main() { main0(); let v: [&'static dyn L; 1] = [&JJ]; println!("{:?}", g(&v)); }
