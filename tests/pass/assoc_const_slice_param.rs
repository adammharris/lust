// A generic body reads an associated const of a param whose type is a
// slice reference (`B::FLAGS`): the template lowers with a placeholder.
pub struct Flag<B> { name: &'static str, value: B }
trait Flags: Sized + 'static { const FLAGS: &'static [Flag<Self>]; }
struct It<B: 'static> { flags: &'static [Flag<B>], idx: usize }
impl<B: Flags> It<B> { fn new() -> Self { It { flags: B::FLAGS, idx: 0 } } }
#[derive(Clone, Copy)]
struct M(u8);
impl Flags for M { const FLAGS: &'static [Flag<M>] = &[Flag { name: "A", value: M(1) }, Flag { name: "B", value: M(2) }]; }
fn main() {
    let it = It::<M>::new();
    println!("{} {} {}", it.flags.len(), it.idx, it.flags[1].name);
    let f: &'static [Flag<M>] = M::FLAGS;
    println!("{}", f[0].value.0);
    fn g<B: Flags>() -> usize { let f = B::FLAGS; f.len() }
    println!("{}", g::<M>());
}
