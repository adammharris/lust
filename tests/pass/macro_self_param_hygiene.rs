// A `self` param a macro passes in (`params: self`) binds the `self` the
// same expansion writes in the body, two macro levels down.
macro_rules! inner {
    (params: $self:ident; $T:ident { fn e(&self) $c:block }) => {
        impl $T {
            pub fn e(&$self) -> u8 $c
        }
    };
}
macro_rules! outer {
    ($T:ident) => {
        inner! {
            params: self;
            $T {
                fn e(&self) { self.0 }
            }
        }
    };
}
struct S(u8);
outer!(S);
fn main() { let s = S(1); println!("{}", s.e()); }
