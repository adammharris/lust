// An `item` fragment ends an impl item, so an empty call after it takes
// its own `;`.
macro_rules! flag {
    ({ name: _, named: { $($named:tt)* }, unnamed: { $($unnamed:tt)* }, }) => { $($unnamed)* };
    ({ name: $F:ident, named: { $($named:tt)* }, unnamed: { $($unnamed:tt)* }, }) => { $($named)* };
}
macro_rules! safe {
    ({ $i:item }) => { safe! { item: { $i }, } };
    (item: { $i:item }, ) => { $i };
}
macro_rules! consts {
    ($($F:tt = $v:expr;)*) => {
        impl S {
            $(
                flag!({ name: $F, named: { safe!({ pub const $F: u8 = $v; }); }, unnamed: {}, });
            )*
        }
    };
}
struct S;
consts! { A = 1; _ = 2; }
consts! { B = 1; }
fn main() { println!("{} {}", S::A, S::B); }
