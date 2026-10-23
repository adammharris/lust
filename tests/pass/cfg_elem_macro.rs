// A list element a macro expands under an off `#[cfg]` goes with its
// comma, as a written `#[cfg(off)]` element does, through nested calls.
macro_rules! safe { ($(#[$a:ident $($args:tt)*])* { $e:expr }) => { $(#[$a $($args)*])* { $e } }; }
fn main() {
    let a = [1, #[cfg(any())] 2, 3];
    let b = [safe!({ 1 }), safe!(#[cfg(any())] { 2 }), safe!({ 3 })];
    println!("{:?} {:?}", a, b);
}
