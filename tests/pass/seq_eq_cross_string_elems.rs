// Sequences of two string types compare element by element: core's
// array, slice, and Vec `PartialEq` impls take `T: PartialEq<U>`, and
// `&str: PartialEq<String>` holds.
use std::borrow::Cow;
fn ignored() -> Vec<String> {
    vec!["dialect".into(), "colour".into(), "sparkles".into()]
}
fn main() {
    let v = ignored();
    let r: &[String] = &v;
    assert_eq!(["dialect", "colour", "sparkles"], r);
    assert_eq!(r, ["dialect", "colour", "sparkles"]);
    assert_ne!(["dialect", "colour"], r);
    assert_ne!(["dialect", "colour", "glitter"], r);
    println!("{} {}", ["dialect", "colour", "sparkles"] == r, r != ["a", "b", "c"]);
    let strs: Vec<&str> = vec!["a", "b"];
    let owned = vec![String::from("a"), String::from("b")];
    println!("{} {} {}", strs == owned, owned == strs, strs[..] == owned[..1]);
    let cows: Vec<Cow<str>> = vec![Cow::Borrowed("a"), Cow::Owned(String::from("b"))];
    println!("{} {}", cows == strs, cows == owned);
    let empty: [&str; 0] = [];
    let none: &[String] = &[];
    assert_eq!(empty, none);
    let r = std::panic::catch_unwind(|| assert_eq!(["x", "y"], &ignored()[..2]));
    println!("{}", r.is_err());
}
