// `assert_eq!` compares a `Cow<str>` with the other string types, as `==`
// does (std's `PartialEq` impls between them), and prints both sides.
use std::borrow::Cow;
fn main() {
    let c: Cow<str> = String::from_utf8_lossy(b"hi");
    assert_eq!(c, "hi");
    assert_eq!("hi", String::from_utf8_lossy(b"hi"));
    assert_eq!(c, String::from("hi"));
    assert_ne!(String::from("ho"), c);
    let r = std::panic::catch_unwind(|| assert_eq!(String::from_utf8_lossy(b"a\xffb"), "ab"));
    println!("{}", r.is_err());
}
