// `fmt::Error` implements `std::error::Error` (serde's `ser::Error` for
// `fmt::Error` needs it as a supertrait).
use std::error::Error;
use std::fmt::Display;
fn show(e: &dyn Error) -> String {
    format!("{} / {:?} / {}", e, e, e.source().is_none())
}
fn padded<T: Display>(t: T) -> String {
    format!("[{:>50}]", t)
}
fn fails() -> Result<(), Box<dyn Error>> {
    Err(std::fmt::Error.into())
}
fn main() {
    let e = std::fmt::Error;
    println!("{}", show(&e));
    #[allow(deprecated)]
    let d = e.description();
    println!("{}", d);
    let b: Box<dyn Error> = Box::new(e);
    println!("{} {}", b, padded(e));
    println!("{:?}", fails());
}
