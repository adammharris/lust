// `doctest` is a well-known cfg name, off in a normal build.
#[cfg(doctest)]
fn only_in_doctests() -> u8 {
    1
}

#[cfg(not(doctest))]
fn always() -> u8 {
    2
}

fn main() {
    println!("{} {}", always(), cfg!(doctest));
}
