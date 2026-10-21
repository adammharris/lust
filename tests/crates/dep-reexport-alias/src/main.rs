pub use util_a as helpers;

mod inner {
    pub use util_a;
    use crate::helpers;

    pub fn twice() -> u8 {
        helpers::one() * 2
    }
}

fn main() {
    println!("{} {} {}", helpers::one(), inner::twice(), inner::util_a::one() + crate::helpers::one());
}
