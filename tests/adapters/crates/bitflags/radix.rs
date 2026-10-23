// lust-reject: L0112
// `{:x}` and kin of a flags value: upstream forwards to the bits. Lust
// has no user impls of the radix fmt traits yet.
use bitflags::bitflags;

bitflags! {
    #[derive(Debug, Clone, Copy)]
    struct F: u8 {
        const A = 1;
        const B = 2;
    }
}

fn main() {
    let f = F::A | F::B;
    println!("{f:#x} {f:#b} {f:o} {f:X}");
}
