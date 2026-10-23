// The `impl` form of `bitflags!` over a user struct, `Flags` generic
// use, a flag renamed with `#[bitflags(flag_name)]`, and a cfg'd flag.
use bitflags::{Flags, bitflags};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Raw(u16);

bitflags! {
    impl Raw: u16 {
        const READ = 0b001;
        const WRITE = 0b010;
        #[cfg(any())]
        const NEVER = 0b100;
        const EXEC = 0b100;
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct Named: u8 {
        #[bitflags(flag_name = "first")]
        const ONE = 1;
        const TWO = 2;
    }
}

fn names<F: Flags>() -> Vec<&'static str> {
    F::FLAGS.iter().map(|f| f.name()).collect()
}

fn main() {
    let r = Raw::READ | Raw::EXEC;
    println!("{:?} {}", r, r.bits());
    println!("{:?}", Raw::all());
    println!("{:?}", Raw::from_name("WRITE"));
    println!("{:?}", names::<Raw>());
    println!("{:?}", names::<Named>());
    println!("{:?} {:?}", Named::from_name("first"), Named::from_name("ONE"));
    println!("{:?}", Named::ONE | Named::TWO);
    let mut text = String::new();
    bitflags::parser::to_writer(&(Named::ONE | Named::TWO), &mut text).unwrap();
    println!("{text}");
    for (name, v) in (Raw::READ | Raw::WRITE).iter_names() {
        println!("{name} {}", v.bits());
    }
}
