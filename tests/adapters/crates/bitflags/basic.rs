// The generated flags type: consts, set operations, iteration, the
// text forms (Debug, Display through the parser), and parsing.
use bitflags::{Flags, bitflags};

bitflags! {
    /// Edges of a box.
    #[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Edges: u8 {
        const NONE = 0;
        const TOP = 1 << 0;
        const LEFT = 1 << 1;
        const BOTTOM = 1 << 2;
        const RIGHT = 1 << 3;
        const ALL = Edges::TOP.bits() | Edges::LEFT.bits() | Edges::BOTTOM.bits() | Edges::RIGHT.bits();
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct Mask: u32 {
        const A = 0b0001;
        const B = 0b0010;
        const AB = Self::A.bits() | Self::B.bits();
        const _ = !0;
    }
}

bitflags! {
    #[derive(Copy, Clone)]
    pub struct Test: u32 {
        const X = 0b00000001;
        const Y = 0b00000010;
    }
}

fn main() {
    let e = Edges::TOP | Edges::LEFT;
    println!("{e:?}");
    println!("{:?}", Edges::empty());
    println!("{:?}", Edges::all());
    println!("{:?}", Edges::from_bits_retain(0b1_0001));
    println!("{:?} {:?}", Edges::from_bits(0b1_0000), Edges::from_bits(0b0101));
    println!("{:?}", Edges::from_bits_truncate(0xff));
    println!("{} {} {}", e.bits(), e.contains(Edges::TOP), e.intersects(Edges::RIGHT));
    println!("{} {}", e.is_empty(), Edges::ALL.is_all());
    let mut m = e;
    m.insert(Edges::BOTTOM);
    m.remove(Edges::TOP);
    m.toggle(Edges::RIGHT);
    m.set(Edges::LEFT, false);
    println!("{m:?}");
    println!("{:?} {:?}", e & m, e ^ m);
    println!("{:?} {:?} {:?}", e - Edges::TOP, !e, e.complement());
    println!("{:?}", e.union(Edges::RIGHT).difference(Edges::LEFT).symmetric_difference(Edges::BOTTOM));
    for f in Edges::ALL.iter() {
        print!("{f:?} ");
    }
    println!();
    for (name, f) in (Edges::TOP | Edges::RIGHT).iter_names() {
        print!("{name}={} ", f.bits());
    }
    println!();
    let collected: Edges = [Edges::TOP, Edges::BOTTOM].into_iter().collect();
    println!("{collected:?}");
    let mut ext = Edges::empty();
    ext.extend([Edges::LEFT, Edges::RIGHT]);
    println!("{ext:?}");
    println!("{:?}", Edges::from_name("LEFT"));
    println!("{:?}", Edges::from_name("left"));
    let mut text = String::new();
    bitflags::parser::to_writer(&e, &mut text).unwrap();
    println!("{text}");
    let parsed: Edges = bitflags::parser::from_str("TOP | RIGHT | 0x10").unwrap();
    println!("{parsed:?}");
    match bitflags::parser::from_str::<Edges>("TOP | NOPE") {
        Ok(v) => println!("ok {v:?}"),
        Err(err) => println!("err {err}"),
    }
    match bitflags::parser::from_str::<Edges>("") {
        Ok(v) => println!("ok {v:?}"),
        Err(err) => println!("err {err}"),
    }
    println!("{:?}", Mask::from_bits(0xf0));
    println!("{:?} {:?}", Mask::all(), Mask::AB);
    println!("{:?}", Mask::from_bits_retain(0b0101));
    println!("{}", Edges::FLAGS.len());
    for f in Edges::FLAGS {
        print!("{}:{} ", f.name(), f.value().bits());
    }
    println!();
    println!("{}", (Test::X | Test::Y).bits());
    let mut h = std::collections::HashSet::new();
    h.insert(Edges::TOP);
    println!("{}", h.contains(&Edges::TOP));
    println!("{:?}", Edges::default());
    println!("{}", Edges::TOP < Edges::LEFT);
}
