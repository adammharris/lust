// Closures that capture nothing, coerced to fn pointers inside const and
// static values, as twig's contract table of move cases is written.
struct Builder {
    nodes: Vec<String>,
}

impl Builder {
    fn add(&mut self, s: &str) -> usize {
        self.nodes.push(s.to_string());
        self.nodes.len() - 1
    }
}

struct MoveCase {
    name: &'static str,
    start: fn(&mut Builder) -> usize,
    expected: fn(&mut Builder) -> usize,
}

const MOVE_CASES: [MoveCase; 2] = [
    MoveCase {
        name: "one",
        start: |b| {
            let q = b.add("a");
            b.add("b") + q
        },
        expected: |b| b.add("c"),
    },
    MoveCase { name: "two", start: |b| b.add("d"), expected: |_| 7 },
];

static PICK: fn(&str) -> &str = |s| s.trim();
const OPS: [(&str, fn(i32, i32) -> i32); 3] = [("add", |a, b| a + b), ("sub", |a, b| a - b), ("pick", |a, b| if a | b > 2 { a } else { b })];

mod m {
    pub const F: fn(u8) -> u8 = |x| x * 3;
}
const F: fn(u8) -> u8 = |x| x + 1;

fn main() {
    for c in &MOVE_CASES {
        let mut b = Builder { nodes: Vec::new() };
        let s = (c.start)(&mut b);
        let e = (c.expected)(&mut b);
        println!("{} {s} {e} {:?}", c.name, b.nodes);
    }
    println!("[{}]", PICK("  hi  "));
    for (name, op) in OPS {
        println!("{name} {}", op(5, 3));
    }
    const LOCAL: fn(u32) -> u32 = |n| match n {
        0 | 1 => 1,
        n => n * 2,
    };
    println!("{} {} {} {}", F(1), m::F(1), LOCAL(1), LOCAL(4));
}
