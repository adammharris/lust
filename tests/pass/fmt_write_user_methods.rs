// A user writer that overrides write_fmt (through fmt::write), errors
// that stop the formatting, enum and generic writers.
use std::fmt::{self, Write};

struct Log(Vec<String>);
impl Write for Log {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push(format!("{s:?}"));
        Ok(())
    }
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.0.push(format!("c{c}"));
        Ok(())
    }
}

// Overrides write_fmt: write! goes to it with the Arguments value.
struct Upper(String);
impl Write for Upper {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push_str(&s.to_uppercase());
        Ok(())
    }
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        self.0.push('{');
        let r = fmt::write(self, args);
        self.0.push('}');
        r
    }
}

struct Inner(u8);
impl fmt::Display for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.0 {
            f.write_str("i")?;
        }
        Ok(())
    }
}

// Fails on the second call: the Display impl sees the error.
struct Fail(u8);
impl Write for Fail {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += 1;
        if self.0 == 2 { Err(fmt::Error) } else { println!("  wrote {s:?}"); Ok(()) }
    }
}

enum Sink {
    A(Vec<u8>),
    B,
}
impl Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self {
            Sink::A(v) => v.extend_from_slice(s.as_bytes()),
            Sink::B => {}
        }
        Ok(())
    }
}

struct Gen<T>(Vec<T>);
impl<T: From<u8>> Write for Gen<T> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.extend(s.bytes().map(T::from));
        Ok(())
    }
}

fn main() {
    let mut l = Log(Vec::new());
    let x = 5;
    write!(l, "{}{}", x, x).unwrap();
    write!(l, "{x}-").unwrap();
    write!(l, "-{x}").unwrap();
    write!(l, "{:#x} {:e} {:>5.1} {:^7?}", 255, 1.5f64, 2.25f64, Some(1)).unwrap();
    write!(l, "{:?} {:?}", "", "\tq").unwrap();
    write!(l, "{:3}|{:>4}", Inner(1), "ab").unwrap();
    println!("{:?}", l.0);

    let mut u = Upper(String::new());
    write!(u, "a{}b", Inner(2)).unwrap();
    u.write_str("c").unwrap();
    println!("{}", u.0);

    let mut f = Fail(0);
    let r = write!(f, "{}{}", Inner(1), Inner(3));
    println!("{r:?} {}", f.0);

    let mut s = Sink::A(Vec::new());
    write!(s, "{}", 12).unwrap();
    if let Sink::A(v) = &s {
        println!("{v:?}");
    }
    write!(Sink::B, "{}", 1).unwrap();
    let mut g: Gen<u16> = Gen(Vec::new());
    writeln!(g, "{}", 3).unwrap();
    println!("{:?}", g.0);
}
