// A user `impl fmt::Write` (write_str only, or with write_char): each
// write!, Formatter, pad, Debug-builder, and char write reaches the
// writer as the same call sequence core makes (the Log writer records it).
use std::fmt::{self, Write};

// A writer that logs every call, to compare the call sequence with rustc.
struct Log(Vec<String>);
impl Write for Log {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push(format!("s{s:?}"));
        Ok(())
    }
}

struct Chars(String);
impl fmt::Write for Chars {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push('[');
        self.0.push_str(s);
        self.0.push(']');
        Ok(())
    }
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.0.push('<');
        self.0.push(c);
        self.0.push('>');
        Ok(())
    }
}

struct StrSink<'a>(&'a mut Vec<u8>);
impl std::fmt::Write for StrSink<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.extend_from_slice(s.as_bytes());
        Ok(())
    }
}

#[derive(Debug)]
struct P {
    a: u8,
    b: &'static str,
}

struct Shown;
impl fmt::Display for Shown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("")?;
        f.write_char('x')?;
        write!(f, "{:>3}", 7)
    }
}

// Fails after two writes.
struct Full(u8);
impl Write for Full {
    fn write_str(&mut self, _: &str) -> fmt::Result {
        if self.0 == 0 {
            return Err(fmt::Error);
        }
        self.0 -= 1;
        Ok(())
    }
}

fn put<W: Write>(w: &mut W, n: i32) -> fmt::Result {
    write!(w, "n={n:+04}")?;
    w.write_char('!')?;
    w.write_str(";")
}

fn main() {
    let mut l = Log(Vec::new());
    write!(l, "a{}b{:5}c{:<3}|{:?}", 1, "xy", 'q', "q\"t").unwrap();
    write!(l, "").unwrap();
    write!(l, "lit").unwrap();
    writeln!(l, "{}", Shown).unwrap();
    write!(l, "{:?} {:#?}", P { a: 1, b: "z" }, P { a: 2, b: "w" }).unwrap();
    l.write_char('é').unwrap();
    println!("{:?}", l.0);

    let mut c = Chars(String::new());
    write!(c, "{:>4}{:?}", 'k', 'm').unwrap();
    put(&mut c, 5).unwrap();
    println!("{}", c.0);

    let mut out = Vec::new();
    let _ = write!(StrSink(&mut out), "\\u{:04x}", 0x1fu8);
    println!("{}", String::from_utf8(out).unwrap());

    let mut s = String::new();
    put(&mut s, -3).unwrap();
    println!("{s}");

    let mut full = Full(2);
    println!("{:?} {}", write!(full, "{} {} {}", 1, 2, 3), full.0);
    let mut full = Full(1);
    println!("{:?}", put(&mut full, 1));

    let mut r = Log(Vec::new());
    let w: &mut Log = &mut r;
    put(w, 9).unwrap();
    let mut rr = &mut r;
    put(&mut rr, 8).unwrap();
    println!("{:?}", r.0);
}
