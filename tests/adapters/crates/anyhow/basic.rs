// The texts every form of `anyhow::Error` prints: Display, `{:#}`,
// Debug with and without causes, and `{:#?}`.
use anyhow::{Context, Error, Result, anyhow, bail, ensure};
use std::fmt;

#[derive(Debug)]
struct Inner;

impl fmt::Display for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("inner failure\nsecond line")
    }
}

impl std::error::Error for Inner {}

#[derive(Debug)]
struct Outer(Inner);

impl fmt::Display for Outer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("outer failure")
    }
}

impl std::error::Error for Outer {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.0)
    }
}

fn parse(s: &str) -> Result<i32> {
    let n: i32 = s.parse().with_context(|| format!("bad number {s:?}"))?;
    Ok(n)
}

fn checked(n: i32) -> Result<i32> {
    ensure!(n >= 0, "negative: {}", n);
    ensure!(n < 100, "too big");
    if n == 42 {
        bail!("the answer {n}");
    }
    if n == 7 {
        let msg = String::from("seven is a message");
        bail!(msg);
    }
    if n == 8 {
        bail!(Outer(Inner));
    }
    Ok(n)
}

fn show(e: &Error) {
    println!("display: {e}");
    println!("alt: {e:#}");
    println!("debug: {e:?}");
    println!("alt debug: {e:#?}");
    println!("chain: {}", e.chain().count());
    println!("root: {}", e.root_cause());
    println!("--");
}

fn main() {
    show(&parse("x").unwrap_err());
    show(&parse("x").context("loading").unwrap_err());
    show(&Error::msg("plain message"));
    show(&anyhow!("formatted {}", 3));
    show(&Error::new(Outer(Inner)));
    show(&Error::new(Outer(Inner)).context("one").context("two"));
    for n in [-1, 100, 42, 7, 8, 5] {
        match checked(n) {
            Ok(v) => println!("ok {v}"),
            Err(e) => show(&e),
        }
    }
    let none: Option<u8> = None;
    show(&none.context("nothing here").unwrap_err());
    show(&none.with_context(|| format!("still {}", "nothing")).unwrap_err());
    let r: Result<u8, std::io::Error> = Err(std::io::Error::new(std::io::ErrorKind::Other, "io broke"));
    show(&r.context("reading").unwrap_err());
    let e = Error::new(Outer(Inner)).context("ctx");
    let rev: Vec<String> = e.chain().rev().map(|c| c.to_string()).collect();
    println!("{rev:?}");
    println!("{}", e.chain().len());
    let boxed: Box<dyn std::error::Error + Send + Sync> = e.into();
    println!("{boxed}");
    println!("{boxed:?}");
    println!("{}", boxed.source().map(|s| s.to_string()).unwrap_or_default());
    show(&anyhow!(Outer(Inner)));
    show(&anyhow!(String::from("owned message")));
    let b: Box<dyn std::error::Error + Send + Sync> = Box::new(Outer(Inner));
    show(&anyhow!(b));
    let wrapped: Result<()> = Err(anyhow!("first")).context("second");
    show(&wrapped.unwrap_err());
    println!("{}", (|| -> Result<u8> { anyhow::Ok(3) })().unwrap());
}
