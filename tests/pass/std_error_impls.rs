// The std error types implement `std::error::Error` (no source), so they
// go behind `&dyn Error` and into `Box<dyn Error + Send + Sync>`.
use std::error::Error;
fn show(e: &dyn Error) { println!("{e} | {e:?} | {}", e.source().is_none()); }
fn main() {
    show(&"x".parse::<i32>().unwrap_err());
    show(&"x".parse::<f64>().unwrap_err());
    show(&"x".parse::<bool>().unwrap_err());
    show(&"xy".parse::<char>().unwrap_err());
    show(&std::str::from_utf8(&[0xff]).unwrap_err());
    show(&String::from_utf8(vec![0xff]).unwrap_err());
    show(&<[u8; 2]>::try_from(&[1u8][..]).unwrap_err());
    show(&std::fmt::Error);
    show(&std::env::var("LUST_SURELY_UNSET_VAR").unwrap_err());
    show(&std::path::Path::new("/a").strip_prefix("/b").unwrap_err());
    { let c = std::cell::RefCell::new(1); let _g = c.borrow(); show(&c.try_borrow_mut().map(|_| ()).unwrap_err()); }
    let b: Box<dyn Error + Send + Sync> = "x".parse::<u8>().unwrap_err().into();
    show(&*b);
}
