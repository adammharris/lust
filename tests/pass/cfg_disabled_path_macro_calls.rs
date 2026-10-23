// Path macro calls (`crate::err!`, `self::m!`, `super::m!`) in cfg-disabled
// code: expression, statement, pattern, and type position parse.
macro_rules! err { ($k:ident) => { stringify!($k).to_string() }; }
macro_rules! ty { () => { u8 }; }
pub(crate) use err;
pub(crate) use ty;
fn main() { println!("{}", crate::err!(Ok)); }
#[cfg(test)]
mod t {
    fn f() -> String {
        let crate::err!(x) = 1;
        let _v: crate::ty!() = 0;
        super::super::err!(A);
        self::err!(B);
        crate::err!(NotFound)
    }
}
