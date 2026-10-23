// An empty byte string from a const fn, through an associated const used in a
// fn body (fig-kit's `Comments::HASH`): its `[u8; 0]` static takes no `{0}`.
#[derive(Debug, Clone, Copy)]
pub struct Delim { pub open: &'static [u8], pub close: &'static [u8], pub forbidden: Option<&'static [u8]> }
impl Delim {
    pub const fn open(open: &'static [u8]) -> Delim { Delim { open, close: b"", forbidden: None } }
}
#[derive(Debug, Clone, Copy)]
pub struct Comments { pub line: Option<Delim>, pub trailing: Option<Delim>, pub block: Option<Delim> }
impl Comments {
    pub const HASH: Comments = Comments { line: Some(Delim::open(b"#")), trailing: Some(Delim::open(b"#")), block: None };
}
#[derive(Debug)]
pub struct Syntax { pub c: Comments, pub pad: &'static [u8] }
pub fn syntax() -> Syntax { Syntax { c: Comments::HASH, pad: b" " } }
fn main() { println!("{:?}", syntax()); }
