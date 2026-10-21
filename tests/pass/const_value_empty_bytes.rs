// A const value that holds an empty byte string (fig-kit's `Syntax::new`
// fills its unused separators with `b""`): its static temp is a struct
// whose one member is `v[0]`, so it takes no initializer in C.
struct Syntax {
    open: &'static [u8],
    pad: Option<&'static [u8]>,
    close: &'static [u8],
}

const fn base(pad: Option<&'static [u8]>) -> Syntax {
    Syntax { open: b"", pad, close: b"" }
}

const FIGL: Syntax = Syntax { open: b">+", ..base(Some(b"{}")) };
static EMPTY: Syntax = base(None);

fn main() {
    let s = FIGL;
    println!("{:?} {:?} {:?}", s.open, s.pad, s.close);
    println!("{} {:?} {}", EMPTY.open.len(), EMPTY.pad, EMPTY.close.is_empty());
}
