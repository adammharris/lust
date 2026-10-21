// A `use` path through a module's std alias goes on as the std path:
// `pub use std::*;` (serde's `crate::lib`) and `pub use std::net;` both
// let `self::core::cell::Cell` or `crate::lib::net::IpAddr` name the std
// item, at module level and in a fn body. A primitive-named std module
// (`f32`) under the glob leaves the name a type in that module.
mod lib {
    mod core {
        pub use std::*;
    }
    pub use self::core::cell::Cell;
    pub use self::core::fmt::{self, Display};
    pub use self::core::net;
    pub use self::core::str;
    pub use self::core::{f32, f64};
}
mod glob_user {
    pub use std::*;
    pub fn half(x: f32) -> f32 {
        let y: f64 = x as f64 / 2.0;
        y as f32
    }
}
mod direct {
    pub use std::cell;
    pub use std::net;
}
use direct::net::Ipv4Addr;
use lib::*;

fn show<T: Display>(t: T) -> String {
    fmt::format(format_args!("<{t}>"))
}

fn kind(a: &net::IpAddr) -> &'static str {
    use crate::lib::net::IpAddr;
    match a {
        IpAddr::V4(_) => "v4",
        IpAddr::V6(_) => "v6",
    }
}

fn main() {
    let c = Cell::new(3);
    c.set(c.get() + 1);
    let r = direct::cell::RefCell::new(vec![1]);
    r.borrow_mut().push(2);
    let a: lib::net::IpAddr = "127.0.0.1".parse().unwrap();
    println!("{} {} {:?} {:?}", c.get(), show(5), str::from_utf8(b"hi"), r.borrow());
    println!("{} {} {} {}", kind(&a), a, Ipv4Addr::LOCALHOST, glob_user::half(3.0));
}
