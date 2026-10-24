// Import paths that walk through a std alias: as the first segment
// (`use std::mem; use mem::swap;`), through a module's re-export of a std
// module (`crate::lib::fmt::Write`, serde's `lib` facade), in fn bodies,
// and through a std source module (`std::net`).
mod lib {
    pub use std::fmt::{self, Display};
    pub use std::net;
    pub use std::result;
}
use std::mem;
use mem::swap;
use std::net as n2;
use n2::Ipv4Addr;
mod a {
    use crate::lib::fmt::{self, Write};
    use crate::lib::result::Result;
    pub fn render(x: i32) -> Result<String, fmt::Error> {
        let mut s = String::new();
        write!(s, "<{}>", x)?;
        Ok(s)
    }
}
fn show<T: lib::Display>(t: T) -> String {
    use crate::lib::fmt::Write;
    let mut s = String::new();
    write!(s, "[{}]", t).unwrap();
    s
}
fn main() {
    let (mut x, mut y) = (1, 2);
    swap(&mut x, &mut y);
    println!("{} {}", x, y);
    println!("{}", a::render(5).unwrap());
    println!("{}", show(3.5));
    use crate::lib::net::IpAddr;
    let ip: IpAddr = "10.0.0.1".parse().unwrap();
    let v4 = Ipv4Addr::new(127, 0, 0, 1);
    let v4b: lib::net::Ipv4Addr = lib::net::Ipv4Addr::new(1, 2, 3, 4);
    println!("{} {} {} {}", ip, v4, v4b, ip.is_ipv4());
}
