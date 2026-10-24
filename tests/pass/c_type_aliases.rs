// The C type aliases of `std::ffi` and `std::os::raw` (fig's `use
// std::os::raw::c_int;`).
use std::ffi::{c_char, c_int, c_long};
use std::os::raw::{c_uint, c_ulong};
use std::collections::HashMap;
pub struct Format(c_int);
fn main() {
    let f = Format(3 as c_int);
    let m: HashMap<c_int, &str> = [(1, "a")].into_iter().collect();
    let c: c_char = 65 as c_char;
    let x: c_long = -5;
    let u: c_uint = 7;
    let ul: c_ulong = 9;
    println!("{} {:?} {} {} {} {} {}", f.0, m.get(&1), c, x, u, ul, std::mem::size_of::<c_long>());
}
