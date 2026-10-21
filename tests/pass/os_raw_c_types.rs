// The C type aliases of `std::os::raw` and `std::ffi` on 64-bit Linux.
use std::ffi::{c_long, c_uint};
use std::os::raw::{c_char, c_double, c_int, c_uchar, c_ulong};
fn main() {
    let x: c_int = -3;
    let y: c_uint = 4;
    let z: c_long = i64::MIN;
    let w: c_ulong = u64::MAX;
    let d: c_double = 0.5;
    let u: c_uchar = 255;
    let c: c_char = b'a' as c_char;
    println!("{x} {y} {z} {w} {d} {u} {}", c as u8 as char);
    println!("{}", std::mem::size_of::<std::os::raw::c_short>() + std::mem::size_of::<std::ffi::c_longlong>());
}
