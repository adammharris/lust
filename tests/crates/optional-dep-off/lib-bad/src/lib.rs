// Valid Rust that lust rejects (L0404): a unit that pulls this crate in
// fails to compile.
#[allow(unused_unsafe)]
pub fn bad() -> u32 {
    unsafe { 7 }
}
