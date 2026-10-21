// A plain dependency of the lib: its module file imports it, so the lib
// built again for the helper needs it too.
pub mod bytes {
    pub fn is_digit(b: &u8) -> bool {
        b.is_ascii_digit()
    }
}
