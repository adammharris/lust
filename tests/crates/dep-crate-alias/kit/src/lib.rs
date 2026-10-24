pub mod table {
    pub struct Table(pub u8);
    impl Table {
        pub fn double(&self) -> u8 {
            self.0 * 2
        }
    }
}
pub fn hi() -> u8 {
    7
}
