pub struct Format(pub u8);

impl Format {
    pub fn doubled(&self) -> u8 {
        self.0 * 2
    }
}
