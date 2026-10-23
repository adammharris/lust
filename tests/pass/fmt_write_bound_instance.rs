// A `W: fmt::Write` bound reaches `write!` on the instance's `String`
// writer without a `use fmt::Write` in the module.
use std::fmt;
trait WriteHex { fn write_hex<W: fmt::Write>(&self, writer: W) -> fmt::Result; }
impl WriteHex for u8 { fn write_hex<W: fmt::Write>(&self, mut writer: W) -> fmt::Result { write!(writer, "{:x}", self) } }
fn to_writer(x: u8, mut writer: impl fmt::Write) -> fmt::Result {
    writer.write_str("0x")?;
    x.write_hex(&mut writer)
}
fn main() {
    let mut s = String::new();
    to_writer(255, &mut s).unwrap();
    println!("{s}");
}
