pub use dep_kit as kit;
use crate::kit::table::Table;

pub mod inner {
    use crate::kit;
    pub fn via_inner() -> u8 {
        kit::hi() + 1
    }
}

pub fn get() -> u8 {
    Table(3).double() + kit::hi() + crate::kit::hi()
}
