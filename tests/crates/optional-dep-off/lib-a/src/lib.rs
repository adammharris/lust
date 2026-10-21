#[cfg(feature = "lib-bad")]
pub use lib_bad::bad;

#[cfg(feature = "extra")]
pub fn extra() -> u32 {
    lib_good::good() + 1
}

pub fn a() -> u32 {
    1
}
