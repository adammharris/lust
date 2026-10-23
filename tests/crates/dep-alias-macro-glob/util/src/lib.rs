// A dependency that exports macros under builtin names. They reach the
// main crate only through an import.
#[macro_export]
macro_rules! matches {
    ($($t:tt)*) => {
        false
    };
}

#[macro_export]
macro_rules! write {
    ($($t:tt)*) => {
        Ok::<(), std::fmt::Error>(())
    };
}

pub fn helper() -> i64 {
    2
}
