// A cfg value a macro passes in an `expr` or `literal` fragment reads as
// the literal, as serde's `atomic_impl!` writes `target_has_atomic = $size`.
macro_rules! width_impl {
    ($($name:ident $width:expr)*) => {
        $(
            #[cfg(target_pointer_width = $width)]
            fn $name() -> &'static str {
                $width
            }
            #[cfg(not(target_pointer_width = $width))]
            fn $name() -> &'static str {
                "other"
            }
        )*
    };
}
macro_rules! os_name {
    ($os:literal) => {
        #[cfg(target_os = $os)]
        const OS: &str = $os;
        #[cfg(not(target_os = $os))]
        const OS: &str = "elsewhere";
    };
}
width_impl! {
    w64 "64"
    w32 "32"
}
os_name!("linux");
fn main() {
    println!("{} {} {}", w64(), w32(), OS);
}
