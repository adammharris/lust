// A cfg value from a macro's `expr` or `literal` fragment that matched one
// string literal (serde's `#[cfg(target_has_atomic = $size)]`).
macro_rules! by_os {
    ($($name:ident $os:expr)*) => {
        $(
            #[cfg(target_os = $os)]
            fn $name() -> bool { true }
            #[cfg(not(target_os = $os))]
            fn $name() -> bool { false }
        )*
    };
}
macro_rules! by_atomic {
    ($($name:ident $size:literal)*) => {
        $(
            #[cfg(target_has_atomic = $size)]
            fn $name() -> &'static str { $size }
        )*
    };
}
by_os! { on_linux "linux" on_plan9 "plan9" }
by_atomic! { a8 "8" a64 "64" aptr "ptr" }
fn main() {
    println!("{} {}", on_linux(), on_plan9());
    println!("{} {} {}", a8(), a64(), aptr());
}
