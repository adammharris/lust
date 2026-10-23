// `<u8>::from_str_radix(..)` and kin: a primitive's associated fn
// through a qualified path, as `u8::from_str_radix` resolves, also
// with the type from a macro fragment.
macro_rules! m {
    ($u:ty) => {
        fn parse(s: &str) -> Option<$u> {
            <$u>::from_str_radix(s, 16).ok()
        }
        fn max() -> $u {
            <$u>::MAX
        }
    };
}
m!(u8);
fn main() {
    println!("{:?} {} {:?}", parse("ff"), max(), <u16>::from_str_radix("10", 16));
    println!("{:?} {:?} {}", <u8>::checked_add(1, 2), <i32>::abs(-3), <f64>::sqrt(4.0));
}
