// expect: L0112
// Valid Rust: rustc prints `{1: 2..3}`. lust marks ranges for Debug only
// under `Option`, `Result`, `Vec`, `Box`, references, arrays, slices,
// and tuples; one in a `HashMap` would print as its tuple, so it rejects.
fn main() {
    let mut m = std::collections::HashMap::new();
    m.insert(1u8, 2..3u8);
    println!("{:?}", m);
}
