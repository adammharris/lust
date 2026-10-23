// Path hashes by components as in std, so a PathBuf is a map key.
use std::collections::HashMap;
use std::path::PathBuf;
fn main() {
    let mut s: HashMap<PathBuf, u8> = HashMap::new();
    s.insert("a".into(), 1);
    println!("{}", s.len());
}
