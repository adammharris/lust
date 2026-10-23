// `if let` knows the scrutinee's type after the fn item's output is
// solved (`and_then(V::as_mapping)`), as `match` does.
struct V(Vec<(String, u8)>);
impl V {
    fn as_mapping(&self) -> Option<&[(String, u8)]> { Some(self.0.as_slice()) }
    fn get(&self, _k: &str) -> Option<&V> { Some(self) }
}
fn main() {
    let v = V(vec![("a".to_string(), 1u8)]);
    if let Some(entries) = v.get("t").and_then(V::as_mapping) {
        for (k, n) in entries { println!("{k} {n}"); }
    }
    if let Some(entries) = v.get("t").and_then(|x| x.as_mapping()) {
        for (k, n) in entries { println!("{k} {n}"); }
    }
}
