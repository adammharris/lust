// expect: L0735
// rustc: implementation of `Deserialize` is not general enough: `Vec<&str>`
// passes the trait lifetime to `&str`, whose impl holds for some only.
trait Deserialize<'de>: Sized {
    fn de(s: &'de str) -> Self;
}
trait DeserializeOwned: for<'de> Deserialize<'de> {}
impl<T> DeserializeOwned for T where T: for<'de> Deserialize<'de> {}
impl<'de> Deserialize<'de> for String {
    fn de(s: &'de str) -> String { s.to_string() }
}
impl<'de: 'a, 'a> Deserialize<'de> for &'a str {
    fn de(s: &'de str) -> &'a str { s }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Vec<T> {
    fn de(s: &'de str) -> Vec<T> { s.split(',').map(T::de).collect() }
}
fn owned<T: DeserializeOwned>(text: &str) -> T {
    T::de(text)
}
fn main() {
    let text = String::from("a,b");
    let v: Vec<String> = owned(&text);
    let w: Vec<&str> = owned(&text);
    println!("{:?} {:?}", v, w);
}
