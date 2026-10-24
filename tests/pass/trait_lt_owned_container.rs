// A `DeserializeOwned`-style bound on a container whose impl passes the
// trait lifetime to its element (`impl<'de, T> Deserialize<'de> for Vec<T>
// where T: Deserialize<'de>`): general when the element type is.
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
    let w: Vec<Vec<String>> = owned(&text);
    println!("{:?} {:?}", v, w);
}
