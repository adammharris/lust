// `impl<O> Tr for dyn Other<O>`: a parameter that occurs only in the dyn
// Self type's trait args is used by the header.
trait Other<O> {
    fn get(&self) -> O;
}
trait Tr {
    type Out;
    fn m(&self) -> Self::Out;
}
impl<O> Tr for dyn Other<O> {
    type Out = O;
    fn m(&self) -> O {
        self.get()
    }
}
struct S;
impl Other<u8> for S {
    fn get(&self) -> u8 {
        7
    }
}
impl Other<String> for S {
    fn get(&self) -> String {
        "s".to_string()
    }
}
fn main() {
    let b: Box<dyn Other<u8>> = Box::new(S);
    let c: Box<dyn Other<String>> = Box::new(S);
    println!("{} {}", b.m(), c.m());
}
