// capability: types: associated type bindings on dyn types of crate traits (`Box<dyn Rule<Out = T>>`), also of a supertrait's associated types
// expect: ok

trait Base {
    type O;
    fn get(&self) -> Self::O;
}

trait Sub: Base {
    fn f(&self) -> u32;
}

struct S;

impl Base for S {
    type O = u8;
    fn get(&self) -> u8 {
        7
    }
}

impl Sub for S {
    fn f(&self) -> u32 {
        1
    }
}

fn g(x: &dyn Base<O = u8>) -> u8 {
    x.get()
}

fn main() {
    let b: Box<dyn Sub<O = u8>> = Box::new(S);
    assert_eq!(b.f(), 1);
    assert_eq!(b.get(), 7);
    assert_eq!(g(&S), 7);
    println!("{} {} {}", b.f(), b.get(), g(&S));
}
