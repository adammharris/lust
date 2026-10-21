// expect: L0110
// rustc E0308: a closure that captures a local cannot become a fn pointer,
// also in a const value.
const ADD: fn(u8) -> u8 = {
    let k = 2;
    move |x| x + k
};
fn main() {
    println!("{}", ADD(1));
}
