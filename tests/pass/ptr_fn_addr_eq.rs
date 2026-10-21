// `ptr::fn_addr_eq` compares two fn pointers by address, also of two
// signatures, as twig compares its custom renderer fns.
use std::ptr;

fn one(x: u8) -> u8 {
    x + 1
}
fn two(x: u8) -> u8 {
    x + 2
}
fn wide(x: u16) -> u16 {
    x
}
enum Renderer {
    Custom(fn(u8) -> u8),
}
fn same(a: &Renderer, b: &Renderer) -> bool {
    match (a, b) {
        (Renderer::Custom(x), Renderer::Custom(y)) => std::ptr::fn_addr_eq(*x, *y),
    }
}
fn main() {
    let f: fn(u8) -> u8 = one;
    let g: fn(u8) -> u8 = one;
    let h: fn(u8) -> u8 = two;
    let w: fn(u16) -> u16 = wide;
    println!("{} {} {}", ptr::fn_addr_eq(f, g), ptr::fn_addr_eq(f, h), ptr::fn_addr_eq(f, w));
    println!("{}", same(&Renderer::Custom(f), &Renderer::Custom(h)));
    println!("{}", ptr::fn_addr_eq::<fn(u8) -> u8, fn(u8) -> u8>(h, two));
}
