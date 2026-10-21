// A fn pointer casts to an integer: its address. Two pointers to one fn
// compare equal, a pointer to another fn does not.
fn a() {}
fn b() {}
fn main() {
    let f: fn() = a;
    let g: fn() = a;
    let h: fn() = b;
    println!("{} {}", f as usize == g as usize, f as usize == h as usize);
    println!("{}", f as usize != 0);
    println!("{}", (f as u128) == (g as usize as u128));
    println!("{}", (h as u64) as usize == h as usize);
}
