fn main() {
    let g = greet::Greeter::new("lust");
    println!("{}", g.line());
    println!("{}", greet::shout(&g));
}
