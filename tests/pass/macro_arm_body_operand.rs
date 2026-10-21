// A `()` macro call that starts a match arm's body is an expression in
// rustc, so an operator after it continues the body. `matches!` expands
// to a `match`, which would end the arm in a flat token stream.
fn main() {
    let x = std::env::args().count();
    let a = match x { 1 | 2 => matches!(x, 3) || x > 5, _ => false };
    let b = match x { 1 => matches!(x, 1) && x < 5, _ => true };
    let c = match x { 0 => true, _ => matches!(x, 1 | 2) == !matches!(x, 3..) };
    let d = match x { _ => vec![x].is_empty() || format!("{x}").len() == 1 };
    println!("{a} {b} {c} {d}");
}
