// `for<'a> fn(&'a str, &'a str) -> &'a str` and `for<'a, 'b> fn(&'a str, &'b str)
// -> &'a str`: a fn more general than the pointer coerces, and a result that
// borrows only the first input outlives the second.
fn longest<'a>(a: &'a str, b: &'a str) -> &'a str { if a.len() >= b.len() { a } else { b } }
fn first<'a, 'b>(a: &'a str, _b: &'b str) -> &'a str { a }
fn main() {
    let f: for<'a> fn(&'a str, &'a str) -> &'a str = longest;
    let g: for<'a, 'b> fn(&'a str, &'b str) -> &'a str = first;
    let h: for<'a> fn(&'a str, &'a str) -> &'a str = first;
    let s = String::from("hello");
    let r;
    {
        let t = String::from("hi");
        r = g(&s, &t);
        println!("{} {}", f(&s, &t), h(&s, &t));
    }
    println!("{r}");
}
