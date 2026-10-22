// `let _: T = init` with a `T` that names a lifetime checks the value
// against it, as twig's api_surface test pins its fn signatures.
#[derive(Clone, Copy)]
enum Format {
    Djot,
}
impl Format {
    fn name(self) -> &'static str {
        match self {
            Format::Djot => "djot",
        }
    }
}
fn label(s: &'static str) -> &'static str {
    s
}
fn main() {
    let _: fn(Format) -> &'static str = Format::name;
    let _: fn(&'static str) -> &'static str = label;
    let _: &'static str = "plain";
    let _: (&'static str, u8) = ("pair", 1);
    println!("{}", Format::Djot.name());
}
