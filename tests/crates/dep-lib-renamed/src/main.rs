use kit::Format;

fn main() {
    let f = Format(3);
    println!("{} {} {}", f.0, f.doubled(), kit::Format(4).doubled());
}
