// An assert! text over 78 bytes: rustc breaks it over lines, as lust
// now does. The condition holds, so nothing prints but `ok`.
fn main() {
    let (first_value, second_value, third_value) = (1, 2, 3);
    assert!(first_value == 1 && second_value == 2 && third_value == 3 && first_value + second_value == 3);
    println!("ok");
}
