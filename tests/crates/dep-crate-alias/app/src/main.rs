use dep_core::kit::table::Table;

fn main() {
    println!("{}", dep_core::get());
    println!("{}", dep_core::inner::via_inner());
    println!("{}", Table(5).double());
    println!("{}", dep_core::kit::hi());
}
