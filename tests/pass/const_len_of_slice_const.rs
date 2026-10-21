// An array length in a type from a const whose value is the `.len()` of
// another const's slice, array, or byte string literal.
#[derive(Clone, Copy, Debug)]
enum Tag {
    A,
    B,
    C,
}
impl Tag {
    const ALL: &'static [Tag] = &[Tag::A, Tag::B, Tag::C];
    const COUNT: usize = Tag::ALL.len();
    const SELF_COUNT: usize = Self::ALL.len();
}
const BYTES: &[u8] = b"abcd";
const ARR: [u8; 2] = [0; 2];
const FREE: usize = BYTES.len() + ARR.len();

struct S {
    x: [u32; Tag::COUNT],
    y: [u8; FREE],
    z: [bool; Tag::SELF_COUNT],
}

fn main() {
    let s = S { x: [0; Tag::COUNT], y: [1; FREE], z: [true; Tag::SELF_COUNT] };
    println!("{} {} {} {:?}", s.x.len(), s.y.len(), s.z.len(), Tag::ALL[2]);
}
