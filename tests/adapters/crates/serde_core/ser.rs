// A text Serializer over serde_core's traits: the std impls (primitives,
// strings, options, tuples, collections, arrays, smart pointers, cells,
// Duration, PathBuf, IP addresses) and the compound serializer traits.
use serde_core::ser::{
    self, Serialize, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
    SerializeTupleStruct, SerializeTupleVariant, Serializer,
};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

#[derive(Debug)]
struct Error(String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
impl ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(msg.to_string())
    }
}

struct Text;
struct Compound {
    out: String,
    first: bool,
    close: &'static str,
}
impl Compound {
    fn open(open: &str, close: &'static str) -> Compound {
        Compound { out: open.to_string(), first: true, close }
    }
    fn sep(&mut self) {
        if !self.first {
            self.out.push_str(", ");
        }
        self.first = false;
    }
    fn push<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.sep();
        self.out.push_str(&v.serialize(Text)?);
        Ok(())
    }
    fn field<T: ?Sized + Serialize>(&mut self, k: &str, v: &T) -> Result<(), Error> {
        self.sep();
        self.out.push_str(k);
        self.out.push_str(": ");
        self.out.push_str(&v.serialize(Text)?);
        Ok(())
    }
    fn done(mut self) -> Result<String, Error> {
        self.out.push_str(self.close);
        Ok(self.out)
    }
}
impl SerializeSeq for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_element<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.push(v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeTuple for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_element<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.push(v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeTupleStruct for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.push(v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeTupleVariant for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.push(v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeMap for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_key<T: ?Sized + Serialize>(&mut self, k: &T) -> Result<(), Error> {
        self.sep();
        self.out.push_str(&k.serialize(Text)?);
        Ok(())
    }
    fn serialize_value<T: ?Sized + Serialize>(&mut self, v: &T) -> Result<(), Error> {
        self.out.push_str(" => ");
        self.out.push_str(&v.serialize(Text)?);
        Ok(())
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeStruct for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, k: &'static str, v: &T) -> Result<(), Error> {
        self.field(k, v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}
impl SerializeStructVariant for Compound {
    type Ok = String;
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, k: &'static str, v: &T) -> Result<(), Error> {
        self.field(k, v)
    }
    fn end(self) -> Result<String, Error> {
        self.done()
    }
}

impl Serializer for Text {
    type Ok = String;
    type Error = Error;
    type SerializeSeq = Compound;
    type SerializeTuple = Compound;
    type SerializeTupleStruct = Compound;
    type SerializeTupleVariant = Compound;
    type SerializeMap = Compound;
    type SerializeStruct = Compound;
    type SerializeStructVariant = Compound;
    fn serialize_bool(self, v: bool) -> Result<String, Error> {
        Ok(format!("{}", v))
    }
    fn serialize_i8(self, v: i8) -> Result<String, Error> {
        Ok(format!("{}i8", v))
    }
    fn serialize_i16(self, v: i16) -> Result<String, Error> {
        Ok(format!("{}i16", v))
    }
    fn serialize_i32(self, v: i32) -> Result<String, Error> {
        Ok(format!("{}i32", v))
    }
    fn serialize_i64(self, v: i64) -> Result<String, Error> {
        Ok(format!("{}i64", v))
    }
    fn serialize_i128(self, v: i128) -> Result<String, Error> {
        Ok(format!("{}i128", v))
    }
    fn serialize_u8(self, v: u8) -> Result<String, Error> {
        Ok(format!("{}u8", v))
    }
    fn serialize_u16(self, v: u16) -> Result<String, Error> {
        Ok(format!("{}u16", v))
    }
    fn serialize_u32(self, v: u32) -> Result<String, Error> {
        Ok(format!("{}u32", v))
    }
    fn serialize_u64(self, v: u64) -> Result<String, Error> {
        Ok(format!("{}u64", v))
    }
    fn serialize_u128(self, v: u128) -> Result<String, Error> {
        Ok(format!("{}u128", v))
    }
    fn serialize_f32(self, v: f32) -> Result<String, Error> {
        Ok(format!("{:?}f32", v))
    }
    fn serialize_f64(self, v: f64) -> Result<String, Error> {
        Ok(format!("{:?}f64", v))
    }
    fn serialize_char(self, v: char) -> Result<String, Error> {
        Ok(format!("{:?}", v))
    }
    fn serialize_str(self, v: &str) -> Result<String, Error> {
        Ok(format!("{:?}", v))
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<String, Error> {
        Ok(format!("b{:?}", v))
    }
    fn serialize_none(self) -> Result<String, Error> {
        Ok("None".to_string())
    }
    fn serialize_some<T: ?Sized + Serialize>(self, v: &T) -> Result<String, Error> {
        Ok(format!("Some({})", v.serialize(Text)?))
    }
    fn serialize_unit(self) -> Result<String, Error> {
        Ok("()".to_string())
    }
    fn serialize_unit_struct(self, name: &'static str) -> Result<String, Error> {
        Ok(name.to_string())
    }
    fn serialize_unit_variant(self, name: &'static str, index: u32, variant: &'static str) -> Result<String, Error> {
        Ok(format!("{}::{}#{}", name, variant, index))
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(self, name: &'static str, v: &T) -> Result<String, Error> {
        Ok(format!("{}({})", name, v.serialize(Text)?))
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        v: &T,
    ) -> Result<String, Error> {
        Ok(format!("{}::{}#{}({})", name, variant, index, v.serialize(Text)?))
    }
    fn serialize_seq(self, len: Option<usize>) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("seq{:?}[", len), "]"))
    }
    fn serialize_tuple(self, len: usize) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("tuple{}(", len), ")"))
    }
    fn serialize_tuple_struct(self, name: &'static str, len: usize) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("{}/{}(", name, len), ")"))
    }
    fn serialize_tuple_variant(self, name: &'static str, i: u32, v: &'static str, len: usize) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("{}::{}#{}/{}(", name, v, i, len), ")"))
    }
    fn serialize_map(self, len: Option<usize>) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("map{:?}{{", len), "}"))
    }
    fn serialize_struct(self, name: &'static str, len: usize) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("{}/{} {{", name, len), "}"))
    }
    fn serialize_struct_variant(self, name: &'static str, i: u32, v: &'static str, len: usize) -> Result<Compound, Error> {
        Ok(Compound::open(&format!("{}::{}#{}/{} {{", name, v, i, len), "}"))
    }
}

struct Point {
    x: i32,
    y: i32,
}
impl Serialize for Point {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut st = s.serialize_struct("Point", 2)?;
        st.serialize_field("x", &self.x)?;
        st.serialize_field("y", &self.y)?;
        st.end()
    }
}
enum Shape {
    Dot,
    Circle(u8),
    Line(i8, i8),
    Rect { w: u16, h: u16 },
}
impl Serialize for Shape {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        match self {
            Shape::Dot => s.serialize_unit_variant("Shape", 0, "Dot"),
            Shape::Circle(r) => s.serialize_newtype_variant("Shape", 1, "Circle", r),
            Shape::Line(a, b) => {
                let mut t = s.serialize_tuple_variant("Shape", 2, "Line", 2)?;
                t.serialize_field(a)?;
                t.serialize_field(b)?;
                t.end()
            }
            Shape::Rect { w, h } => {
                let mut t = s.serialize_struct_variant("Shape", 3, "Rect", 2)?;
                t.serialize_field("w", w)?;
                t.serialize_field("h", h)?;
                t.end()
            }
        }
    }
}
struct Shown(u32);
impl Serialize for Shown {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(&format_args!("<{}>", self.0))
    }
}
struct Fails;
impl Serialize for Fails {
    fn serialize<S: Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
        Err(ser::Error::custom(format_args!("cannot serialize {}", "Fails")))
    }
}

fn show<T: ?Sized + Serialize>(v: &T) {
    match v.serialize(Text) {
        Ok(s) => println!("{}", s),
        Err(e) => println!("error: {}", e),
    }
}

fn main() {
    show(&true);
    show(&-5i8);
    show(&300i16);
    show(&-70000i32);
    show(&(1i64 << 40));
    show(&-(1i128 << 100));
    show(&255u8);
    show(&65535u16);
    show(&4000000000u32);
    show(&u64::MAX);
    show(&u128::MAX);
    show(&1.5f32);
    show(&-0.0f64);
    show(&f64::NAN);
    show(&'x');
    show("quote\"d");
    show(&String::from("owned"));
    show(&Some(3u8));
    show(&None::<u8>);
    show(&());
    show(&(1u8,));
    show(&(1u8, "two", 3.0f64));
    show(&vec![1u16, 2, 3]);
    show(&[7u8; 0]);
    show(&[1i32, 2, 3]);
    show(&&[4u8, 5][..]);
    show(&VecDeque::from(vec![9u8, 8]));
    show(&BTreeSet::from([3u8, 1, 2]));
    let mut hs = HashSet::new();
    hs.insert(5u8);
    show(&hs);
    let mut bm = BTreeMap::new();
    bm.insert("b", 2u8);
    bm.insert("a", 1u8);
    show(&bm);
    let mut hm = HashMap::new();
    hm.insert(1u8, vec!['a']);
    show(&hm);
    show(&Box::new(42u32));
    show(&Cell::new(6u8));
    show(&RefCell::new(String::from("cell")));
    show(&std::sync::Mutex::new(1u8));
    show(&std::time::Duration::new(3, 500));
    show(&(std::time::UNIX_EPOCH + std::time::Duration::new(7, 9)));
    show(std::ffi::OsStr::new("os"));
    show(&std::ffi::OsString::from("owned os"));
    show(&std::path::Path::new("rel/p"));
    show(&std::ops::Bound::Included(3u8));
    show(&std::ops::Bound::<u8>::Unbounded);
    show(&std::sync::atomic::AtomicU8::new(9));
    show(&std::sync::atomic::AtomicBool::new(true));
    show(&std::sync::RwLock::new('r'));
    show(&std::path::PathBuf::from("/tmp/x"));
    let ip: std::net::IpAddr = "192.168.0.1".parse().unwrap();
    show(&ip);
    let v6: std::net::Ipv6Addr = "::1".parse().unwrap();
    show(&v6);
    let sock: std::net::SocketAddr = "10.0.0.1:80".parse().unwrap();
    show(&sock);
    show(&Ok::<u8, String>(1));
    show(&Err::<u8, String>("bad".to_string()));
    show(&std::cmp::Reverse(4u8));
    show(&std::marker::PhantomData::<String>);
    show(&Point { x: 1, y: -2 });
    show(&[Shape::Dot, Shape::Circle(3), Shape::Line(-1, 1), Shape::Rect { w: 2, h: 3 }]);
    show(&Shown(12));
    show(&vec![Some(Point { x: 0, y: 0 }), None]);
    show(&Fails);
    show(&vec![Fails]);
    let s = Text.collect_seq(vec![1u8, 2].iter().map(|x| x * 10)).unwrap();
    println!("{}", s);
    let m = Text.collect_map(vec![("k", 1u8)]).unwrap();
    println!("{}", m);
    println!("{}", Text.is_human_readable());
}
