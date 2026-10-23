// `PathBuf`/`OsString` as map and set keys looked up by `&Path`/`&OsStr`
// (`Borrow`), and `Path`'s hash: std's, so equal paths (`a/./b`,
// `a//b/`) hash equal and the values match rustc's.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

fn main() {
    let mut set: HashSet<PathBuf> = HashSet::new();
    set.insert(PathBuf::from("/a/b"));
    let p: &Path = Path::new("/a/b");
    println!("{}", set.contains(p));
    let mut map: HashMap<PathBuf, u32> = HashMap::new();
    map.insert(PathBuf::from("x"), 7);
    println!("{}", map.contains_key(Path::new("x")));
    println!("{}", map[Path::new("x")]);
    println!("{:?}", map.get(Path::new("y")));
    let mut bt: BTreeMap<PathBuf, u32> = BTreeMap::new();
    bt.insert(PathBuf::from("k"), 1);
    println!("{:?}", bt.get(Path::new("k")));
    use std::borrow::Borrow;
    let pb = PathBuf::from("z");
    let r: &Path = pb.borrow();
    println!("{}", r.display());
    hashes();
}

fn h<T: std::hash::Hash + ?Sized>(t: &T) -> u64 {
    use std::hash::{DefaultHasher, Hasher};
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

#[allow(dead_code)]
fn hashes() {
    for p in ["", "/", "a/b", "a/./b", "a//b/", "./a", "/a/.", "foo/bar", "foobar", "a/../b"] {
        println!("{p:?} {}", h(Path::new(p)));
        assert_eq!(h(Path::new(p)), h(&PathBuf::from(p)));
    }
    println!("{}", h(std::ffi::OsStr::new("xy")));
    println!("{}", h(&std::ffi::OsString::from("xy")));
    let mut set: HashSet<std::ffi::OsString> = HashSet::new();
    set.insert("q".into());
    println!("{}", set.contains(std::ffi::OsStr::new("q")));
}
