// fs::copy: the byte count, the source's permissions on the copy, a copy
// over an existing file, std's error for a directory source, and a copy
// onto itself, which std's truncating open empties.
use std::os::unix::fs::PermissionsExt;
fn main() {
    let dir = std::env::temp_dir().join(format!("fs_copy_probe_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let a = dir.join("a.txt");
    std::fs::write(&a, b"hello copy").unwrap();
    std::fs::set_permissions(&a, std::fs::Permissions::from_mode(0o640)).unwrap();
    let b = dir.join("b.txt");
    println!("{}", std::fs::copy(&a, &b).unwrap());
    println!("{:?}", std::fs::read_to_string(&b).unwrap());
    println!("{:o}", std::fs::metadata(&b).unwrap().permissions().mode() & 0o777);
    std::fs::write(&a, b"hi").unwrap();
    println!("{} {:?}", std::fs::copy(&a, &b).unwrap(), std::fs::read(&b).unwrap());
    match std::fs::copy(&dir, dir.join("c")) {
        Ok(n) => println!("ok? {n}"),
        Err(e) => println!("{:?} {}", e.kind(), e),
    }
    match std::fs::copy(dir.join("missing"), dir.join("d")) {
        Ok(n) => println!("ok? {n}"),
        Err(e) => println!("{:?}", e.kind()),
    }
    println!("{} {}", std::fs::copy(&b, &b).unwrap(), std::fs::read(&b).unwrap().len());
    std::fs::remove_dir_all(&dir).unwrap();
}
