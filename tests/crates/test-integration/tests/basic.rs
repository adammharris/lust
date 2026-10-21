mod common;

#[test]
fn greets() {
    assert_eq!(test_integration::greet(common::NAME), "hello, lust");
}

#[test]
fn runs_in_the_package_dir() {
    // cargo test runs a test in its package dir, with CARGO_MANIFEST_DIR set.
    assert!(std::path::Path::new("tests/basic.rs").is_file());
    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    assert_eq!(std::path::Path::new(&dir).join("Cargo.toml").is_file(), true);
}

#[test]
fn through_a_dev_dependency() {
    let n: test_integration::names::Name = wrap::Name("lust".into());
    assert_eq!(wrap::api::shout(&n), "LUST");
}

mod more {
    #[test]
    fn nested() {
        assert_eq!(super::common::twice(21), 42);
    }
}
