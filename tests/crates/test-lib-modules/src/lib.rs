mod parse;

pub fn double(x: u32) -> u32 {
    x * 2
}

pub fn words(s: &str) -> Vec<&str> {
    s.split_whitespace().collect()
}

#[test]
fn root_test() {
    assert_eq!(double(4), 8);
}

#[test]
#[should_panic(expected = "too big")]
fn root_panics() {
    if double(100) > 10 {
        panic!("too big: {}", double(100));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_test() {
        assert_eq!(words("a b  c"), ["a", "b", "c"]);
    }

    #[test]
    #[ignore]
    fn ignored() {
        panic!("never runs");
    }

    #[test]
    fn returns_ok() -> Result<(), String> {
        if double(1) == 2 { Ok(()) } else { Err("bad".into()) }
    }

    #[test]
    fn returns_err() -> Result<(), String> {
        Err(format!("double(3) is {}", double(3)))
    }

    #[test]
    #[cfg(feature = "extra")]
    fn only_with_extra() {
        panic!("configured out");
    }

    mod nested {
        #[test]
        fn deep() {
            assert_eq!(super::super::double(0), 0);
        }
    }

    #[test]
    fn uses_dev_dependency() {
        assert_eq!(helper::quadruple(3), 12);
    }
}
