// A module file with its own tests module.
use kit::bytes::is_digit;

pub fn digits(s: &str) -> usize {
    s.bytes().filter(is_digit).count()
}

#[cfg(test)]
mod tests {
    #[test]
    fn counts_digits() {
        assert_eq!(super::digits("a1b22"), 3);
    }

    #[test]
    fn fails_on_purpose() {
        assert_eq!(super::digits("123"), 4, "a failing test fails in both");
    }
}
