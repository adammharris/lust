use std::sync::Mutex;

/// A process-wide registry, as twig-doc keeps its languages.
pub static REGISTRY: Mutex<Vec<&'static str>> = Mutex::new(Vec::new());

pub fn register(name: &'static str) {
    REGISTRY.lock().unwrap().push(name);
}

pub fn registered(name: &str) -> bool {
    REGISTRY.lock().unwrap().iter().any(|n| *n == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_registers_markdown() {
        register("markdown");
    }

    // Runs after `a_registers_markdown` (tests run sorted by name, one at a
    // time under `--test-threads 1`) in the same process, so it passes.
    #[test]
    fn b_sees_the_registration() {
        assert!(registered("markdown"));
    }

    #[test]
    fn c_thread_is_named_by_the_test() {
        assert_eq!(std::thread::current().name(), Some("tests::c_thread_is_named_by_the_test"));
    }

    #[test]
    fn d_a_panic_fails_only_its_test() {
        panic!("only this test fails");
    }

    #[test]
    fn e_the_next_test_still_runs() {
        assert!(registered("markdown"));
    }

    #[test]
    #[should_panic(expected = "boom")]
    fn f_panics_with_the_text() {
        panic!("a boom here");
    }

    #[test]
    #[should_panic(expected = "zzz")]
    fn g_panics_with_other_text() {
        panic!("boom");
    }

    #[test]
    #[should_panic]
    fn h_does_not_panic() {}

    #[test]
    fn i_returns_err() -> Result<(), String> {
        Err("no".into())
    }

    #[test]
    fn j_returns_ok() -> Result<(), String> {
        Ok(())
    }

    #[test]
    #[ignore]
    fn k_ignored() {
        panic!("never runs");
    }

    #[test]
    #[should_panic(expected = "x")]
    fn l_non_string_payload() {
        std::panic::panic_any(5u8);
    }
}
