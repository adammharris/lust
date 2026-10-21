pub fn quadruple(x: u32) -> u32 {
    test_lib_modules::double(test_lib_modules::double(x))
}

// A dependency builds without `cfg(test)`, also under `cargo test` of
// another crate: this module must not compile there (its file is missing).
#[cfg(test)]
mod tests {
    const DATA: &[u8] = include_bytes!("../no-such-file.bin");

    #[test]
    fn data() {
        assert!(!DATA.is_empty());
    }
}
