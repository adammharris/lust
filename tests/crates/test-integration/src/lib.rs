pub fn greet(name: &str) -> String {
    format!("hello, {name}")
}

// The lib's own unit tests are not part of an integration test build.
#[cfg(test)]
mod tests {
    #[test]
    fn unit_only() {
        panic!("not in the integration test");
    }
}
