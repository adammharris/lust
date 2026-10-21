// Depends back on the package and re-exports one of its modules, as
// twig-doc does with twig-kit: the lib it sees is the plain lib, with
// none of the integration test's dev-dependencies.
pub use test_integration::names;
pub use names::Name;

pub mod api {
    use crate::names::Name;

    pub fn shout(n: &Name) -> String {
        n.0.to_uppercase()
    }
}
