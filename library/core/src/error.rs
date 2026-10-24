// `core::error` (docs/ARCH.md section 3.1; W-STD-C phase 2): the
// `Error` trait. `std::error::Error` is this trait, as in std;
// `core::error::X` and `std::error::X` walk into this module
// (`STD_MODULES` in src/stdmods.rs).
//
// Adapted from rust-lang/rust 1.99 `core/src/error.rs` and the
// `Box<dyn Error>` conversions of `alloc::boxed` (F3: `dyn Error`
// rides the fmt header shims, check/object.rs). Not here: the
// unstable generic member access items (`Request`, `provide`),
// and the `dyn Error` downcast methods (`downcast_ref` and kin
// need a type id in the vtable, like `dyn Any` has).

/// The trait of error values: `Debug` and `Display`.
pub trait Error: core::fmt::Debug + core::fmt::Display {
    /// The error under this one, if any: the chain a report walks.
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }

    /// A short text form. Deprecated in std; `Display` is the
    /// current one. The default text is std's.
    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }

    /// The cause under this one. Deprecated in std; `source` is
    /// the current one.
    fn cause(&self) -> Option<&dyn Error> {
        self.source()
    }
}

// alloc's word error (`StringError` in `alloc::boxed`): what a
// `Box<dyn Error>` from a `&str`, `String`, or `Cow<str>` holds.
// Its `Display` and `Debug` are the string's own, as in std.
struct StringError(String);

impl core::fmt::Debug for StringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

// Std forwards the formatter (`Display::fmt(&**self, f)`), so a width
// pads the text: `f.pad` is `str`'s Display.
impl core::fmt::Display for StringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.0)
    }
}

impl Error for StringError {}

// std's pair is over every `'a`; a named-lifetime bound on a
// parameter is not in the subset yet (L0203), so these are the
// `'static` forms (a `Box<dyn Error + 'a>` build from a short
// lived error rejects, never miscompiles).
impl<E: Error + 'static> From<E> for Box<dyn Error> {
    fn from(error: E) -> Box<dyn Error> {
        Box::new(error)
    }
}

impl<E: Error + Send + Sync + 'static> From<E> for Box<dyn Error + Send + Sync> {
    fn from(error: E) -> Box<dyn Error + Send + Sync> {
        Box::new(error)
    }
}

impl From<&str> for Box<dyn Error + Send + Sync> {
    fn from(error: &str) -> Box<dyn Error + Send + Sync> {
        Box::new(StringError(String::from(error)))
    }
}

impl From<&str> for Box<dyn Error> {
    fn from(error: &str) -> Box<dyn Error> {
        Box::new(StringError(String::from(error)))
    }
}

impl From<String> for Box<dyn Error + Send + Sync> {
    fn from(error: String) -> Box<dyn Error + Send + Sync> {
        Box::new(StringError(error))
    }
}

impl From<String> for Box<dyn Error> {
    fn from(error: String) -> Box<dyn Error> {
        Box::new(StringError(error))
    }
}

impl From<std::borrow::Cow<'_, str>> for Box<dyn Error + Send + Sync> {
    fn from(error: std::borrow::Cow<'_, str>) -> Box<dyn Error + Send + Sync> {
        Box::new(StringError(String::from(error)))
    }
}

impl From<std::borrow::Cow<'_, str>> for Box<dyn Error> {
    fn from(error: std::borrow::Cow<'_, str>) -> Box<dyn Error> {
        Box::new(StringError(String::from(error)))
    }
}

// core's pointer impls: a reference to an error is an error.
impl<T: ?Sized + Error> Error for &T {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        (**self).source()
    }
}

impl<T: ?Sized + Error> Error for Box<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        (**self).source()
    }
}

// core's conversion errors (fx-tryfrom): `Error` with the default
// `description`, as in core.
impl Error for core::num::TryFromIntError {}
impl Error for core::char::CharTryFromError {}
impl Error for core::char::TryFromCharError {}
impl Error for core::convert::Infallible {}

// core's `Error` for `fmt::Error`.
impl Error for core::fmt::Error {}

// std's `Error` for `io::Error` (written in std::io in std; here so
// the trait path resolves in this splice): `source` is the boxed
// payload of a custom error, which lust does not take at
// `io::Error::new`, so it stays `None`, as in std for the forms
// lust accepts there (F3).
impl Error for std::io::Error {}
