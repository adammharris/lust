// Adapter: anyhow 1.0.104 (docs/ARCH.md section 3.6; README.md here).
//
// Upstream keeps the error behind a hand-built vtable (`ErrorImpl`,
// `ptr.rs`) so `Error` is one pointer wide and can downcast. Lust has
// no `unsafe`, so the error here is a `Box<dyn StdError + Send + Sync>`
// of the same wrapper values upstream builds (`MessageError`,
// `DisplayError`, `ContextError`, `BoxedError`, or the user's error),
// and every text `Display`, `Debug`, `{:#}` and `{:#?}` print is
// upstream's. Downcasting and backtraces are not here (README.md).

mod chain;
mod context;
mod error;
mod escape;

pub use crate::chain::Chain;
pub use crate::context::Context;
pub use crate::error::Error;

/// `Result<T, Error>`, with the error type open as upstream has it.
pub type Result<T, E = Error> = core::result::Result<T, E>;

/// `Ok(value)` with the error type fixed to `Error`.
#[allow(non_snake_case)]
pub fn Ok<T>(value: T) -> Result<T> {
    Result::Ok(value)
}

/// Builds an `Error` from a format string, or from an error or
/// message value.
#[macro_export]
macro_rules! anyhow {
    ($msg:literal $(,)?) => {
        $crate::Error::msg(::std::format!($msg))
    };
    ($err:expr $(,)?) => {{
        use $crate::__private::kind::*;
        let error = match $err {
            error => (&error).anyhow_kind().new(error),
        };
        error
    }};
    ($fmt:expr, $($arg:tt)*) => {
        $crate::Error::msg(::std::format!($fmt, $($arg)*))
    };
}

/// Returns early with an error: `return Err(anyhow!(...))`.
#[macro_export]
macro_rules! bail {
    ($msg:literal $(,)?) => {
        return $crate::__private::Err($crate::anyhow!($msg))
    };
    ($err:expr $(,)?) => {
        return $crate::__private::Err($crate::anyhow!($err))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return $crate::__private::Err($crate::anyhow!($fmt, $($arg)*))
    };
}

/// Returns early with an error if a condition is false. The form with
/// no message is not in the adapter (README.md).
#[macro_export]
macro_rules! ensure {
    ($cond:expr, $msg:literal $(,)?) => {
        if !$cond {
            return $crate::__private::Err($crate::anyhow!($msg));
        }
    };
    ($cond:expr, $err:expr $(,)?) => {
        if !$cond {
            return $crate::__private::Err($crate::anyhow!($err));
        }
    };
    ($cond:expr, $fmt:expr, $($arg:tt)*) => {
        if !$cond {
            return $crate::__private::Err($crate::anyhow!($fmt, $($arg)*));
        }
    };
}

/// Upstream's `format_err!`: another name for `anyhow!`.
#[macro_export]
macro_rules! format_err {
    ($($tt:tt)*) => {
        $crate::anyhow!($($tt)*)
    };
}

// Not public API: what the macros expand to.
#[doc(hidden)]
pub mod __private {
    pub use core::result::Result::Err;

    // Upstream's autoref dispatch for `anyhow!($err)`: a value that is
    // `Into<Error>` (a std error, or an `Error`) converts, a boxed std
    // error keeps its chain, and any other `Display + Debug` value is
    // a message.
    pub mod kind {
        use crate::Error;
        use core::fmt::{Debug, Display};
        use std::error::Error as StdError;

        pub struct Adhoc;

        pub trait AdhocKind: Sized {
            fn anyhow_kind(&self) -> Adhoc {
                Adhoc
            }
        }

        impl<T> AdhocKind for &T where T: ?Sized + Display + Debug + Send + Sync + 'static {}

        impl Adhoc {
            pub fn new<M>(self, message: M) -> Error
            where
                M: Display + Debug + Send + Sync + 'static,
            {
                Error::msg(message)
            }
        }

        pub struct Trait;

        pub trait TraitKind: Sized {
            fn anyhow_kind(&self) -> Trait {
                Trait
            }
        }

        impl<E> TraitKind for E where E: Into<Error> {}

        impl Trait {
            pub fn new<E>(self, error: E) -> Error
            where
                E: Into<Error>,
            {
                error.into()
            }
        }

        pub struct Boxed;

        pub trait BoxedKind: Sized {
            fn anyhow_kind(&self) -> Boxed {
                Boxed
            }
        }

        impl BoxedKind for Box<dyn StdError + Send + Sync> {}

        impl Boxed {
            pub fn new(self, error: Box<dyn StdError + Send + Sync>) -> Error {
                Error::from_boxed(error)
            }
        }
    }
}
