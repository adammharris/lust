// `Context` (upstream context.rs).

use crate::Error;
use crate::error::ContextError;
use core::fmt::Display;
use std::error::Error as StdError;

/// `context` and `with_context` on `Result` and `Option`.
pub trait Context<T, E>: private::Sealed {
    /// Wraps the error value with additional context.
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static;

    /// Wraps the error value with context that is built only when an
    /// error occurs.
    fn with_context<C, F>(self, f: F) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
        F: FnOnce() -> C;
}

pub(crate) mod private {
    use super::*;

    /// The errors `Context` takes: std errors and `Error` itself.
    pub trait StdErrorExt {
        fn ext_context<C>(self, context: C) -> Error
        where
            C: Display + Send + Sync + 'static;
    }

    impl<E> StdErrorExt for E
    where
        E: StdError + Send + Sync + 'static,
    {
        fn ext_context<C>(self, context: C) -> Error
        where
            C: Display + Send + Sync + 'static,
        {
            Error { inner: Box::new(ContextError { context, error: self }) }
        }
    }

    impl StdErrorExt for Error {
        fn ext_context<C>(self, context: C) -> Error
        where
            C: Display + Send + Sync + 'static,
        {
            self.context(context)
        }
    }

    pub trait Sealed {}

    impl<T, E> Sealed for Result<T, E> where E: StdErrorExt {}
    impl<T> Sealed for Option<T> {}
}

impl<T, E> Context<T, E> for Result<T, E>
where
    E: private::StdErrorExt + Send + Sync + 'static,
{
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
    {
        match self {
            Ok(ok) => Ok(ok),
            Err(error) => Err(error.ext_context(context)),
        }
    }

    fn with_context<C, F>(self, context: F) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
        F: FnOnce() -> C,
    {
        match self {
            Ok(ok) => Ok(ok),
            Err(error) => Err(error.ext_context(context())),
        }
    }
}

impl<T> Context<T, core::convert::Infallible> for Option<T> {
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
    {
        match self {
            Some(ok) => Ok(ok),
            None => Err(Error::from_display(context)),
        }
    }

    fn with_context<C, F>(self, context: F) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
        F: FnOnce() -> C,
    {
        match self {
            Some(ok) => Ok(ok),
            None => Err(Error::from_display(context())),
        }
    }
}

