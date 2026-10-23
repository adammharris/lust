// `Error` and the values it holds (upstream error.rs, fmt.rs,
// wrapper.rs, and the context error of context.rs).

use crate::Chain;
use core::fmt::{self, Debug, Display, Write};
use std::error::Error as StdError;

/// A dynamic error with an optional chain of causes.
pub struct Error {
    pub(crate) inner: Box<dyn StdError + Send + Sync + 'static>,
}

impl Error {
    /// An error from a value of a type that implements `std::error::Error`.
    pub fn new<E>(error: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        Error { inner: Box::new(error) }
    }

    /// An error from a message: its `Display` is the error's text,
    /// its `Debug` the `{:#?}` form.
    pub fn msg<M>(message: M) -> Self
    where
        M: Display + Debug + Send + Sync + 'static,
    {
        Error { inner: Box::new(MessageError(message)) }
    }

    /// An error from a boxed `std::error::Error` value.
    pub fn from_boxed(boxed_error: Box<dyn StdError + Send + Sync + 'static>) -> Self {
        Error { inner: Box::new(BoxedError(boxed_error)) }
    }

    pub(crate) fn from_display<M>(message: M) -> Self
    where
        M: Display + Send + Sync + 'static,
    {
        Error { inner: Box::new(DisplayError(message)) }
    }

    /// Wraps the error in a higher-level context: the context prints
    /// first, and this error becomes its source.
    pub fn context<C>(self, context: C) -> Self
    where
        C: Display + Send + Sync + 'static,
    {
        Error { inner: Box::new(ContextError { context, error: self }) }
    }

    /// The error, then its source, then the source's source, and so on.
    pub fn chain(&self) -> Chain<'_> {
        Chain::new(&*self.inner)
    }

    /// The last error of `chain()`: the lowest-level cause.
    pub fn root_cause(&self) -> &(dyn StdError + 'static) {
        self.chain().last().unwrap()
    }

    /// The error as a boxed `std::error::Error` whose `Display` and
    /// `Debug` are this error's.
    pub fn into_boxed_dyn_error(self) -> Box<dyn StdError + Send + Sync + 'static> {
        Box::new(ErrorBox(self))
    }
}

impl<E> From<E> for Error
where
    E: StdError + Send + Sync + 'static,
{
    fn from(error: E) -> Self {
        Error::new(error)
    }
}

impl core::ops::Deref for Error {
    type Target = dyn StdError + Send + Sync + 'static;

    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl core::ops::DerefMut for Error {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.inner
    }
}

impl AsRef<dyn StdError + Send + Sync> for Error {
    fn as_ref(&self) -> &(dyn StdError + Send + Sync + 'static) {
        &*self.inner
    }
}

impl AsRef<dyn StdError> for Error {
    fn as_ref(&self) -> &(dyn StdError + 'static) {
        &*self.inner
    }
}

impl From<Error> for Box<dyn StdError + Send + Sync + 'static> {
    fn from(error: Error) -> Self {
        error.into_boxed_dyn_error()
    }
}

impl From<Error> for Box<dyn StdError + Send + 'static> {
    fn from(error: Error) -> Self {
        Box::new(ErrorBox(error))
    }
}

impl From<Error> for Box<dyn StdError + 'static> {
    fn from(error: Error) -> Self {
        Box::new(ErrorBox(error))
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)?;
        if f.alternate() {
            for cause in self.chain().skip(1) {
                write!(f, ": {}", cause)?;
            }
        }
        Ok(())
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error = &*self.inner;
        if f.alternate() {
            return Debug::fmt(error, f);
        }
        write!(f, "{}", error)?;
        if let Some(cause) = error.source() {
            write!(f, "\n\nCaused by:")?;
            let multiple = cause.source().is_some();
            for (n, error) in Chain::new(cause).enumerate() {
                writeln!(f)?;
                let mut indented = Indented { inner: f, number: if multiple { Some(n) } else { None }, started: false };
                write!(indented, "{}", error)?;
            }
        }
        Ok(())
    }
}

/// The writer of one numbered cause in `Debug`: every line after the
/// first is indented under the first.
struct Indented<'a, D> {
    inner: &'a mut D,
    number: Option<usize>,
    started: bool,
}

impl<T> Write for Indented<'_, T>
where
    T: Write,
{
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for (i, line) in s.split('\n').enumerate() {
            if !self.started {
                self.started = true;
                match self.number {
                    Some(number) => write!(self.inner, "{: >5}: ", number)?,
                    None => self.inner.write_str("    ")?,
                }
            } else if i > 0 {
                self.inner.write_char('\n')?;
                if self.number.is_some() {
                    self.inner.write_str("       ")?;
                } else {
                    self.inner.write_str("    ")?;
                }
            }
            self.inner.write_str(line)?;
        }
        Ok(())
    }
}

// The values an `Error` holds, as upstream's wrapper.rs and context.rs
// define them.

struct MessageError<M>(M);

impl<M: Display + Debug> Debug for MessageError<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<M: Display + Debug> Display for MessageError<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<M: Display + Debug + 'static> StdError for MessageError<M> {}

struct DisplayError<M>(M);

impl<M: Display> Debug for DisplayError<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<M: Display> Display for DisplayError<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<M: Display + 'static> StdError for DisplayError<M> {}

struct BoxedError(Box<dyn StdError + Send + Sync>);

impl Debug for BoxedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Display for BoxedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl StdError for BoxedError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.source()
    }
}

pub(crate) struct ContextError<C, E> {
    pub(crate) context: C,
    pub(crate) error: E,
}

impl<C: Display, E: Debug> Debug for ContextError<C, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error").field("context", &Quoted(&self.context)).field("source", &self.error).finish()
    }
}

impl<C: Display, E> Display for ContextError<C, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.context, f)
    }
}

impl<C: Display, E: StdError + 'static> StdError for ContextError<C, E> {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&self.error)
    }
}

impl<C: Display> StdError for ContextError<C, Error> {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&*self.error.inner)
    }
}

/// The context in `{:#?}`: its `Display` text, quoted and escaped.
struct Quoted<C>(C);

impl<C: Display> Debug for Quoted<C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_char('"')?;
        Quoted(&mut *formatter).write_fmt(format_args!("{}", self.0))?;
        formatter.write_char('"')?;
        Ok(())
    }
}

impl Write for Quoted<&mut fmt::Formatter<'_>> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        crate::escape::write_escape_debug(self.0, s)
    }
}

/// An `Error` as a `std::error::Error` (upstream's `ErrorImpl` behind
/// `into_boxed_dyn_error`): the error's own texts, the source of the
/// error it holds.
struct ErrorBox(Error);

impl Debug for ErrorBox {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Display for ErrorBox {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl StdError for ErrorBox {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.inner.source()
    }
}

