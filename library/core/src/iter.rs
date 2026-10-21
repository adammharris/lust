// `core::iter` overlay (docs/ARCH.md section 3.1; W-STD-C): the sources
// `once`, `once_with`, `from_fn`, `successors`, `repeat` and their iterator
// types. The other `core::iter` items (`empty`, `zip`, the adapters, the
// iterator traits) stay compiler-known; `std::iter::X` and `core::iter::X`
// walk into this module only for the names it defines (`STD_MODULES` in
// src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `core/src/iter/sources/{once,once_with,from_fn,successors,repeat}.rs`. Not
// here: `FusedIterator` and `TrustedLen` (lust has no such traits, so a
// bound on them rejects; lowering knows which of these types std marks
// `TrustedLen`, src/lower/iter.rs `std_trusted_len`). `Once<T>` holds
// `Option<T>` where core holds an `option::IntoIter<T>`; its Debug text
// writes core's nesting by hand
// (`Once { inner: IntoIter { inner: Item { opt: Some(1) } } }`).

/// Creates an iterator that yields an element exactly once.
pub fn once<T>(value: T) -> Once<T> {
    Once { inner: Some(value) }
}

/// An iterator that yields an element exactly once (`once`).
#[derive(Clone)]
pub struct Once<T> {
    inner: Option<T>,
}

/// Debug of core's `option::Item { opt }` inside `option::IntoIter`.
struct OptionItemDebug<'a, T>(&'a Option<T>);

impl<T: core::fmt::Debug> core::fmt::Debug for OptionItemDebug<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Item").field("opt", self.0).finish()
    }
}

/// Debug of core's `option::IntoIter { inner }`.
struct OptionIntoIterDebug<'a, T>(&'a Option<T>);

impl<T: core::fmt::Debug> core::fmt::Debug for OptionIntoIterDebug<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IntoIter").field("inner", &OptionItemDebug(self.0)).finish()
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Once<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Once").field("inner", &OptionIntoIterDebug(&self.inner)).finish()
    }
}

impl<T> Iterator for Once<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.take()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = if self.inner.is_some() { 1 } else { 0 };
        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for Once<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for Once<T> {
    fn len(&self) -> usize {
        if self.inner.is_some() { 1 } else { 0 }
    }
}

/// Creates an iterator that lazily makes a value exactly once by
/// calling the closure.
pub fn once_with<A, F: FnOnce() -> A>(make: F) -> OnceWith<F> {
    OnceWith { make: Some(make) }
}

/// An iterator that yields one element of type `A` by calling the
/// closure `F: FnOnce() -> A` (`once_with`).
#[derive(Clone)]
pub struct OnceWith<F> {
    make: Option<F>,
}

impl<F> core::fmt::Debug for OnceWith<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.make.is_some() { f.write_str("OnceWith(Some(_))") } else { f.write_str("OnceWith(None)") }
    }
}

impl<A, F: FnOnce() -> A> Iterator for OnceWith<F> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        let f = self.make.take()?;
        Some(f())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = if self.make.is_some() { 1 } else { 0 };
        (len, Some(len))
    }
}

impl<A, F: FnOnce() -> A> DoubleEndedIterator for OnceWith<F> {
    fn next_back(&mut self) -> Option<A> {
        self.next()
    }
}

impl<A, F: FnOnce() -> A> ExactSizeIterator for OnceWith<F> {
    fn len(&self) -> usize {
        if self.make.is_some() { 1 } else { 0 }
    }
}

/// Creates an iterator where each iteration calls the closure
/// `F: FnMut() -> Option<T>`.
pub fn from_fn<T, F>(f: F) -> FromFn<F>
where
    F: FnMut() -> Option<T>,
{
    FromFn(f)
}

/// An iterator where each iteration calls the closure (`from_fn`).
#[derive(Clone)]
pub struct FromFn<F>(F);

impl<T, F> Iterator for FromFn<F>
where
    F: FnMut() -> Option<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        (self.0)()
    }
}

impl<F> core::fmt::Debug for FromFn<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FromFn").finish()
    }
}

/// Creates an iterator where each item is computed from the one before
/// it, starting at `first`.
pub fn successors<T, F>(first: Option<T>, succ: F) -> Successors<T, F>
where
    F: FnMut(&T) -> Option<T>,
{
    Successors { next: first, succ }
}

/// An iterator where each item is computed from the one before it
/// (`successors`).
#[derive(Clone)]
pub struct Successors<T, F> {
    next: Option<T>,
    succ: F,
}

impl<T, F> Iterator for Successors<T, F>
where
    F: FnMut(&T) -> Option<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.next.take()?;
        self.next = (self.succ)(&item);
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.next.is_some() { (1, None) } else { (0, Some(0)) }
    }
}

impl<T: core::fmt::Debug, F> core::fmt::Debug for Successors<T, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Successors").field("next", &self.next).finish()
    }
}

/// Creates an iterator that endlessly repeats a single element.
pub fn repeat<T: Clone>(elt: T) -> Repeat<T> {
    Repeat { element: elt }
}

/// An iterator that repeats an element endlessly (`repeat`).
#[derive(Clone, Debug)]
pub struct Repeat<A> {
    element: A,
}

impl<A: Clone> Iterator for Repeat<A> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        Some(self.element.clone())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

impl<A: Clone> DoubleEndedIterator for Repeat<A> {
    fn next_back(&mut self) -> Option<A> {
        Some(self.element.clone())
    }
}
