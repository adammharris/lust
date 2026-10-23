// `Chain` (upstream chain.rs). Upstream buffers the rest of the chain
// in a Vec on the first `next_back`; here the chain stays linked and
// counts what the back has taken, so `next_back` walks from the front.
// Same items in the same order either way; chains are short.

use std::error::Error as StdError;

/// The causes of an error, from the error down to its root cause.
#[derive(Clone)]
pub struct Chain<'a> {
    next: Option<&'a (dyn StdError + 'static)>,
    back_taken: usize,
}

impl<'a> Chain<'a> {
    /// The chain that starts at `head`.
    pub fn new(head: &'a (dyn StdError + 'static)) -> Self {
        Chain { next: Some(head), back_taken: 0 }
    }
}

impl<'a> Iterator for Chain<'a> {
    type Item = &'a (dyn StdError + 'static);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len() == 0 {
            return None;
        }
        let error = self.next?;
        self.next = error.source();
        Some(error)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl DoubleEndedIterator for Chain<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let len = self.len();
        if len == 0 {
            return None;
        }
        let mut cause = self.next?;
        for _ in 1..len {
            cause = cause.source()?;
        }
        self.back_taken += 1;
        Some(cause)
    }
}

impl ExactSizeIterator for Chain<'_> {
    fn len(&self) -> usize {
        let mut len = 0;
        let mut next = self.next;
        while let Some(cause) = next {
            next = cause.source();
            len += 1;
        }
        len - self.back_taken
    }
}

impl Default for Chain<'_> {
    fn default() -> Self {
        Chain { next: None, back_taken: 0 }
    }
}
