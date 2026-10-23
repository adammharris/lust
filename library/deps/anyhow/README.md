# Adapter: anyhow 1.0.104

Lust adapter crate (docs/ARCH.md section 3.6) with upstream's public
shape: `Error`, `Result`, `Chain`, `Context`, `Ok`, and the `anyhow!`,
`bail!`, `ensure!`, and `format_err!` macros. Gate:
`scripts/test-adapters.sh anyhow`.

Upstream keeps the error behind a hand-built vtable (`ErrorImpl`,
ptr.rs) so `Error` is one pointer wide and can downcast. Lust has no
`unsafe`, so here `Error` holds a `Box<dyn StdError + Send + Sync>` of
the same values upstream builds: `MessageError`, `DisplayError`,
`ContextError<C, E>`, `BoxedError`, or the user's own error.

## Implemented, same results as upstream

- `Error::new`, `msg`, `from_boxed`, `context`, `chain`, `root_cause`,
  `into_boxed_dyn_error`; `From<E: std::error::Error>`; `Deref` and
  `DerefMut` to `dyn StdError + Send + Sync`; `AsRef` to `dyn StdError`
  (with and without `Send + Sync`); `From<Error>` for the three boxed
  `dyn StdError` forms.
- The texts: `{}` (the outermost error), `{:#}` (the chain joined by
  `": "`), `{:?}` (the outermost error, then `Caused by:` with numbered
  or unnumbered, indented causes), `{:#?}` (the struct form, the context
  quoted with `str::escape_debug`, which escape.rs writes from char
  Debug and a table of printable grapheme extenders probed from rustc
  1.99), and `main` returning `anyhow::Result` (`Error: ` and the Debug
  form on stderr, exit status 1; checked by hand: the corpus runner
  compares stdout and needs status 0).
- `Context::context` and `with_context` on `Result<T, E>` for std errors
  and for `Error`, and on `Option<T>`.
- `Chain` as `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator`,
  `Clone`, `Default`. Upstream buffers the chain in a Vec on the first
  `next_back`; here it stays linked and counts what the back took (the
  same items in the same order).
- The macro forms: a literal (with inline captures), a format string
  with arguments, and one expression, which goes through upstream's
  autoref dispatch (`__private::kind`): a std error or `Error` converts,
  a `Box<dyn StdError + Send + Sync>` keeps its chain, any other
  `Display + Debug` value is a message.

## Rejected (lust error, never a different answer)

- The `backtrace` feature, `Error::backtrace`, and the downcasts (`is`,
  `downcast`, `downcast_ref`, `downcast_mut`): lust's `dyn` has no type
  id. Calls are L0104.
- `ensure!(cond)` with no message: upstream's message prints the
  condition's operands with Debug, which this adapter does not rebuild.
  The call matches no rule (L0806).
