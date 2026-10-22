// `std::sync` overlay (docs/ARCH.md section 3.1; W-STD-C): `LazyLock`, `Once`.
// `OnceLock`, `Arc`, `Mutex`, and the other `sync` items stay compiler-
// known (W-THREADS, thread-safe); `std::sync::X` walks into this module
// only for the names it defines (`STD_MODULES` in src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `std/src/sync/lazy_lock.rs`. The value lives in W-THREADS's
// `OnceLock<T>`, so first access is thread-safe: `get_or_init` runs the
// init closure exactly once, and only that closure takes `F` out of
// `init` (through the privileged `core::intrinsics::once_take`), so the
// take never races. `LazyLock: Sync` follows std's impl (`T: Send + Sync`,
// `F: Send`), given by `auto_structural` in src/check/collect.rs; `Send`
// is structural, as in std.

/// Debug text of an empty lock: `<uninit>`.
struct Uninit;

impl core::fmt::Debug for Uninit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("<uninit>")
    }
}

/// A value initialized on first access by `F`.
pub struct LazyLock<T, F = fn() -> T> {
    once: std::sync::OnceLock<T>,
    init: Option<F>,
}

impl<T, F: FnOnce() -> T> LazyLock<T, F> {
    pub const fn new(f: F) -> LazyLock<T, F> {
        LazyLock { once: std::sync::OnceLock::new(), init: Some(f) }
    }

    pub fn force(this: &LazyLock<T, F>) -> &T {
        this.once.get_or_init(|| match core::intrinsics::once_take(&this.init) {
            Some(f) => f(),
            None => panic!("LazyLock instance has previously been poisoned"), //@ std/src/sync/lazy_lock.rs:415:5
        })
    }

    pub fn force_mut(this: &mut LazyLock<T, F>) -> &mut T {
        LazyLock::force(this);
        match this.once.get_mut() {
            Some(v) => v,
            None => unreachable!(), //@ never
        }
    }

    pub fn get(this: &LazyLock<T, F>) -> Option<&T> {
        this.once.get()
    }

    pub fn get_mut(this: &mut LazyLock<T, F>) -> Option<&mut T> {
        this.once.get_mut()
    }
}

impl<T, F: FnOnce() -> T> core::ops::Deref for LazyLock<T, F> {
    type Target = T;
    fn deref(&self) -> &T {
        LazyLock::force(self)
    }
}

impl<T, F> From<T> for LazyLock<T, F> {
    fn from(value: T) -> LazyLock<T, F> {
        LazyLock { once: std::sync::OnceLock::from(value), init: None }
    }
}

impl<T: core::fmt::Debug, F> core::fmt::Debug for LazyLock<T, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_tuple("LazyLock");
        match self.once.get() {
            Some(v) => d.field(v),
            None => d.field(&Uninit),
        };
        d.finish()
    }
}

/// A one-time initialization guard, adapted from rust-lang/rust 1.99
/// `std/src/sync/once.rs`. The run happens inside W-THREADS's
/// `OnceLock<()>`, so a second caller blocks until the first run ends.
/// A run that panics leaves the lock empty and `poisoned` set: the next
/// `call_once` runs the closure below again, which panics as std's
/// poisoned `Once` does. (`call_once_force` and `OnceState` have no lust
/// form, so a program that names them does not compile.)
pub struct Once {
    done: std::sync::OnceLock<()>,
    poisoned: std::sync::atomic::AtomicBool,
}

impl Once {
    pub const fn new() -> Once {
        Once { done: std::sync::OnceLock::new(), poisoned: std::sync::atomic::AtomicBool::new(false) }
    }

    /// `#[track_caller]` as std's: a poisoned `Once` panics at the
    /// caller. The check inside the closure only runs when another thread
    /// poisons the `Once` while this call waits; that panic reports lust's
    /// line (a known gap: the closure cannot take the caller's location).
    #[track_caller]
    pub fn call_once<F: FnOnce()>(&self, f: F) {
        if self.done.get().is_none() && self.poisoned.load(std::sync::atomic::Ordering::Acquire) {
            panic!("Once instance has previously been poisoned");
        }
        self.done.get_or_init(|| {
            if self.poisoned.load(std::sync::atomic::Ordering::Acquire) {
                panic!("Once instance has previously been poisoned"); //@ gap
            }
            // Poisoned only when `f` unwinds: a caller that comes while
            // `f` runs waits in `get_or_init`, as std's `Once` waits.
            let mut guard = PoisonOnUnwind { poisoned: &self.poisoned, done: false };
            f();
            guard.done = true;
        });
    }

    pub fn is_completed(&self) -> bool {
        self.done.get().is_some()
    }
}

/// Sets a `Once`'s poison flag when its run ends without finishing (`f`
/// panicked and this drops in the unwind).
struct PoisonOnUnwind<'a> {
    poisoned: &'a std::sync::atomic::AtomicBool,
    done: bool,
}

impl Drop for PoisonOnUnwind<'_> {
    fn drop(&mut self) {
        if !self.done {
            self.poisoned.store(true, std::sync::atomic::Ordering::Release);
        }
    }
}

impl core::fmt::Debug for Once {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Once").finish_non_exhaustive()
    }
}
