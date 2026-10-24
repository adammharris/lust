// `core::marker` overlay (docs/ARCH.md section 3.1; W-STD-C):
// `PhantomData`. The other `core::marker` items (Send, Sync, Copy,
// Sized, Unpin) stay compiler-known; `std::marker::X` and
// `core::marker::X` walk into this module only for the names it
// defines (`STD_MODULES` in src/stdmods.rs).
//
// The compiler treats `PhantomData<T>` as holding a `T` for auto
// traits, unused-parameter checks, and regions, while its value is
// zero-sized (`Program::is_phantom_adt`).

/// A zero-sized type that acts as if it owns a `T`. Std's impls have no
/// bounds on `T`; the derives here give the same answers, because the
/// struct has no fields (lust derives on a generic Adt ask only the
/// fields).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhantomData<T: ?Sized>;

// Lust std source, adapted from rust-lang/rust 1.99 `core/src/marker.rs`
// (`impl Hash`): no bound on `T`, and it writes nothing. `Debug`
// (`PhantomData<{type_name::<T>()}>`) is compiler glue instead
// (src/cgen/fmt.rs), so it exists exactly for the `T` whose type name
// lust can print (`check::any::type_name_of`), and no instance is made
// for the others.

impl<T: ?Sized> core::hash::Hash for PhantomData<T> {
    fn hash<H: core::hash::Hasher>(&self, _: &mut H) {}
}
