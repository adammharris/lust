// Lust adapter: the field type of a flags type the `struct` form of
// `bitflags!` declares.
//
// Upstream declares a private `InternalBitFlags` struct per macro call
// inside `const _: () = { .. };`, with its impls beside it, so the name
// never escapes. Lust has no impls inside bodies yet (L0820), and a
// macro cannot make a fresh name at module level, so this one generic
// type stands in for every `InternalBitFlags`: the bits, and the public
// type it belongs to as a marker. Its impls give the same results as
// upstream's derives and impls on `InternalBitFlags` (internal.rs): the
// derives compare and hash the bits alone, and Debug, Display, and
// FromStr print and parse through the public type. No radix fmt impls
// (`Binary`, `LowerHex`, ..): lust has no user impls of those yet.
//
// Not here: upstream's inherent methods on the internal type (the same
// set as the public type's, plus `bits_mut`). Only code in the module
// that calls `bitflags!` can reach the field to call them.

use crate::Bits;
use crate::parser::ParseError;
use core::fmt;
use core::marker::PhantomData;

// Derived, as upstream derives them on `InternalBitFlags`: they compare
// and hash the bits (`PhantomData` adds nothing). The derives also bound
// `P`, the flags type, which derives the same traits to use them.
#[doc(hidden)]
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Internal<P, B>(pub B, pub PhantomData<P>);

impl<P, B: Bits> Default for Internal<P, B> {
    fn default() -> Self {
        Internal(B::EMPTY, PhantomData)
    }
}

/// The link from a flags type to its bits, which the macro implements
/// for each flags type with concrete types. Lust cannot yet use a
/// bound `P: Flags<Bits = B>` in these generic impls (it loses `B`), so
/// the per-type impl does the work upstream's `InternalBitFlags` impls
/// do: Debug, Display through the parser, and FromStr.
#[doc(hidden)]
pub trait LinkBits<B>: Sized {
    fn __debug_bits(bits: B, f: &mut fmt::Formatter<'_>) -> fmt::Result;
    fn __display_bits(bits: B, f: &mut fmt::Formatter<'_>) -> fmt::Result;
    fn __parse_bits(s: &str) -> Result<B, ParseError>;
}

impl<P: LinkBits<B>, B: Copy> fmt::Debug for Internal<P, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        P::__debug_bits(self.0, f)
    }
}

impl<P: LinkBits<B>, B: Copy> fmt::Display for Internal<P, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        P::__display_bits(self.0, f)
    }
}

impl<P: LinkBits<B>, B> core::str::FromStr for Internal<P, B> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        P::__parse_bits(s).map(|bits| Internal(bits, PhantomData))
    }
}

impl<P, B> AsRef<B> for Internal<P, B> {
    fn as_ref(&self) -> &B {
        &self.0
    }
}

impl<P, B> From<B> for Internal<P, B> {
    fn from(bits: B) -> Self {
        Internal(bits, PhantomData)
    }
}

/// The rest of upstream's per-call impls, at module level: the
/// `PublicFlags` link and the constructor the wrapped bodies use.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_lust_internal {
    ($PublicBitFlags:ident: $T:ty) => {
        impl $crate::__private::PublicFlags for $PublicBitFlags {
            type Primitive = $T;
            type Internal = $crate::__private::Internal<$PublicBitFlags, $T>;
        }

        impl $crate::__private::LinkBits<$T> for $PublicBitFlags {
            fn __debug_bits(bits: $T, f: &mut $crate::__private::core::fmt::Formatter<'_>) -> $crate::__private::core::fmt::Result {
                // Upstream: `write!(f, "{:#x}", EMPTY)` for the empty
                // value; every `Bits` type's EMPTY is 0, which `{:#x}`
                // writes as `0x0` (no padding: `write!` starts fresh
                // format arguments).
                if bits == <$T as $crate::Bits>::EMPTY {
                    f.write_str("0x0")
                } else {
                    $crate::parser::to_writer(&$PublicBitFlags::from_bits_retain(bits), f)
                }
            }

            fn __display_bits(bits: $T, f: &mut $crate::__private::core::fmt::Formatter<'_>) -> $crate::__private::core::fmt::Result {
                $crate::parser::to_writer(&$PublicBitFlags::from_bits_retain(bits), f)
            }

            fn __parse_bits(s: &str) -> $crate::__private::core::result::Result<$T, $crate::parser::ParseError> {
                $crate::parser::from_str::<$PublicBitFlags>(s).map(|flags| flags.bits())
            }
        }

        impl $PublicBitFlags {
            #[doc(hidden)]
            #[inline]
            const fn __bitflags_raw(bits: $T) -> Self {
                Self($crate::__private::Internal(bits, $crate::__private::core::marker::PhantomData))
            }
        }
    };
}
