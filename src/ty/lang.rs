// Lang items, shipped crates, and the intrinsic registry (docs/ARCH.md
// sections 3.1, 3.2, and 3.6, serial refactor S5).
//
// Three closed tables live here, in one place, so no other file hardcodes a
// std path or an intrinsic name:
//
// - `LANG_ITEMS`: the items the compiler must know by def (section 3.1).
//   The std loader (`src/stdload.rs`) fills a `LangItems` once per session:
//   builtin-backed items come from `BuiltinDefs`, source items from
//   `#[lust_lang = "..."]` marks in `library/` source. A missing item that
//   is marked `required` is a compiler installation error, never a user
//   diagnostic. An item that is not required yet has no source def today;
//   the ledger in `library/README.md` tracks it.
// - `INTRINSICS`: every compiler-known callable (section 3.2), each with a
//   normal fn signature, a C symbol, and the shipped crates that may call
//   it. Check and cgen both run the privilege test (section 3.1 item 1):
//   only a shipped crate named in the row may name the intrinsic, matched
//   by the crate the call site's source belongs to, never by name matching
//   in user source. A user call is `L0642`. A privileged call to an
//   intrinsic whose body does not exist yet is `L0640`. Only `implemented`
//   rows reach codegen.
// - `STD_FNS`: the non-generic source std fns the loader splices into a
//   compile (section 9.2 S5: the source path covers non-generic fns only
//   until the minimal generic pipeline). A row with `implemented: false`
//   is a declared std item with no body yet: a call rejects with `L0640`
//   naming the item, per the surface-parity rule in section 3.1.
use super::{BOOL, BuiltinDefs, FloatTy, I32, Mut, NEVER, Ty, TyIntern, TyKind, UNIT, USIZE};
use crate::def::{DefId, StableCrateHash, stable_crate_hash};

/// A crate the compiler ships in `library/` (section 3.1) or `library/deps/`
/// (section 3.6). Privilege is matched by this identity (through its stable
/// crate hash at load, and through source ranges in a spliced compile),
/// never by a name a user crate can write.
#[allow(dead_code)] // Adapter variants are first constructed by W-DEPS source; registry rows name them now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShippedCrate {
    Core,
    Alloc,
    Std,
    RustcHash,
    Indexmap,
    Smallvec,
    Memchr,
    Bumpalo,
    XxhashRust,
    RyuJs,
    NumBigInt,
    Rustix,
    Nix,
    SignalHook,
    NameToHandleAt,
}

impl ShippedCrate {
    /// Every shipped crate, in `library/` layout order.
    #[allow(dead_code)] // Iterated by registry tests now; the driver iterates it when adapter loading lands.
    pub const ALL: &[ShippedCrate] = &[
        ShippedCrate::Core,
        ShippedCrate::Alloc,
        ShippedCrate::Std,
        ShippedCrate::RustcHash,
        ShippedCrate::Indexmap,
        ShippedCrate::Smallvec,
        ShippedCrate::Memchr,
        ShippedCrate::Bumpalo,
        ShippedCrate::XxhashRust,
        ShippedCrate::RyuJs,
        ShippedCrate::NumBigInt,
        ShippedCrate::Rustix,
        ShippedCrate::Nix,
        ShippedCrate::SignalHook,
        ShippedCrate::NameToHandleAt,
    ];

    /// The crate name as user code writes it in a path (`std::...`).
    pub fn name(self) -> &'static str {
        match self {
            ShippedCrate::Core => "core",
            ShippedCrate::Alloc => "alloc",
            ShippedCrate::Std => "std",
            ShippedCrate::RustcHash => "rustc_hash",
            ShippedCrate::Indexmap => "indexmap",
            ShippedCrate::Smallvec => "smallvec",
            ShippedCrate::Memchr => "memchr",
            ShippedCrate::Bumpalo => "bumpalo",
            ShippedCrate::XxhashRust => "xxhash_rust",
            ShippedCrate::RyuJs => "ryu_js",
            ShippedCrate::NumBigInt => "num_bigint",
            ShippedCrate::Rustix => "rustix",
            ShippedCrate::Nix => "nix",
            ShippedCrate::SignalHook => "signal_hook",
            ShippedCrate::NameToHandleAt => "name_to_handle_at",
        }
    }

    /// The crate's stable disambiguator (section 1.7). The shipped library
    /// is fixed inside one lust version, so the package id is a constant.
    /// This is the identity intrinsic privilege is matched by at std load.
    pub fn stable_hash(self) -> StableCrateHash {
        stable_crate_hash(&format!("lust-library-v1/{}", self.name()), "lib", self.name(), false)
    }
}

/// One lang item the compiler must know by def (section 3.1). New items go
/// at the end only; the discriminant indexes `LangItems`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LangItem {
    Option,
    Result,
    String,
    Vec,
    Box,
    Rc,
    Arc,
    UnsafeCell,
    PhantomData,
    Range,
    RangeFrom,
    RangeTo,
    RangeFull,
    RangeInclusive,
    RangeToInclusive,
    Iterator,
    IntoIterator,
    Drop,
    Deref,
    DerefMut,
    Fn,
    FnMut,
    FnOnce,
    Sized,
    Send,
    Sync,
    Panic,
    PanicBounds,
    Formatter,
    ExchangeMalloc,
    ExchangeFree,
}

/// The static row for one lang item: its `#[lust_lang]` name, the shipped
/// crate that must define it, and whether std load must fail without it
/// today. Only items with a def source today (a builtin def, or shipped
/// source) are `required`; the rest join as W-STD writes them.
pub struct LangItemDef {
    pub item: LangItem,
    pub name: &'static str,
    pub krate: ShippedCrate,
    pub required: bool,
}

use LangItem as L;
use ShippedCrate as C;

/// The lang item table (section 3.1). Keep rows in `LangItem` order: the
/// row index is the item's discriminant (a test pins this).
pub const LANG_ITEMS: &[LangItemDef] = &[
    LangItemDef { item: L::Option, name: "option", krate: C::Core, required: true },
    LangItemDef { item: L::Result, name: "result", krate: C::Core, required: true },
    LangItemDef { item: L::String, name: "string", krate: C::Alloc, required: true },
    LangItemDef { item: L::Vec, name: "vec", krate: C::Alloc, required: true },
    LangItemDef { item: L::Box, name: "box", krate: C::Alloc, required: true },
    LangItemDef { item: L::Rc, name: "rc", krate: C::Alloc, required: true },
    LangItemDef { item: L::Arc, name: "arc", krate: C::Alloc, required: false },
    LangItemDef { item: L::UnsafeCell, name: "unsafe_cell", krate: C::Core, required: false },
    LangItemDef { item: L::PhantomData, name: "phantom_data", krate: C::Core, required: false },
    LangItemDef { item: L::Range, name: "range", krate: C::Core, required: false },
    LangItemDef { item: L::RangeFrom, name: "range_from", krate: C::Core, required: false },
    LangItemDef { item: L::RangeTo, name: "range_to", krate: C::Core, required: false },
    LangItemDef { item: L::RangeFull, name: "range_full", krate: C::Core, required: false },
    LangItemDef { item: L::RangeInclusive, name: "range_inclusive", krate: C::Core, required: false },
    LangItemDef { item: L::RangeToInclusive, name: "range_to_inclusive", krate: C::Core, required: false },
    LangItemDef { item: L::Iterator, name: "iterator", krate: C::Core, required: false },
    LangItemDef { item: L::IntoIterator, name: "into_iterator", krate: C::Core, required: false },
    LangItemDef { item: L::Drop, name: "drop", krate: C::Core, required: false },
    LangItemDef { item: L::Deref, name: "deref", krate: C::Core, required: false },
    LangItemDef { item: L::DerefMut, name: "deref_mut", krate: C::Core, required: false },
    LangItemDef { item: L::Fn, name: "fn", krate: C::Core, required: false },
    LangItemDef { item: L::FnMut, name: "fn_mut", krate: C::Core, required: false },
    LangItemDef { item: L::FnOnce, name: "fn_once", krate: C::Core, required: false },
    LangItemDef { item: L::Sized, name: "sized", krate: C::Core, required: false },
    LangItemDef { item: L::Send, name: "send", krate: C::Core, required: false },
    LangItemDef { item: L::Sync, name: "sync", krate: C::Core, required: false },
    LangItemDef { item: L::Panic, name: "panic", krate: C::Core, required: false },
    LangItemDef { item: L::PanicBounds, name: "panic_bounds", krate: C::Core, required: false },
    LangItemDef { item: L::Formatter, name: "formatter", krate: C::Core, required: false },
    LangItemDef { item: L::ExchangeMalloc, name: "exchange_malloc", krate: C::Alloc, required: false },
    LangItemDef { item: L::ExchangeFree, name: "exchange_free", krate: C::Alloc, required: false },
];

/// The lang item with this `#[lust_lang]` name, if the table has it.
pub fn lang_item_by_name(name: &str) -> Option<LangItem> {
    LANG_ITEMS.iter().find(|d| d.name == name).map(|d| d.item)
}

/// The resolved lang items of one std load: one def per item, or none while
/// the item has no def source. Built by the std loader, read by later waves
/// (mono, traits) through `get`.
#[derive(Clone, Debug)]
pub struct LangItems {
    defs: [Option<DefId>; LANG_ITEMS.len()],
}

impl LangItems {
    /// A table with the builtin-backed items filled from `BuiltinDefs`.
    /// These types are builtin Adts until source std replaces them
    /// (section 3.1); their defs are already stable path hashes.
    pub fn from_builtins(b: BuiltinDefs) -> LangItems {
        let mut items = LangItems { defs: [None; LANG_ITEMS.len()] };
        items.set(LangItem::Option, b.option);
        items.set(LangItem::Result, b.result);
        items.set(LangItem::String, b.string);
        items.set(LangItem::Vec, b.vec);
        items.set(LangItem::Box, b.boxed);
        items.set(LangItem::Rc, b.rc);
        items
    }

    /// Records the def of one item. A second record replaces the first;
    /// the loader reports duplicates before it calls this.
    pub fn set(&mut self, item: LangItem, def: DefId) {
        self.defs[item as usize] = Some(def);
    }

    /// The def of one item, if this load resolved it.
    pub fn get(&self, item: LangItem) -> Option<DefId> {
        self.defs[item as usize]
    }

    /// Required items with no def. Empty on a good load; the loader turns
    /// a non-empty list into an installation error (section 3.1).
    pub fn required_missing(&self) -> Vec<LangItem> {
        LANG_ITEMS.iter().filter(|d| d.required && self.get(d.item).is_none()).map(|d| d.item).collect()
    }
}

/// One type in an intrinsic signature, before interning. The registry is a
/// static table, so it cannot hold a `Ty`; check resolves these through
/// the body's type store. `Ptr` is an erased raw pointer (`*mut ()`):
/// sized intrinsics take explicit size and align (section 3.2), and the
/// typed pointer API is source in std wrappers. `Bytes` is `&[u8]`,
/// passed to C as two arguments (`const uint8_t *ptr, uint64_t len`), so
/// adapter cores can take a slice before source std has raw pointers.
/// `U128` is `u128` (C `lust_u128`). `StringMut` is `&mut String` (C
/// `lust_String *`), for a core that appends text. New variants go at
/// the end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SigTy {
    Unit,
    Never,
    Bool,
    I32,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Ptr,
    Bytes,
    U128,
    StringMut,
    I64,
    /// `&mut Vec<u8>`: an output byte buffer (a `lust_Vec *` in C).
    VecU8Mut,
    /// `Vec<u8>` by value (a `lust_Vec` in C).
    VecU8,
    /// `fmt::Arguments` by value: its formatted text, a `lust_String`
    /// in C (W-SHIM; see `cgen::fmt_ctype`).
    Arguments,
    /// `&str` (a `lust_str` in C).
    Str,
    /// `String` by value (a `lust_String` in C).
    String,
    /// `&mut fmt::Formatter<'_>`.
    FmtMut,
}

impl SigTy {
    /// The interned form of this signature type in `tys`.
    pub fn resolve(self, tys: &mut impl TyIntern) -> Ty {
        match self {
            SigTy::Unit => UNIT,
            SigTy::Never => NEVER,
            SigTy::Bool => BOOL,
            SigTy::I32 => I32,
            SigTy::U32 => super::int(super::IntTy::U32),
            SigTy::U64 => super::int(super::IntTy::U64),
            SigTy::Usize => USIZE,
            SigTy::F32 => tys.intern(TyKind::Float(FloatTy::F32)),
            SigTy::F64 => tys.intern(TyKind::Float(FloatTy::F64)),
            SigTy::Ptr => tys.intern(TyKind::RawPtr(Mut::Mut, UNIT)),
            SigTy::Bytes => {
                let bytes = tys.intern(TyKind::Slice(super::int(super::IntTy::U8)));
                tys.intern(TyKind::Ref(super::Region::Erased, Mut::Shared, bytes))
            }
            SigTy::U128 => super::int(super::IntTy::U128),
            SigTy::StringMut => tys.intern(TyKind::Ref(super::Region::Erased, Mut::Mut, super::STRING)),
            SigTy::I64 => super::int(super::IntTy::I64),
            SigTy::VecU8Mut => {
                let v = tys.mk_vec(super::int(super::IntTy::U8));
                tys.intern(TyKind::Ref(super::Region::Erased, Mut::Mut, v))
            }
            SigTy::VecU8 => tys.mk_vec(super::int(super::IntTy::U8)),
            SigTy::Arguments => super::fmt::fmt_ty(tys, super::fmt::FmtTy::Arguments),
            SigTy::Str => super::REF_STR,
            SigTy::String => super::STRING,
            SigTy::FmtMut => {
                let f = super::fmt::fmt_ty(tys, super::fmt::FmtTy::Formatter);
                tys.intern(TyKind::Ref(super::Region::Erased, Mut::Mut, f))
            }
        }
    }
}

/// One intrinsic (section 3.2): a normal fn signature in
/// `core::intrinsics`, a C symbol, the shipped crates that may call it,
/// and whether codegen can emit it today. The id of an intrinsic in
/// check side tables and IR is its index in `INTRINSICS`; add new rows
/// at the end of their group only in a wave that owns this file, and
/// never remove or reorder a row inside one lust version.
pub struct IntrinsicDef {
    pub name: &'static str,
    pub c_symbol: &'static str,
    pub params: &'static [SigTy],
    pub ret: SigTy,
    pub allowed: &'static [ShippedCrate],
    pub implemented: bool,
}

impl IntrinsicDef {
    /// True if source that belongs to `krate` may call this intrinsic.
    /// `None` is user source: never allowed (section 3.1 item 1).
    pub fn allows(&self, krate: Option<ShippedCrate>) -> bool {
        krate.is_some_and(|k| self.allowed.contains(&k))
    }
}

use SigTy as S;

const LIB: &[ShippedCrate] = &[C::Core, C::Alloc, C::Std];
const ALLOC_STD: &[ShippedCrate] = &[C::Alloc, C::Std];
const CORE_ALLOC: &[ShippedCrate] = &[C::Core, C::Alloc];
const CORE_STD: &[ShippedCrate] = &[C::Core, C::Std];
const ONLY_STD: &[ShippedCrate] = &[C::Std];

/// The intrinsic registry (section 3.2 table, plus the section 3.4
/// predicates and the section 3.6 adapter cores). Width-specific atomic
/// and sync variants are one row per operation today; W-STD widens a row
/// into per-width rows when its wrappers land, with a difftest each.
pub const INTRINSICS: &[IntrinsicDef] = &[
    // Memory: the process allocator (section 3.7).
    IntrinsicDef {
        name: "alloc",
        c_symbol: "lust_alloc",
        params: &[S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "dealloc",
        c_symbol: "lust_dealloc",
        params: &[S::Ptr, S::Usize, S::Usize],
        ret: S::Unit,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "realloc",
        c_symbol: "lust_realloc",
        params: &[S::Ptr, S::Usize, S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "alloc_zeroed",
        c_symbol: "lust_alloc_zeroed",
        params: &[S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    // Bytes.
    IntrinsicDef {
        name: "memcpy",
        c_symbol: "lust_memcpy",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memmove",
        c_symbol: "lust_memmove",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memset",
        c_symbol: "lust_memset",
        params: &[S::Ptr, S::U32, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memcmp",
        c_symbol: "lust_memcmp",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: LIB,
        implemented: false,
    },
    // Raw pointer load/store/offset: one unsafe boundary for borrowck.
    IntrinsicDef {
        name: "ptr_read",
        c_symbol: "lust_ptr_read",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "ptr_write",
        c_symbol: "lust_ptr_write",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "ptr_offset",
        c_symbol: "lust_ptr_offset",
        params: &[S::Ptr, S::Usize],
        ret: S::Ptr,
        allowed: LIB,
        implemented: false,
    },
    // Float text: shortest round-trip print, correctly rounded parse.
    // The C entry takes (out, value, spec); SigTy cannot name the spec
    // struct yet, so these rows name the plain Display entries, whose
    // C signatures are exactly (out, value). A formatted row joins
    // when SigTy can name the spec (W-STD).
    IntrinsicDef {
        name: "fmt_f64",
        c_symbol: "lust_fmt_f64_display",
        params: &[S::Ptr, S::F64],
        ret: S::Unit,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "fmt_f32",
        c_symbol: "lust_fmt_f32_display",
        params: &[S::Ptr, S::F32],
        ret: S::Unit,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "parse_f64",
        c_symbol: "lust_parse_f64",
        params: &[S::Ptr, S::Usize],
        ret: S::F64,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "parse_f32",
        c_symbol: "lust_parse_f32",
        params: &[S::Ptr, S::Usize],
        ret: S::F32,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    // Panic entry points (section 7).
    IntrinsicDef {
        name: "panic",
        c_symbol: "lust_panic_payload",
        params: &[S::Ptr, S::Ptr, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "panic_bounds",
        c_symbol: "lust_panic_bounds",
        params: &[S::Usize, S::Usize, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "panic_str",
        c_symbol: "lust_panic_str",
        params: &[S::Ptr, S::Usize, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    // Threads and TLS (section 7.3).
    IntrinsicDef {
        name: "thread_spawn",
        c_symbol: "lust_thread_spawn",
        params: &[S::Ptr, S::Ptr],
        ret: S::U64,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "thread_join_raw",
        c_symbol: "lust_thread_join_raw",
        params: &[S::U64],
        ret: S::Ptr,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "tls_key_create",
        c_symbol: "lust_tls_key_create",
        params: &[S::Ptr],
        ret: S::U64,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "tls_get", c_symbol: "lust_tls_get", params: &[S::U64], ret: S::Ptr, allowed: ONLY_STD, implemented: false },
    IntrinsicDef {
        name: "tls_set",
        c_symbol: "lust_tls_set",
        params: &[S::U64, S::Ptr],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "park", c_symbol: "lust_park", params: &[], ret: S::Unit, allowed: ONLY_STD, implemented: false },
    IntrinsicDef { name: "unpark", c_symbol: "lust_unpark", params: &[S::U64], ret: S::Unit, allowed: ONLY_STD, implemented: false },
    // Sync cores on opaque handles.
    IntrinsicDef {
        name: "mutex_lock",
        c_symbol: "lust_mutex_lock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "mutex_unlock",
        c_symbol: "lust_mutex_unlock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_read",
        c_symbol: "lust_rwlock_read",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_write",
        c_symbol: "lust_rwlock_write",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_unlock",
        c_symbol: "lust_rwlock_unlock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_wait",
        c_symbol: "lust_condvar_wait",
        params: &[S::U64, S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_notify_one",
        c_symbol: "lust_condvar_notify_one",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_notify_all",
        c_symbol: "lust_condvar_notify_all",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    // Atomics (per width and ordering when the wrappers land).
    IntrinsicDef {
        name: "atomic_load",
        c_symbol: "lust_atomic_load",
        params: &[S::Ptr, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_store",
        c_symbol: "lust_atomic_store",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::Unit,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_xchg",
        c_symbol: "lust_atomic_xchg",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_cas",
        c_symbol: "lust_atomic_cas",
        params: &[S::Ptr, S::U64, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_fetch_add",
        c_symbol: "lust_atomic_fetch_add",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    // Time.
    // A clock reading: the low word is tv_sec (i64 bits), the high word
    // tv_nsec (W-STD-C; runtime/stdc.c). Monotonic for `Instant`,
    // realtime for `SystemTime`.
    IntrinsicDef { name: "clock_now_raw", c_symbol: "lust_clock_now_raw", params: &[], ret: S::U128, allowed: ONLY_STD, implemented: true },
    IntrinsicDef {
        name: "system_time_raw",
        c_symbol: "lust_system_time_raw",
        params: &[],
        ret: S::U128,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Raw fd IO plus errno.
    IntrinsicDef {
        name: "fd_read",
        c_symbol: "lust_fd_read",
        params: &[S::I32, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "fd_write",
        c_symbol: "lust_fd_write",
        params: &[S::I32, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "fd_close", c_symbol: "lust_fd_close", params: &[S::I32], ret: S::I32, allowed: ONLY_STD, implemented: false },
    IntrinsicDef { name: "errno", c_symbol: "lust_errno", params: &[], ret: S::I32, allowed: ONLY_STD, implemented: false },
    // Process: raw args/env tables, and exit.
    IntrinsicDef {
        name: "args_raw",
        c_symbol: "lust_args_raw",
        params: &[S::Usize, S::Ptr],
        ret: S::Bool,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "env_get",
        c_symbol: "lust_env_get",
        params: &[S::Ptr, S::Usize, S::Ptr],
        ret: S::Bool,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "exit", c_symbol: "lust_exit", params: &[S::I32], ret: S::Never, allowed: ONLY_STD, implemented: true },
    // std::alloc::handle_alloc_error: std's alloc error hook text for a layout of `size` bytes, then abort.
    IntrinsicDef { name: "alloc_error", c_symbol: "lust_oom_size", params: &[S::Usize], ret: S::Never, allowed: ONLY_STD, implemented: true },
    // Specialization predicates (section 3.4). Mono evaluates them as
    // constants after substitution; the signature here is the erased form.
    IntrinsicDef { name: "is_trusted_random_access", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    IntrinsicDef { name: "is_trusted_len", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    IntrinsicDef { name: "in_place_collect", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    // Adapter cores (section 3.6): each adapter only its own rows.
    IntrinsicDef {
        name: "arena_alloc",
        c_symbol: "lust_arena_alloc",
        params: &[S::U64, S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: &[C::Bumpalo],
        implemented: false,
    },
    // Byte and substring search: the index of the first (memchr, memmem)
    // or last (memrchr) match, or usize::MAX for none (no slice is that
    // long).
    IntrinsicDef {
        name: "memchr",
        c_symbol: "lust_memchr",
        params: &[S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    IntrinsicDef {
        name: "memrchr",
        c_symbol: "lust_memrchr",
        params: &[S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    // The first or last index of a byte equal to one of three needles (two needles repeat
    // one): the port's memchr2/memchr3 searches.
    IntrinsicDef {
        name: "memchr3",
        c_symbol: "lust_memchr3",
        params: &[S::U32, S::U32, S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    IntrinsicDef {
        name: "memrchr3",
        c_symbol: "lust_memrchr3",
        params: &[S::U32, S::U32, S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    IntrinsicDef {
        name: "memmem",
        c_symbol: "lust_memmem",
        params: &[S::Bytes, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    // XXH3 of the bytes with a seed (0 is the unseeded hash).
    IntrinsicDef {
        name: "xxh3_64",
        c_symbol: "lust_xxh3_64",
        params: &[S::Bytes, S::U64],
        ret: S::U64,
        allowed: &[C::XxhashRust],
        implemented: true,
    },
    IntrinsicDef {
        name: "xxh3_128",
        c_symbol: "lust_xxh3_128",
        params: &[S::Bytes, S::U64],
        ret: S::U128,
        allowed: &[C::XxhashRust],
        implemented: true,
    },
    // Appends the ECMAScript Number::toString text of the f64 (ryu-js
    // 1.0.2 Buffer::format) to the String; the core is in float.c.
    IntrinsicDef {
        name: "ryu_js_fmt_f64",
        c_symbol: "lust_fmt_js_f64",
        params: &[S::StringMut, S::F64],
        ret: S::Unit,
        allowed: &[C::RyuJs],
        implemented: true,
    },
    // The std platform crate (W-SHIM, library/std/src/platform.rs; C in
    // src/runtime/sys.c). Errors come back as negative errno values or
    // as a nonzero errno.
    //
    // Writes the bytes to stdout (fd 1) or stderr (fd 2) through the
    // runtime's stdio stream that `print!`/`eprint!` use: the count
    // written, or -errno.
    IntrinsicDef {
        name: "sys_write_std",
        c_symbol: "lust_sys_write_std",
        params: &[S::I32, S::Bytes],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Flushes that stream: 0, or the errno.
    IntrinsicDef {
        name: "sys_flush_std",
        c_symbol: "lust_sys_flush_std",
        params: &[S::I32],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The bytes of a `format_args!` value (`io::Write::write_fmt`).
    IntrinsicDef {
        name: "sys_fmt_arguments_bytes",
        c_symbol: "lust_sys_fmt_arguments_bytes",
        params: &[S::Arguments],
        ret: S::VecU8,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Byte views of text (W-SHIM, for OsStr and Path): `&str` as its
    // bytes, and bytes as `&str` with no check (the caller validated
    // them, or they are an OsStr's raw bytes only std reads as text).
    // As a return, `&[u8]` comes back from C as a lust_str.
    IntrinsicDef {
        name: "sys_str_as_bytes",
        c_symbol: "lust_sys_str_as_bytes",
        params: &[S::Str],
        ret: S::Bytes,
        allowed: ONLY_STD,
        implemented: true,
    },
    IntrinsicDef {
        name: "sys_bytes_as_str",
        c_symbol: "lust_sys_bytes_as_str",
        params: &[S::Bytes],
        ret: S::Str,
        allowed: ONLY_STD,
        implemented: true,
    },
    // `Vec<u8>` to `String` with no check, taking over the buffer.
    IntrinsicDef {
        name: "sys_string_from_utf8_unchecked",
        c_symbol: "lust_sys_string_from_utf8_unchecked",
        params: &[S::VecU8],
        ret: S::String,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The length of the longest valid UTF-8 prefix of the bytes.
    IntrinsicDef {
        name: "sys_utf8_valid_up_to",
        c_symbol: "lust_sys_utf8_valid_up_to",
        params: &[S::Bytes],
        ret: S::Usize,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Appends the bytes to the String as `String::from_utf8_lossy` does
    // (U+FFFD per maximal invalid subpart).
    IntrinsicDef {
        name: "sys_utf8_lossy",
        c_symbol: "lust_sys_utf8_lossy",
        params: &[S::Bytes, S::StringMut],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // getenv: appends the value's bytes to the Vec and returns true, or
    // returns false when the variable is unset (or the key holds NUL).
    IntrinsicDef {
        name: "sys_getenv",
        c_symbol: "lust_sys_getenv",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::Bool,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Appends every `environ` entry, each with a NUL terminator.
    IntrinsicDef {
        name: "sys_environ",
        c_symbol: "lust_sys_environ",
        params: &[S::VecU8Mut],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Appends every `argv` entry, each with a NUL terminator.
    IntrinsicDef {
        name: "sys_argv",
        c_symbol: "lust_sys_argv",
        params: &[S::VecU8Mut],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Appends the current directory; 0, or errno.
    IntrinsicDef {
        name: "sys_getcwd",
        c_symbol: "lust_sys_getcwd",
        params: &[S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // chdir: 0, errno, or -1 for a path with a NUL byte.
    IntrinsicDef {
        name: "sys_chdir",
        c_symbol: "lust_sys_chdir",
        params: &[S::Bytes],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // readlink into the Vec: 0, errno, or -1 for a path with a NUL byte.
    IntrinsicDef {
        name: "sys_readlink",
        c_symbol: "lust_sys_readlink",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Reads a whole file into the Vec. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_read_file",
        c_symbol: "lust_sys_read_file",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Creates or truncates a file and writes the bytes. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_write_file",
        c_symbol: "lust_sys_write_file",
        params: &[S::Bytes, S::Bytes],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // mkdir (0), unlink (1), or rmdir (2). 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_path_op",
        c_symbol: "lust_sys_path_op",
        params: &[S::Bytes, S::I32],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // rename. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_rename",
        c_symbol: "lust_sys_rename",
        params: &[S::Bytes, S::Bytes],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // stat (true) or lstat as 8-byte fields. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_stat",
        c_symbol: "lust_sys_stat",
        params: &[S::Bytes, S::Bool, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // realpath into the Vec. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_realpath",
        c_symbol: "lust_sys_realpath",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The NUL-terminated names of a directory. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_read_dir",
        c_symbol: "lust_sys_read_dir",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // remove_dir_all as std does it on Linux. 0, errno, or -1 for a NUL byte (sys.h).
    IntrinsicDef {
        name: "sys_remove_dir_all",
        c_symbol: "lust_sys_remove_dir_all",
        params: &[S::Bytes],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // getpid.
    IntrinsicDef { name: "sys_getpid", c_symbol: "lust_sys_getpid", params: &[], ret: S::U32, allowed: &[C::Std, C::Rustix], implemented: true },
    // The running executable's path into the Vec (env::current_exe, sys.h).
    // 0 or errno.
    IntrinsicDef {
        name: "sys_current_exe",
        c_symbol: "lust_sys_current_exe",
        params: &[S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Appends the OS text of an error code (strerror) to the String.
    IntrinsicDef {
        name: "sys_os_error_text",
        c_symbol: "lust_sys_os_error_text",
        params: &[S::I32, S::StringMut],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The std platform crate's fd and process calls (W-SHIM phase 2,
    // src/runtime/sysio.c). Counts come back with -errno for errors;
    // the rest return 0 or errno (sysio.h has each contract).
    // One read of up to `max` bytes from the fd into the Vec.
    IntrinsicDef {
        name: "sys_fd_read",
        c_symbol: "lust_sys_fd_read",
        params: &[S::I32, S::U64, S::VecU8Mut],
        ret: S::I64,
        allowed: &[C::Std, C::Rustix],
        implemented: true,
    },
    // One write of the bytes to the fd.
    IntrinsicDef {
        name: "sys_fd_write",
        c_symbol: "lust_sys_fd_write",
        params: &[S::I32, S::Bytes],
        ret: S::I64,
        allowed: &[C::Std, C::Rustix, C::SignalHook],
        implemented: true,
    },
    // close.
    IntrinsicDef { name: "sys_fd_close", c_symbol: "lust_sys_fd_close", params: &[S::I32], ret: S::I32, allowed: &[C::Std, C::Rustix, C::SignalHook], implemented: true },
    // dup with FD_CLOEXEC: the new fd, or -errno.
    IntrinsicDef { name: "sys_fd_dup", c_symbol: "lust_sys_fd_dup", params: &[S::I32], ret: S::I32, allowed: &[C::Std, C::Rustix], implemented: true },
    // fsync.
    IntrinsicDef { name: "sys_fd_sync", c_symbol: "lust_sys_fd_sync", params: &[S::I32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // fdatasync.
    IntrinsicDef {
        name: "sys_fd_sync_data",
        c_symbol: "lust_sys_fd_sync_data",
        params: &[S::I32],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // ftruncate to the length.
    IntrinsicDef {
        name: "sys_fd_truncate",
        c_symbol: "lust_sys_fd_truncate",
        params: &[S::I32, S::U64],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // lseek: the new position, or -errno.
    IntrinsicDef {
        name: "sys_fd_seek",
        c_symbol: "lust_sys_fd_seek",
        params: &[S::I32, S::I64, S::I32],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // pread of up to `max` bytes at the offset, appended to the Vec: the
    // count, or -errno (FileExt::read_at, tf-p6).
    IntrinsicDef {
        name: "sys_fd_pread",
        c_symbol: "lust_sys_fd_pread",
        params: &[S::I32, S::U64, S::I64, S::VecU8Mut],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // pwrite of the bytes at the offset: the count, or -errno.
    IntrinsicDef {
        name: "sys_fd_pwrite",
        c_symbol: "lust_sys_fd_pwrite",
        params: &[S::I32, S::Bytes, S::I64],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // isatty: 1 for a terminal, else 0 (IsTerminal, tf-p6).
    IntrinsicDef { name: "sys_fd_isatty", c_symbol: "lust_sys_fd_isatty", params: &[S::I32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // The path an open fd names (File's Debug): 0 or errno.
    IntrinsicDef {
        name: "sys_fd_path",
        c_symbol: "lust_sys_fd_path",
        params: &[S::I32, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // fstat as 8-byte fields, like sys_stat.
    IntrinsicDef {
        name: "sys_fd_stat",
        c_symbol: "lust_sys_fd_stat",
        params: &[S::I32, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // open with the abstract flag bits of sysio.c: the fd, or -errno.
    IntrinsicDef {
        name: "sys_fd_open",
        c_symbol: "lust_sys_fd_open",
        params: &[S::Bytes, S::I32],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // `OpenOptions::open` with std's custom flags and creation mode
    // (OpenOptionsExt, sysio.c): the fd or -errno.
    IntrinsicDef {
        name: "sys_fd_open_ext",
        c_symbol: "lust_sys_fd_open_ext",
        params: &[S::Bytes, S::I32, S::I32, S::U32],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Stdin through the process-wide buffer: up to `max` bytes into
    // the Vec, the count or -errno.
    IntrinsicDef {
        name: "sys_stdin_read",
        c_symbol: "lust_sys_stdin_read",
        params: &[S::U64, S::VecU8Mut],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The buffered stdin bytes into the Vec, not consumed.
    IntrinsicDef {
        name: "sys_stdin_fill",
        c_symbol: "lust_sys_stdin_fill",
        params: &[S::VecU8Mut],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Drops up to `n` buffered stdin bytes.
    IntrinsicDef {
        name: "sys_stdin_consume",
        c_symbol: "lust_sys_stdin_consume",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Spawns a process with the packed argv, env, cwd, stdio specs
    // and fds process_os.rs builds (sysio.c has the formats). On
    // success the Vec gains the pid and the three pipe parent fds as
    // 8-byte fields. 0, or errno.
    IntrinsicDef {
        name: "sys_proc_spawn",
        c_symbol: "lust_sys_proc_spawn",
        params: &[S::Bytes, S::Bytes, S::Bytes, S::Bytes, S::U32, S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // `CommandExt::exec`: the spawn inputs, run in this process
    // (sysio.c); returns only the errno of a failed exec.
    IntrinsicDef {
        name: "sys_proc_exec",
        c_symbol: "lust_sys_proc_exec",
        params: &[S::Bytes, S::Bytes, S::Bytes, S::Bytes, S::U32, S::Bytes],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // waitpid: the raw wait status, -2 when a non-blocking wait
    // finds the child still running, or -errno.
    IntrinsicDef {
        name: "sys_proc_wait",
        c_symbol: "lust_sys_proc_wait",
        params: &[S::U32, S::Bool],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // kill with SIGKILL: 0, or errno.
    IntrinsicDef { name: "sys_proc_kill", c_symbol: "lust_sys_proc_kill", params: &[S::U32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // Reads two fds to EOF at once (poll), for Command::output:
    // 0, or errno of the first failed read.
    IntrinsicDef {
        name: "sys_fd_read_both",
        c_symbol: "lust_sys_fd_read_both",
        params: &[S::I32, S::VecU8Mut, S::I32, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // The socket calls behind `std::net` (w-cinterop,
    // src/runtime/sysnet.c). An address crosses as one 48-byte record
    // (sysnet.h has the layout and each contract).
    // getaddrinfo: address records out, the count, or -1 with the
    // gai_strerror text in the Vec.
    IntrinsicDef {
        name: "sys_net_resolve",
        c_symbol: "lust_sys_net_resolve",
        params: &[S::Bytes, S::U64, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // TCP listener bind of one record: the fd or -errno.
    IntrinsicDef {
        name: "sys_net_tcp_bind",
        c_symbol: "lust_sys_net_tcp_bind",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // UDP bind of one record: the fd or -errno.
    IntrinsicDef {
        name: "sys_net_udp_bind",
        c_symbol: "lust_sys_net_udp_bind",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // TCP connect to one record: the fd or -errno.
    IntrinsicDef {
        name: "sys_net_tcp_connect",
        c_symbol: "lust_sys_net_tcp_connect",
        params: &[S::Bytes, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // connect with a timeout in microseconds: the fd, -errno, or
    // -10000 when the poll timed out.
    IntrinsicDef {
        name: "sys_net_tcp_connect_timeout",
        c_symbol: "lust_sys_net_tcp_connect_timeout",
        params: &[S::Bytes, S::I64, S::VecU8Mut],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: true,
    },
    // connect of an existing fd: 0 or errno.
    IntrinsicDef { name: "sys_net_connect_fd", c_symbol: "lust_sys_net_connect_fd", params: &[S::I32, S::Bytes], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // accept: the new fd or -errno, the peer record out.
    IntrinsicDef { name: "sys_net_accept", c_symbol: "lust_sys_net_accept", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // getsockname (peer 0) or getpeername (peer 1): 0 or errno.
    IntrinsicDef { name: "sys_net_addr_of", c_symbol: "lust_sys_net_addr_of", params: &[S::I32, S::I32, S::VecU8Mut], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // shutdown: 0 read, 1 write, 2 both. 0 or errno.
    IntrinsicDef { name: "sys_net_shutdown", c_symbol: "lust_sys_net_shutdown", params: &[S::I32, S::I32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // Socket options by number (sysnet.h): set 0 or errno.
    IntrinsicDef { name: "sys_net_setopt", c_symbol: "lust_sys_net_setopt", params: &[S::I32, S::I32, S::I64], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // The option's value, or -errno.
    IntrinsicDef { name: "sys_net_getopt", c_symbol: "lust_sys_net_getopt", params: &[S::I32, S::I32], ret: S::I64, allowed: ONLY_STD, implemented: true },
    // sendto (empty record is a plain send): the count or -errno.
    IntrinsicDef {
        name: "sys_net_sendto",
        c_symbol: "lust_sys_net_sendto",
        params: &[S::I32, S::Bytes, S::Bytes],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // recvfrom into the Vec, the source record into the second Vec:
    // the count or -errno. Flags bit 0 is MSG_PEEK.
    IntrinsicDef {
        name: "sys_net_recvfrom",
        c_symbol: "lust_sys_net_recvfrom",
        params: &[S::I32, S::U64, S::I32, S::VecU8Mut, S::VecU8Mut],
        ret: S::I64,
        allowed: ONLY_STD,
        implemented: true,
    },
    // Unix domain sockets (w-cinterop2, sysnet.c unix section):
    // pair returns the first fd and appends the second; bind and
    // connect take path bytes plus an abstract flag; accept and
    // addr append an address record (kind u64, then name bytes).
    IntrinsicDef { name: "sys_net_unix_pair", c_symbol: "lust_sys_net_unix_pair", params: &[S::VecU8Mut], ret: S::I32, allowed: ONLY_STD, implemented: true },
    IntrinsicDef { name: "sys_net_unix_bind", c_symbol: "lust_sys_net_unix_bind", params: &[S::Bytes, S::I32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    IntrinsicDef { name: "sys_net_unix_connect", c_symbol: "lust_sys_net_unix_connect", params: &[S::Bytes, S::I32], ret: S::I32, allowed: ONLY_STD, implemented: true },
    IntrinsicDef { name: "sys_net_unix_accept", c_symbol: "lust_sys_net_unix_accept", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: ONLY_STD, implemented: true },
    IntrinsicDef { name: "sys_net_unix_addr", c_symbol: "lust_sys_net_unix_addr", params: &[S::I32, S::I32, S::VecU8Mut], ret: S::I32, allowed: ONLY_STD, implemented: true },
    // The Unix calls behind the rustix adapter (w-cinterop2,
    // src/runtime/sysx.c). Errors are errno, or -errno where the
    // value is an fd or flags (sysx.h has each contract).
    IntrinsicDef { name: "sys_x_kill", c_symbol: "lust_sys_x_kill", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_getppid", c_symbol: "lust_sys_x_getppid", params: &[], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_prctl_deathsig", c_symbol: "lust_sys_x_prctl_deathsig", params: &[S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_getrlimit", c_symbol: "lust_sys_x_getrlimit", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_setrlimit", c_symbol: "lust_sys_x_setrlimit", params: &[S::I32, S::U64, S::U64], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_openat", c_symbol: "lust_sys_x_openat", params: &[S::I32, S::Bytes, S::I32, S::U32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_statat", c_symbol: "lust_sys_x_statat", params: &[S::I32, S::Bytes, S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_fstat", c_symbol: "lust_sys_x_fstat", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_statx", c_symbol: "lust_sys_x_statx", params: &[S::I32, S::Bytes, S::I32, S::U32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_accessat", c_symbol: "lust_sys_x_accessat", params: &[S::I32, S::Bytes, S::I32, S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef {
        name: "sys_x_utimensat",
        c_symbol: "lust_sys_x_utimensat",
        params: &[S::I32, S::Bytes, S::I64, S::I64, S::I64, S::I64, S::I32],
        ret: S::I32,
        allowed: &[C::Rustix],
        implemented: true,
    },
    IntrinsicDef { name: "sys_x_mknodat", c_symbol: "lust_sys_x_mknodat", params: &[S::I32, S::Bytes, S::U32, S::U64], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_fcntl_getfl", c_symbol: "lust_sys_x_fcntl_getfl", params: &[S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_fcntl_setfl", c_symbol: "lust_sys_x_fcntl_setfl", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_winsize", c_symbol: "lust_sys_x_winsize", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_pipe", c_symbol: "lust_sys_x_pipe", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_dup2", c_symbol: "lust_sys_x_dup2", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_poll", c_symbol: "lust_sys_x_poll", params: &[S::VecU8Mut, S::I64, S::I64], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    // inotify and directory reading for the rustix adapter
    // (tf-adapters F1, sysx.c): fds and watch descriptors come
    // back with -errno for errors, rm_watch with 0 or errno.
    IntrinsicDef { name: "sys_x_inotify_init1", c_symbol: "lust_sys_x_inotify_init1", params: &[S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_inotify_add_watch", c_symbol: "lust_sys_x_inotify_add_watch", params: &[S::I32, S::Bytes, S::U32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_inotify_rm_watch", c_symbol: "lust_sys_x_inotify_rm_watch", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    // One getdents64 of at most `max` bytes into the Vec: the
    // byte count or -errno.
    IntrinsicDef { name: "sys_x_getdents", c_symbol: "lust_sys_x_getdents", params: &[S::I32, S::U64, S::VecU8Mut], ret: S::I64, allowed: &[C::Rustix], implemented: true },
    // statvfs and fstatvfs: the 11-u64 record out, 0 or errno.
    IntrinsicDef { name: "sys_x_statvfs", c_symbol: "lust_sys_x_statvfs", params: &[S::Bytes, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    IntrinsicDef { name: "sys_x_fstatvfs", c_symbol: "lust_sys_x_fstatvfs", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    // waitid for rustix (tf-front2, sysx.c): the siginfo fields out.
    IntrinsicDef { name: "sys_x_waitid", c_symbol: "lust_sys_x_waitid", params: &[S::I32, S::I32, S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::Rustix], implemented: true },
    // pthread_sigmask for nix's SigSet (tf-front2, sysx.c): the set as
    // a bit mask of signals 1..64; 0 or errno.
    IntrinsicDef { name: "sys_x_sigmask", c_symbol: "lust_sys_x_sigmask", params: &[S::I32, S::U64], ret: S::I32, allowed: &[C::Nix], implemented: true },
    // prctl THP disable for the nix adapter: mode 0 get (0/1 or
    // -errno), mode 1 set (0 or -errno).
    IntrinsicDef { name: "sys_x_prctl_thp", c_symbol: "lust_sys_x_prctl_thp", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::Nix], implemented: true },
    // fanotify for the nix adapter (tf-adapters F2, sysx.c):
    // init returns the fd or -errno; mark 0 or errno, with a
    // has_path flag for the optional pathname.
    IntrinsicDef { name: "sys_x_fanotify_init", c_symbol: "lust_sys_x_fanotify_init", params: &[S::U32, S::U32], ret: S::I32, allowed: &[C::Nix], implemented: true },
    IntrinsicDef { name: "sys_x_fanotify_mark", c_symbol: "lust_sys_x_fanotify_mark", params: &[S::I32, S::U32, S::U64, S::I32, S::I32, S::Bytes], ret: S::I32, allowed: &[C::Nix], implemented: true },
    // name_to_handle_at for the name-to-handle-at adapter
    // (tf-adapters F2, sysx.c): the handle record out
    // (handle_type and the mount id as u64 fields, then the
    // handle bytes), 0 or errno. open_by_handle_at returns
    // the fd or -errno.
    IntrinsicDef { name: "sys_x_name_to_handle_at", c_symbol: "lust_sys_x_name_to_handle_at", params: &[S::I32, S::Bytes, S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::NameToHandleAt], implemented: true },
    IntrinsicDef { name: "sys_x_open_by_handle_at", c_symbol: "lust_sys_x_open_by_handle_at", params: &[S::I32, S::I32, S::Bytes, S::I32], ret: S::I32, allowed: &[C::NameToHandleAt], implemented: true },
    // kqueue/kevent for the nix adapter's sys::event (Darwin, sysx.c):
    // kqueue returns the fd or -errno; kevent takes 48-byte records
    // (sysx.h) and returns the event count or -errno.
    IntrinsicDef { name: "sys_x_kqueue", c_symbol: "lust_sys_x_kqueue", params: &[], ret: S::I32, allowed: &[C::Nix], implemented: true },
    IntrinsicDef { name: "sys_x_kevent", c_symbol: "lust_sys_x_kevent", params: &[S::I32, S::Bytes, S::VecU8Mut, S::I32, S::I64, S::I64], ret: S::I32, allowed: &[C::Nix], implemented: true },
    // The signal registry behind the signal-hook adapter.
    IntrinsicDef { name: "sys_sig_register", c_symbol: "lust_sys_sig_register", params: &[S::I32, S::I32, S::Ptr, S::U64], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_register_pipe", c_symbol: "lust_sys_sig_register_pipe", params: &[S::I32, S::I32], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_unregister_pipe", c_symbol: "lust_sys_sig_unregister_pipe", params: &[S::I32], ret: S::Unit, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_pipe", c_symbol: "lust_sys_sig_pipe", params: &[S::VecU8Mut], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_poll_read", c_symbol: "lust_sys_sig_poll_read", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_read_now", c_symbol: "lust_sys_sig_read_now", params: &[S::I32, S::VecU8Mut], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_raise", c_symbol: "lust_sys_sig_raise", params: &[S::I32], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_restore_raise", c_symbol: "lust_sys_sig_restore_raise", params: &[S::I32], ret: S::I32, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_exit", c_symbol: "lust_sys_sig_exit", params: &[S::I32], ret: S::Never, allowed: &[C::SignalHook], implemented: true },
    IntrinsicDef { name: "sys_sig_abort", c_symbol: "lust_sys_sig_abort", params: &[], ret: S::Never, allowed: &[C::SignalHook], implemented: true },
    // The Formatter's alignment as `rt::Alignment` encodes it (0 left,
    // 1 right, 2 center, 3 none written), for Debug impls that pad by
    // hand like `Duration`'s (W-STD-C; runtime/stdc.c).
    IntrinsicDef { name: "fmt_align", c_symbol: "lust_fmt_align", params: &[S::FmtMut], ret: S::U32, allowed: CORE_STD, implemented: true },
    // `std::panic` hooks (W-UNWIND; runtime/panic.c): whether a custom
    // hook is installed, and std's default hook text (file, line, column,
    // message) for the hook `take_hook` hands out.
    IntrinsicDef { name: "panic_hook_custom", c_symbol: "lust_hook_custom", params: &[S::Bool], ret: S::Unit, allowed: ONLY_STD, implemented: true },
    // core's `BorrowedCursor::advance_checked` assert (`io::copy` with a
    // `Read` impl that reports more bytes than its buffer holds).
    IntrinsicDef { name: "panic_read_buf_overrun", c_symbol: "lust_panic_read_buf_overrun", params: &[], ret: S::Unit, allowed: ONLY_STD, implemented: true },
    IntrinsicDef {
        name: "panic_default_hook",
        c_symbol: "lust_hook_default",
        params: &[S::Str, S::U32, S::U32, S::Str],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: true,
    },
    // One char through the Unicode case tables (TRIAGE T8;
    // runtime/core.c `lust_char_case`), for `core::char`'s
    // `ToLowercase` and `ToUppercase`: the mapped code points (one
    // to three, 21 bits each) in the low word, their count in the
    // high word.
    IntrinsicDef { name: "char_case", c_symbol: "lust_char_case", params: &[S::U32, S::Bool], ret: S::U128, allowed: LIB, implemented: true },
    // symlink(2) for `std::os::unix::fs::symlink` (TRIAGE T5):
    // 0, errno, or -1 for a path with a NUL byte (sys.h).
    IntrinsicDef { name: "sys_symlink", c_symbol: "lust_sys_symlink", params: &[S::Bytes, S::Bytes], ret: S::I32, allowed: ONLY_STD, implemented: true },
];

/// The intrinsic with this `core::intrinsics` name: its registry id.
pub fn intrinsic_by_name(name: &str) -> Option<u32> {
    INTRINSICS.iter().position(|d| d.name == name).map(|i| i as u32)
}

/// The registry row for an intrinsic id from check or IR.
pub fn intrinsic(id: u32) -> &'static IntrinsicDef {
    &INTRINSICS[id as usize]
}

/// One non-generic std fn the loader can route (section 9.2 S5). `path`
/// is the full Rust path a user writes. `mangled` is the name the fn
/// carries inside a spliced one-crate compile, so it can never collide
/// with a user fn of the same short name. `trigger` is the byte string
/// the driver scans for before it pays for a std load; a miss only costs
/// the old `L0505` module-path reject, never a wrong accept.
pub struct StdFnDef {
    pub path: &'static [&'static str],
    pub mangled: &'static str,
    pub trigger: &'static str,
    pub krate: ShippedCrate,
    pub implemented: bool,
}

/// The source std fns known to the loader. The loader checks that every
/// `implemented` row has a matching fn in `library/` source at load;
/// a mismatch is an installation error, like a missing lang item.
pub const STD_FNS: &[StdFnDef] = &[
    StdFnDef {
        path: &["std", "process", "exit"],
        mangled: "__lust_std_process_exit",
        trigger: "process::exit",
        krate: C::Std,
        implemented: true,
    },
    // Declared surface only (section 3.1): real std has this fn, lust std
    // has no body yet, so a call rejects with L0640 instead of "no such
    // path". The body lands with W-STD (it needs the abort runtime hook).
    StdFnDef {
        path: &["std", "process", "abort"],
        mangled: "__lust_std_process_abort",
        trigger: "process::abort",
        krate: C::Std,
        implemented: false,
    },
];

/// The std types lust knows by name that are not in the prelude
/// (W-STD-A): a module names one only after a `use` of its std path
/// or a glob of its std module, as in Rust. (crates, module, name).
pub const STD_IMPORTED_TYPES: &[(&[&str], &str, &str)] = &[
    (&["std", "alloc"], "rc", "Rc"),
    (&["std", "alloc"], "rc", "Weak"),
    (&["std", "core"], "cell", "RefCell"),
    (&["std", "core"], "cell", "Cell"),
    (&["std", "core"], "cell", "Ref"),
    (&["std", "core"], "cell", "RefMut"),
    (&["std", "core"], "cell", "BorrowError"),
    (&["std", "core"], "cell", "BorrowMutError"),
    (&["std", "core"], "cmp", "Ordering"),
    (&["std", "core"], "ops", "Bound"),
    (&["std"], "process", "ExitCode"),
    (&["std", "core"], "str", "Utf8Error"),
    (&["std", "alloc"], "string", "FromUtf8Error"),
    (&["std", "core"], "num", "NonZero"),
    (&["std", "core"], "num", "NonZeroU8"),
    (&["std", "core"], "num", "NonZeroU16"),
    (&["std", "core"], "num", "NonZeroU32"),
    (&["std", "core"], "num", "NonZeroU64"),
    (&["std", "core"], "num", "NonZeroU128"),
    (&["std", "core"], "num", "NonZeroUsize"),
    (&["std", "core"], "num", "NonZeroI8"),
    (&["std", "core"], "num", "NonZeroI16"),
    (&["std", "core"], "num", "NonZeroI32"),
    (&["std", "core"], "num", "NonZeroI64"),
    (&["std", "core"], "num", "NonZeroI128"),
    (&["std", "core"], "num", "NonZeroIsize"),
];

/// The std types under `std::sync::mpsc` lust knows by name besides the
/// sync types (ty/sync.rs): the synthetic error Adts (W-THREADS).
pub const STD_MPSC_ADTS: &[&str] = &["RecvError", "TryRecvError", "RecvTimeoutError"];

/// True when the glob `use` of `path` (`std::rc` in `use std::rc::*;`)
/// brings the std type `name` into scope. The sync types and
/// `atomic::Ordering` live in deeper modules (W-THREADS).
pub fn std_glob_imports(path: &[&str], name: &str) -> bool {
    let mut full = path.to_vec();
    full.push(name);
    STD_IMPORTED_TYPES
        .iter()
        .any(|&(crates, module, n)| n == name && path.len() == 2 && crates.contains(&path[0]) && path[1] == module)
        || crate::ty::sync::SyncTy::by_path(&full).is_some()
        || (name == "Ordering" && matches!(full.as_slice(), ["std" | "core", "sync", "atomic", "Ordering"]))
        || (STD_MPSC_ADTS.contains(&name) && path == ["std", "sync", "mpsc"])
        || (name == "TryLockError" && path == ["std", "sync"])
}

/// True when a glob of the std module `path` imports `name` and the
/// module is one of the sync or thread modules (W-THREADS): a sync
/// type, `atomic::Ordering`, or a std free fn of that module.
pub fn std_sync_glob_imports(path: &[&str], name: &str) -> bool {
    let sync_module = matches!(path, ["std" | "core", "sync", ..] | ["std" | "core", "hint"]);
    sync_module && (std_glob_imports(path, name) || std_glob_fns(path).contains(&name))
}

/// The std free fns a glob `use` of `path` brings (`use std::sync::
/// atomic::*;` brings `fence`).
pub fn std_glob_fns(path: &[&str]) -> Vec<&'static str> {
    STD_FN_PATHS
        .iter()
        .filter_map(|row| {
            let parts: Vec<&str> = row.split('/').collect();
            (parts.len() == path.len() + 1 && parts.iter().zip(path).all(|(a, b)| a == b)).then(|| *parts.last().unwrap())
        })
        .collect()
}

/// Every std type name a glob `use` can bring (`std_glob_imports`).
pub fn std_glob_names() -> impl Iterator<Item = &'static str> {
    STD_IMPORTED_TYPES.iter().map(|t| t.2).chain(crate::ty::sync::SyncTy::ALL.iter().map(|k| k.name())).chain(STD_MPSC_ADTS.iter().copied()).chain(["TryLockError"])
}

/// The `use` path to suggest for a non-prelude std type lust knows by
/// name (`needs_std_use`), as `std::module::Name`.
pub fn std_use_hint(name: &str) -> String {
    if let Some(t) = STD_IMPORTED_TYPES.iter().find(|t| t.2 == name) {
        return format!("std::{}::{name}", t.1);
    }
    if STD_MPSC_ADTS.contains(&name) {
        return format!("std::sync::mpsc::{name}");
    }
    match crate::ty::sync::SyncTy::ALL.iter().find(|k| k.name() == name) {
        Some(k) => format!("std::{}::{name}", k.module().join("::")),
        None => format!("std::rc::{name}"),
    }
}

/// The variant names of the std enum at `path` (`std::cmp::Ordering`
/// gives Less, Equal, Greater), for a glob import of its variants.
pub fn std_enum_variants(path: &[&str]) -> Vec<&'static str> {
    STD_VARIANT_PATHS
        .iter()
        .filter_map(|row| {
            let parts: Vec<&str> = row.split('/').collect();
            (parts.len() == path.len() + 1 && parts.iter().zip(path).all(|(a, b)| a == b)).then(|| *parts.last().unwrap())
        })
        .collect()
}

/// True when `name` is one of `STD_IMPORTED_TYPES`.
pub fn needs_std_use(name: &str) -> bool {
    // A set built once: the resolver asks for every path it rewrites.
    type Names = std::collections::HashSet<&'static str, std::hash::BuildHasherDefault<crate::intern::FxHasher>>;
    static NAMES: std::sync::OnceLock<Names> = std::sync::OnceLock::new();
    let names = NAMES.get_or_init(|| {
        let mut set: Names = STD_IMPORTED_TYPES.iter().map(|&(_, _, n)| n).collect();
        set.extend(crate::ty::sync::SyncTy::ALL.iter().map(|k| k.name()));
        set.extend(STD_MPSC_ADTS.iter().copied());
        set
    });
    names.contains(name)
}

/// The methods std source defines on `Option` and `Result`
/// (library/core/src/{option,result}.rs, W-STD-A), sorted. A user
/// source that names none of them after a `.` or `::` (and no
/// implemented `STD_FNS` row) compiles without std source. The
/// loader test `lang_methods_match_source` keeps this list equal to
/// the methods the shipped files define.
pub const STD_LANG_METHODS: &[&str] = &[
    "and",
    "and_then",
    "as_deref",
    "as_deref_mut",
    "as_mut",
    "as_mut_slice",
    "as_ref",
    "as_slice",
    "cloned",
    "copied",
    "err",
    "expect",
    "expect_err",
    "filter",
    "flatten",
    "get_or_insert",
    "get_or_insert_default",
    "get_or_insert_with",
    "insert",
    "inspect",
    "inspect_err",
    "is_err",
    "is_err_and",
    "is_none",
    "is_none_or",
    "is_ok",
    "is_ok_and",
    "is_some",
    "is_some_and",
    "map",
    "map_err",
    "map_or",
    "map_or_default",
    "map_or_else",
    "ok",
    "ok_or",
    "ok_or_else",
    "or",
    "or_else",
    "replace",
    "take",
    "take_if",
    "transpose",
    "unwrap",
    "unwrap_err",
    "unwrap_or",
    "unwrap_or_default",
    "unwrap_or_else",
    "unzip",
    "xor",
    "zip",
];

/// The std source one compile needs: found by `std_needs`, read by
/// the std splice (`StdLoad::splice`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StdNeeds {
    /// An implemented `STD_FNS` row's trigger occurs.
    pub fns: bool,
    /// A `STD_LANG_METHODS` name follows a `.` or a `::`.
    pub methods: bool,
    /// The std source modules that can be named, one bit per
    /// `stdmods::STD_MODULES` row (`stdmods::needs`).
    pub modules: u32,
}

impl StdNeeds {
    pub fn any(self) -> bool {
        self.fns || self.methods || self.modules != 0
    }
}

/// The std source `src` can mention: implemented `STD_FNS` triggers,
/// and each `STD_LANG_METHODS` name that follows a `.` or a `::`
/// (whitespace allowed between). Plain byte scans with no allocation:
/// this runs on every compile. A miss (a name only a macro builds)
/// costs a "no method" reject, never a wrong accept.
pub fn std_needs(src: &str) -> StdNeeds {
    std_needs_known(src, crate::stdmods::needs(src))
}

/// `std_needs` for a caller that knows `stdmods::needs(src)` already:
/// routing finds it in its parallel pass (`route_root_std`).
pub fn std_needs_known(src: &str, modules: u32) -> StdNeeds {
    // Bit n of FIRST[c]: some method name starts with byte c and has
    // length n. It turns away almost every other name (`push`, `len`)
    // before a search, which keeps the scan near memory speed.
    const FIRST: [u32; 128] = {
        let mut t = [0u32; 128];
        let mut i = 0;
        while i < STD_LANG_METHODS.len() {
            let n = STD_LANG_METHODS[i].as_bytes();
            t[n[0] as usize] |= 1 << n.len();
            i += 1;
        }
        t
    };
    let b = src.as_bytes();
    let named_at = |mut j: usize| -> bool {
        while j < b.len() && b[j].is_ascii_whitespace() {
            j += 1;
        }
        let start = j;
        if j >= b.len() || b[j] >= 128 || FIRST[b[j] as usize] == 0 {
            return false;
        }
        while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
            j += 1;
        }
        let len = j - start;
        len < 32 && FIRST[b[start] as usize] & (1 << len) != 0 && STD_LANG_METHODS.binary_search(&&src[start..j]).is_ok()
    };
    // `match_indices` on one char uses std's memchr searcher, much
    // faster than a byte loop (or a two-byte `"::"` search).
    let methods = src.match_indices('.').any(|(i, _)| named_at(i + 1))
        || src.match_indices(':').any(|(i, _)| b.get(i + 1) == Some(&b':') && named_at(i + 2));
    StdNeeds { fns: STD_FNS.iter().any(|d| d.implemented && src.contains(d.trigger)), methods, modules }
}

/// True if `src` can mention an implemented source std fn or a std
/// method of `Option`/`Result`, so the driver must load std before it
/// compiles.
pub fn needs_std_load(src: &str) -> bool {
    std_needs(src).any()
}

/// What namespace a canonical std path names its item in. A path
/// outside the tables below is not a std item lust knows by full
/// path: check rejects it instead of trusting its last segment
/// (rule zero: `std::option::Vec` must not mean `Vec`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StdPathKind {
    Type,
    Trait,
    Fn,
    Macro,
    Variant,
}

/// Canonical std paths lust can mean by full path, as
/// `crate/module/Name`. `std` re-exports the `core` and `alloc`
/// rows. Only rows whose item lust supports (or rejects by name,
/// like `HashMap`) belong here; a `use` rename of a row binds the
/// new name to the row's path (resolve), and check trusts a
/// written `std::...` path only when it is a row.
const STD_TYPE_PATHS: &[&str] = &[
    "core/option/Option",
    "std/option/Option",
    "core/result/Result",
    "std/result/Result",
    // std's alias `Result<T, Box<dyn Any + Send>>` (R26; check resolves it).
    "std/thread/Result",
    "alloc/string/String",
    "std/string/String",
    "alloc/vec/Vec",
    "std/vec/Vec",
    "alloc/boxed/Box",
    "std/boxed/Box",
    "alloc/rc/Rc",
    "std/rc/Rc",
    "alloc/rc/Weak",
    "std/rc/Weak",
    "alloc/sync/Arc",
    "std/sync/Arc",
    "core/cell/Cell",
    "std/cell/Cell",
    "core/cell/RefCell",
    "std/cell/RefCell",
    "core/cell/Ref",
    "std/cell/Ref",
    "core/cell/RefMut",
    "std/cell/RefMut",
    "core/cell/BorrowError",
    "std/cell/BorrowError",
    "core/cell/BorrowMutError",
    "std/cell/BorrowMutError",
    "core/cmp/Ordering",
    "std/cmp/Ordering",
    "core/ops/Bound",
    "std/ops/Bound",
    "std/process/ExitCode",
    "core/str/Utf8Error",
    "std/str/Utf8Error",
    "std/sync/mpsc/RecvError",
    "std/sync/mpsc/TrySendError",
    "std/sync/WaitTimeoutResult",
    "std/sync/TryLockError",
    "std/sync/mpsc/TryRecvError",
    "std/sync/mpsc/RecvTimeoutError",
    "alloc/string/FromUtf8Error",
    "std/string/FromUtf8Error",
    "core/any/TypeId",
    "std/any/TypeId",
    "core/panic/Location",
    "std/panic/Location",
    "std/collections/HashMap",
    "std/collections/HashSet",
    "alloc/collections/BTreeMap",
    "std/collections/BTreeMap",
    "core/fmt/Formatter",
    "std/fmt/Formatter",
    "core/fmt/Arguments",
    "std/fmt/Arguments",
    "core/fmt/Result",
    "std/fmt/Result",
    "core/fmt/Error",
    "std/fmt/Error",
    "core/fmt/DebugStruct",
    "std/fmt/DebugStruct",
    "core/fmt/DebugTuple",
    "std/fmt/DebugTuple",
    "core/fmt/DebugList",
    "std/fmt/DebugList",
    "core/fmt/DebugSet",
    "std/fmt/DebugSet",
    "core/fmt/DebugMap",
    "std/fmt/DebugMap",
    "core/sync/atomic/Ordering",
    "std/sync/atomic/Ordering",
    "std/borrow/Cow",
    "alloc/borrow/Cow",
    "std/vec/IntoIter",
    "alloc/vec/IntoIter",
    "std/collections/hash_map/IntoIter",
    "std/collections/hash_map/IntoKeys",
    "std/collections/hash_map/IntoValues",
    "std/collections/hash_set/IntoIter",
    "std/collections/hash_map/HashMap",
    "std/collections/hash_map/Entry",
    "std/collections/hash_set/HashSet",
    "std/collections/hash_map/RandomState",
    "std/collections/hash_map/DefaultHasher",
    "std/hash/RandomState",
    "std/hash/DefaultHasher",
    "std/hash/BuildHasherDefault",
    "core/hash/BuildHasherDefault",
    "core/mem/MaybeUninit",
    "std/mem/MaybeUninit",
    "core/num/NonZero",
    "std/num/NonZero",
    "core/num/NonZeroU8",
    "std/num/NonZeroU8",
    "core/num/NonZeroU16",
    "std/num/NonZeroU16",
    "core/num/NonZeroU32",
    "std/num/NonZeroU32",
    "core/num/NonZeroU64",
    "std/num/NonZeroU64",
    "core/num/NonZeroU128",
    "std/num/NonZeroU128",
    "core/num/NonZeroUsize",
    "std/num/NonZeroUsize",
    "core/num/NonZeroI8",
    "std/num/NonZeroI8",
    "core/num/NonZeroI16",
    "std/num/NonZeroI16",
    "core/num/NonZeroI32",
    "std/num/NonZeroI32",
    "core/num/NonZeroI64",
    "std/num/NonZeroI64",
    "core/num/NonZeroI128",
    "std/num/NonZeroI128",
    "core/num/NonZeroIsize",
    "std/num/NonZeroIsize",
    "core/num/TryFromIntError",
    "std/num/TryFromIntError",
    "core/num/IntErrorKind",
    "std/num/IntErrorKind",
    "core/char/CharTryFromError",
    "std/char/CharTryFromError",
    "core/char/TryFromCharError",
    "std/char/TryFromCharError",
    "core/convert/Infallible",
    "std/convert/Infallible",
    "core/num/ParseIntError",
    "std/num/ParseIntError",
    "core/num/ParseFloatError",
    "std/num/ParseFloatError",
    "core/str/ParseBoolError",
    "std/str/ParseBoolError",
    "core/char/ParseCharError",
    "std/char/ParseCharError",
    "core/array/TryFromSliceError",
    "std/array/TryFromSliceError",
    // The std iterator types of check/stdtypes.rs (`iter_by_path`),
    // so a `use` of one binds and expands like the full path (T5).
    "alloc/string/Drain",
    "alloc/vec/Drain",
    "core/array/IntoIter",
    "core/iter/Chain",
    "core/iter/Cloned",
    "core/iter/Copied",
    "core/iter/Enumerate",
    "core/iter/Filter",
    "core/iter/FilterMap",
    "core/iter/Flatten",
    "core/iter/Inspect",
    "core/iter/Map",
    "core/iter/MapWhile",
    "core/iter/Peekable",
    "core/iter/RepeatN",
    "core/iter/Rev",
    "core/iter/Skip",
    "core/iter/SkipWhile",
    "core/iter/StepBy",
    "core/iter/Take",
    "core/iter/TakeWhile",
    "core/iter/Zip",
    "core/ops/Range",
    "core/ops/RangeFrom",
    "core/ops/RangeFull",
    "core/ops/RangeInclusive",
    "core/ops/RangeTo",
    "core/ops/RangeToInclusive",
    "core/option/IntoIter",
    "core/option/Iter",
    "core/option/IterMut",
    "core/result/IntoIter",
    "core/result/Iter",
    "core/result/IterMut",
    "core/slice/Chunks",
    "core/slice/ChunksExact",
    "core/slice/ChunksExactMut",
    "core/slice/ChunksMut",
    "core/slice/Iter",
    "core/slice/IterMut",
    "core/slice/Windows",
    "core/str/Bytes",
    "core/str/CharIndices",
    "core/str/Chars",
    "core/str/Lines",
    "core/str/RSplit",
    "core/str/RSplitN",
    "core/str/RSplitTerminator",
    "core/str/Split",
    "core/str/SplitAsciiWhitespace",
    "core/str/SplitInclusive",
    "core/str/SplitN",
    "core/str/SplitTerminator",
    "core/str/SplitWhitespace",
    "core/str/Utf8Chunk",
    "core/str/Utf8Chunks",
    "std/array/IntoIter",
    "std/collections/hash_map/Iter",
    "std/collections/hash_map/IterMut",
    "std/collections/hash_map/Keys",
    "std/collections/hash_map/Values",
    "std/collections/hash_map/ValuesMut",
    "std/collections/hash_set/Iter",
    "std/iter/Chain",
    "std/iter/Cloned",
    "std/iter/Copied",
    "std/iter/Enumerate",
    "std/iter/Filter",
    "std/iter/FilterMap",
    "std/iter/Flatten",
    "std/iter/Inspect",
    "std/iter/Map",
    "std/iter/MapWhile",
    "std/iter/Peekable",
    "std/iter/RepeatN",
    "std/iter/Rev",
    "std/iter/Skip",
    "std/iter/SkipWhile",
    "std/iter/StepBy",
    "std/iter/Take",
    "std/iter/TakeWhile",
    "std/iter/Zip",
    "std/ops/Range",
    "std/ops/RangeFrom",
    "std/ops/RangeFull",
    "std/ops/RangeInclusive",
    "std/ops/RangeTo",
    "std/ops/RangeToInclusive",
    "std/option/IntoIter",
    "std/option/Iter",
    "std/option/IterMut",
    "std/result/IntoIter",
    "std/result/Iter",
    "std/result/IterMut",
    "std/slice/Chunks",
    "std/slice/ChunksExact",
    "std/slice/ChunksExactMut",
    "std/slice/ChunksMut",
    "std/slice/Iter",
    "std/slice/IterMut",
    "std/slice/Windows",
    "std/str/Bytes",
    "std/str/CharIndices",
    "std/str/Chars",
    "std/env/Args",
    "std/str/Lines",
    "std/str/RSplit",
    "std/str/RSplitN",
    "std/str/RSplitTerminator",
    "std/str/Split",
    "std/str/SplitAsciiWhitespace",
    "std/str/SplitInclusive",
    "std/str/SplitN",
    "std/str/SplitTerminator",
    "std/str/SplitWhitespace",
    "std/str/Utf8Chunk",
    "std/str/Utf8Chunks",
    "std/string/Drain",
    "std/sync/mpsc/IntoIter",
    "std/sync/mpsc/Iter",
    "std/sync/mpsc/TryIter",
    "std/vec/Drain",
];

const STD_TRAIT_PATHS: &[&str] = &[
    "core/any/Any",
    "std/any/Any",
    "core/clone/Clone",
    "std/clone/Clone",
    "core/cmp/PartialEq",
    "std/cmp/PartialEq",
    "core/cmp/Eq",
    "std/cmp/Eq",
    "core/cmp/PartialOrd",
    "std/cmp/PartialOrd",
    "core/cmp/Ord",
    "std/cmp/Ord",
    "core/convert/From",
    "std/convert/From",
    "core/convert/Into",
    "std/convert/Into",
    "core/convert/AsRef",
    "std/convert/AsRef",
    "core/convert/AsMut",
    "std/convert/AsMut",
    "core/convert/TryFrom",
    "std/convert/TryFrom",
    "core/convert/TryInto",
    "std/convert/TryInto",
    "core/default/Default",
    "std/default/Default",
    "core/fmt/Debug",
    "std/fmt/Debug",
    "core/fmt/Display",
    "std/fmt/Display",
    "core/fmt/Write",
    "std/fmt/Write",
    "core/hash/Hash",
    "std/hash/Hash",
    "core/hash/Hasher",
    "std/hash/Hasher",
    "core/hash/BuildHasher",
    "std/hash/BuildHasher",
    "core/iter/Iterator",
    "std/iter/Iterator",
    "core/iter/IntoIterator",
    "std/iter/IntoIterator",
    "core/iter/FromIterator",
    "std/iter/FromIterator",
    "core/iter/Extend",
    "std/iter/Extend",
    "core/str/FromStr",
    "std/str/FromStr",
    "core/iter/ExactSizeIterator",
    "std/iter/ExactSizeIterator",
    "core/iter/DoubleEndedIterator",
    "std/iter/DoubleEndedIterator",
    "core/ops/RangeBounds",
    "std/ops/RangeBounds",
    "core/marker/Sized",
    "std/marker/Sized",
    "core/marker/Copy",
    "std/marker/Copy",
    "core/marker/Send",
    "std/marker/Send",
    "core/marker/Sync",
    "std/marker/Sync",
    "core/marker/Unpin",
    "std/marker/Unpin",
    "core/ops/Add",
    "std/ops/Add",
    "core/ops/Sub",
    "std/ops/Sub",
    "core/ops/Mul",
    "std/ops/Mul",
    "core/ops/Div",
    "std/ops/Div",
    "core/ops/Rem",
    "std/ops/Rem",
    "core/ops/Neg",
    "std/ops/Neg",
    "core/ops/Not",
    "std/ops/Not",
    "core/ops/BitAnd",
    "std/ops/BitAnd",
    "core/ops/BitOr",
    "std/ops/BitOr",
    "core/ops/BitXor",
    "std/ops/BitXor",
    "core/ops/Shl",
    "std/ops/Shl",
    "core/ops/Shr",
    "std/ops/Shr",
    "core/ops/AddAssign",
    "std/ops/AddAssign",
    "core/ops/SubAssign",
    "std/ops/SubAssign",
    "core/ops/MulAssign",
    "std/ops/MulAssign",
    "core/ops/DivAssign",
    "std/ops/DivAssign",
    "core/ops/RemAssign",
    "std/ops/RemAssign",
    "core/ops/BitAndAssign",
    "std/ops/BitAndAssign",
    "core/ops/BitOrAssign",
    "std/ops/BitOrAssign",
    "core/ops/BitXorAssign",
    "std/ops/BitXorAssign",
    "core/ops/ShlAssign",
    "std/ops/ShlAssign",
    "core/ops/ShrAssign",
    "std/ops/ShrAssign",
    "core/ops/Index",
    "std/ops/Index",
    "core/ops/IndexMut",
    "std/ops/IndexMut",
    "core/ops/Drop",
    "std/ops/Drop",
    "core/ops/Deref",
    "std/ops/Deref",
    "core/ops/DerefMut",
    "std/ops/DerefMut",
    "core/ops/Fn",
    "std/ops/Fn",
    "core/ops/FnMut",
    "std/ops/FnMut",
    "core/ops/FnOnce",
    "std/ops/FnOnce",
    "alloc/string/ToString",
    "std/string/ToString",
    "alloc/borrow/ToOwned",
    "std/borrow/ToOwned",
    "core/borrow/Borrow",
    "std/borrow/Borrow",
    "core/borrow/BorrowMut",
    "std/borrow/BorrowMut",
];

const STD_FN_PATHS: &[&str] = &[
    "core/mem/drop",
    "std/mem/drop",
    "core/mem/swap",
    "std/mem/swap",
    "core/iter/repeat_n",
    "std/iter/repeat_n",
    "core/array/from_fn",
    "std/array/from_fn",
    "core/mem/replace",
    "std/mem/replace",
    "core/mem/take",
    "std/mem/take",
    "core/mem/forget",
    "std/mem/forget",
    "core/mem/size_of",
    "std/mem/size_of",
    "core/mem/align_of",
    "std/mem/align_of",
    "core/mem/size_of_val",
    "std/mem/size_of_val",
    "core/mem/align_of_val",
    "std/mem/align_of_val",
    "core/mem/needs_drop",
    "std/mem/needs_drop",
    "core/cmp/max",
    "std/cmp/max",
    "core/cmp/min",
    "std/cmp/min",
    "core/str/from_utf8",
    "std/str/from_utf8",
    "std/env/args",
    "std/process/exit",
    "std/process/abort",
    "core/sync/atomic/fence",
    "std/sync/atomic/fence",
    "core/sync/atomic/compiler_fence",
    "std/sync/atomic/compiler_fence",
    "core/hint/spin_loop",
    "std/hint/spin_loop",
    "core/hint/black_box",
    "std/hint/black_box",
    "std/thread/spawn",
    "std/thread/current",
    "std/thread/yield_now",
    "std/thread/panicking",
    "std/thread/scope",
    "std/sync/mpsc/channel",
    "std/sync/mpsc/sync_channel",
    "std/thread/sleep",
    "std/panic/catch_unwind",
    "std/panic/resume_unwind",
    "std/panic/panic_any",
    "core/any/type_name",
    "std/any/type_name",
    "alloc/fmt/format",
    "std/fmt/format",
    "core/slice/from_ref",
    "std/slice/from_ref",
    "core/slice/from_mut",
    "std/slice/from_mut",
    "core/ptr/from_ref",
    "std/ptr/from_ref",
    "core/ptr/from_mut",
    "std/ptr/from_mut",
    "core/ptr/null",
    "std/ptr/null",
    "core/ptr/null_mut",
    "std/ptr/null_mut",
    "core/ptr/eq",
    "std/ptr/eq",
    "core/ptr/addr_eq",
    "std/ptr/addr_eq",
];

const STD_MACRO_PATHS: &[&str] = &[
    "alloc/vec",
    "std/vec",
    "alloc/format",
    "std/format",
    "core/panic",
    "std/panic",
    "core/assert",
    "std/assert",
    "core/assert_eq",
    "std/assert_eq",
    "core/assert_ne",
    "std/assert_ne",
    "core/todo",
    "std/todo",
    "core/unreachable",
    "std/unreachable",
    "core/matches",
    "std/matches",
    "core/write",
    "std/write",
    "core/writeln",
    "std/writeln",
    "std/print",
    "std/println",
    "std/eprint",
    "std/eprintln",
];

const STD_VARIANT_PATHS: &[&str] = &[
    "std/collections/hash_map/Entry/Occupied",
    "std/collections/hash_map/Entry/Vacant",
    "core/option/Option/Some",
    "std/option/Option/Some",
    "core/option/Option/None",
    "std/option/Option/None",
    "core/result/Result/Ok",
    "std/result/Result/Ok",
    "core/result/Result/Err",
    "std/result/Result/Err",
    "core/cmp/Ordering/Less",
    "std/cmp/Ordering/Less",
    "core/cmp/Ordering/Equal",
    "std/cmp/Ordering/Equal",
    "core/cmp/Ordering/Greater",
    "std/cmp/Ordering/Greater",
    "core/ops/Bound/Included",
    "std/ops/Bound/Included",
    "core/ops/Bound/Excluded",
    "std/ops/Bound/Excluded",
    "core/ops/Bound/Unbounded",
    "std/ops/Bound/Unbounded",
    "core/sync/atomic/Ordering/Relaxed",
    "std/sync/atomic/Ordering/Relaxed",
    "core/sync/atomic/Ordering/Release",
    "std/sync/atomic/Ordering/Release",
    "core/sync/atomic/Ordering/Acquire",
    "std/sync/atomic/Ordering/Acquire",
    "core/sync/atomic/Ordering/AcqRel",
    "std/sync/atomic/Ordering/AcqRel",
    "core/sync/atomic/Ordering/SeqCst",
    "std/sync/atomic/Ordering/SeqCst",
    "std/sync/mpsc/TryRecvError/Empty",
    "std/sync/mpsc/TryRecvError/Disconnected",
    "std/sync/mpsc/RecvTimeoutError/Timeout",
    "std/sync/mpsc/RecvTimeoutError/Disconnected",
    "std/sync/TryLockError/Poisoned",
    "std/sync/TryLockError/WouldBlock",
];

/// True for a trait of the Rust 2024 prelude (and the prelude's
/// marker traits), which a bare name reaches with no `use`.
pub fn is_prelude_trait(name: &str) -> bool {
    matches!(
        name,
        "Copy"
            | "Send"
            | "Sized"
            | "Sync"
            | "Unpin"
            | "Drop"
            | "Fn"
            | "FnMut"
            | "FnOnce"
            | "AsMut"
            | "AsRef"
            | "From"
            | "Into"
            | "DoubleEndedIterator"
            | "ExactSizeIterator"
            | "Extend"
            | "IntoIterator"
            | "Iterator"
            | "Clone"
            | "Default"
            | "Eq"
            | "Ord"
            | "PartialEq"
            | "PartialOrd"
            | "ToOwned"
            | "ToString"
            | "TryFrom"
            | "TryInto"
            | "FromIterator"
            | "Future"
            | "IntoFuture"
    )
}

/// The std module of a non-prelude trait lust knows by name, for the
/// import hint of a bare name.
pub fn std_trait_module(name: &str) -> Option<&'static str> {
    STD_TRAIT_PATHS.iter().find_map(|row| {
        let mut parts = row.split('/');
        let (krate, module, n) = (parts.next()?, parts.next()?, parts.next()?);
        (krate == "std" && n == name && parts.next().is_none()).then_some(module)
    })
}

fn std_row_eq(row: &str, path: &[&str]) -> bool {
    row.split('/').eq(path.iter().copied())
}

/// The kind a full written path (`core/mem/drop`) names, if the
/// path is a canonical std path in the tables above.
pub fn std_path_kind(path: &[&str]) -> Option<StdPathKind> {
    let mut find = |rows: &[&str], kind| rows.iter().any(|r| std_row_eq(r, path)).then_some(kind);
    find(STD_TYPE_PATHS, StdPathKind::Type)
        .or_else(|| crate::ty::sync::SyncTy::by_path(path).map(|_| StdPathKind::Type))
        .or_else(|| find(STD_TRAIT_PATHS, StdPathKind::Trait))
        .or_else(|| find(STD_FN_PATHS, StdPathKind::Fn))
        .or_else(|| find(STD_MACRO_PATHS, StdPathKind::Macro))
        .or_else(|| find(STD_VARIANT_PATHS, StdPathKind::Variant))
}

/// True when `path` names a std module: a shipped crate root, or a
/// proper prefix of a canonical std path. A `use` rename of a
/// module binds the new name to this path.
pub fn std_is_module_path(path: &[&str]) -> bool {
    if path.is_empty() {
        return false;
    }
    if path.len() == 1 {
        return matches!(path[0], "std" | "core" | "alloc");
    }
    let prefix_of = |row: &str| {
        let mut parts = row.split('/');
        path.iter().all(|p| parts.next() == Some(p)) && parts.next().is_some()
    };
    [STD_TYPE_PATHS, STD_TRAIT_PATHS, STD_FN_PATHS, STD_MACRO_PATHS, STD_VARIANT_PATHS].iter().any(|rows| rows.iter().any(|r| prefix_of(r)))
        || crate::ty::sync::type_rows().iter().any(|r| prefix_of(r))
}

/// Canonical std paths under a shipped platform module that the
/// platform crate does not define, so the compiler's std compat
/// handling keeps them (fx-stdos): `library/std/src/os.rs` defines
/// `std::os::unix::fs` with only `MetadataExt`, and before that
/// module existed every other item of `std::os::unix::fs` resolved
/// through the std alias path. A platform module must not hide
/// them: the resolver falls back to the alias handling for a row
/// here that the platform module lacks. Rows must name real std
/// items (rustc rejects the rest) and must not name an item the
/// platform crate defines.
const STD_PLATFORM_COMPAT_PATHS: &[&str] = &[
    "std/os/unix/fs/DirBuilderExt",
    "std/os/unix/fs/DirEntryExt",
    "std/os/unix/fs/FileExt",
    "std/os/unix/fs/FileTypeExt",
    "std/os/unix/fs/OpenOptionsExt",
    "std/os/unix/fs/chown",
    "std/os/unix/fs/fchown",
    "std/os/unix/fs/lchown",
    "std/os/unix/fs/symlink",
];

/// True when `path` is a row of `STD_PLATFORM_COMPAT_PATHS`: a std
/// item a shipped platform module does not define, which keeps the
/// std compat handling instead of an unresolved import.
pub fn std_platform_compat_path(path: &[&str]) -> bool {
    STD_PLATFORM_COMPAT_PATHS.iter().any(|r| std_row_eq(r, path))
}

/// True for `std::primitive::u8` style paths: a primitive type
/// name under the `primitive` module of `std` or `core`.
pub fn std_is_primitive_path(path: &[&str]) -> bool {
    path.len() == 3
        && matches!(path[0], "std" | "core")
        && path[1] == "primitive"
        && matches!(
            path[2],
            "bool"
                | "char"
                | "str"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
                | "f16"
                | "f32"
                | "f64"
                | "f128"
                | "never"
                | "unit"
                | "tuple"
                | "array"
                | "slice"
                | "pointer"
                | "reference"
                | "fn"
        )
}

/// True for the names of the primitive types a type path can name.
pub fn is_primitive_type_name(name: &str) -> bool {
    matches!(
        name,
        "bool" | "char" | "str" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "f16" | "f32" | "f64" | "f128"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::GlobalTys;

    /// The table covers every lang item section 3.1 names, in enum order,
    /// with unique `#[lust_lang]` names.
    #[test]
    fn lang_table_covers_arch_list() {
        for (i, d) in LANG_ITEMS.iter().enumerate() {
            assert_eq!(d.item as usize, i, "row {} out of LangItem order", d.name);
            assert_eq!(lang_item_by_name(d.name), Some(d.item), "name {} must resolve once", d.name);
        }
        for name in [
            "option",
            "result",
            "string",
            "vec",
            "box",
            "rc",
            "arc",
            "unsafe_cell",
            "phantom_data",
            "iterator",
            "into_iterator",
            "drop",
            "deref",
            "fn",
            "sized",
            "send",
            "sync",
            "panic",
            "formatter",
            "exchange_malloc",
        ] {
            assert!(lang_item_by_name(name).is_some(), "missing lang item {name}");
        }
        // The Range family and the Fn family are one ARCH phrase each.
        assert_eq!(LANG_ITEMS.iter().filter(|d| d.name.starts_with("range")).count(), 6);
        assert_eq!(LANG_ITEMS.iter().filter(|d| d.name.starts_with("fn")).count(), 3);
    }

    /// Builtin-backed items resolve from `BuiltinDefs`, and every item
    /// marked required has a source today, so a load cannot fail on them.
    #[test]
    fn lang_items_resolve_builtins() {
        let g = GlobalTys::new();
        let b = *g.builtins();
        let items = LangItems::from_builtins(b);
        assert_eq!(items.get(LangItem::Option), Some(b.option));
        assert_eq!(items.get(LangItem::Result), Some(b.result));
        assert_eq!(items.get(LangItem::String), Some(b.string));
        assert_eq!(items.get(LangItem::Vec), Some(b.vec));
        assert_eq!(items.get(LangItem::Box), Some(b.boxed));
        assert_eq!(items.get(LangItem::Rc), Some(b.rc));
        assert!(items.required_missing().is_empty(), "required items must resolve: {:?}", items.required_missing());
    }

    /// The canonical std path rows are unique across kinds, and the
    /// lookup answers only for exact rows (never a wrong module).
    #[test]
    fn std_path_rows_are_unique_and_exact() {
        let all: Vec<&str> = [STD_TYPE_PATHS, STD_TRAIT_PATHS, STD_FN_PATHS, STD_MACRO_PATHS, STD_VARIANT_PATHS]
            .iter()
            .flat_map(|rows| rows.iter().copied())
            .collect();
        for (i, a) in all.iter().enumerate() {
            assert!(!a.is_empty());
            assert!(all.iter().skip(i + 1).all(|b| b != a), "duplicate std path row {a}");
        }
        assert_eq!(std_path_kind(&["std", "option", "Option"]), Some(StdPathKind::Type));
        assert_eq!(std_path_kind(&["core", "mem", "drop"]), Some(StdPathKind::Fn));
        assert_eq!(std_path_kind(&["std", "option", "Vec"]), None);
        assert_eq!(std_path_kind(&["core", "vec", "Vec"]), None);
        assert!(std_is_module_path(&["std", "mem"]));
        assert!(std_is_module_path(&["std"]));
        assert!(!std_is_module_path(&["std", "mem", "drop"]));
        assert!(!std_is_module_path(&["std", "nope"]));
        assert!(std_platform_compat_path(&["std", "os", "unix", "fs", "OpenOptionsExt"]));
        assert!(!std_platform_compat_path(&["std", "os", "unix", "fs", "MetadataExt"]));
        assert!(!std_platform_compat_path(&["std", "os", "unix", "fs", "NoSuchThing"]));
    }

    /// Registry rows are well formed: unique names, no empty allow list,
    /// and only implemented rows carry a C symbol.
    #[test]
    fn intrinsic_registry_is_well_formed() {
        for (i, d) in INTRINSICS.iter().enumerate() {
            assert_eq!(intrinsic_by_name(d.name), Some(i as u32), "duplicate intrinsic {}", d.name);
            assert!(!d.allowed.is_empty(), "intrinsic {} allows no crate", d.name);
            if d.implemented {
                assert!(!d.c_symbol.is_empty(), "implemented intrinsic {} needs a C symbol", d.name);
            }
        }
        // Every group in the section 3.2 table has at least one row.
        for name in [
            "alloc",
            "memcpy",
            "ptr_read",
            "fmt_f64",
            "panic",
            "thread_spawn",
            "mutex_lock",
            "atomic_load",
            "clock_now_raw",
            "fd_read",
            "exit",
            "arena_alloc",
        ] {
            assert!(intrinsic_by_name(name).is_some(), "missing intrinsic {name}");
        }
    }

    /// Privilege follows the row: user source (None) gets nothing, each
    /// adapter only its own cores, and `exit` is std-only.
    #[test]
    fn intrinsic_privilege_follows_the_row() {
        let exit = intrinsic(intrinsic_by_name("exit").unwrap());
        assert!(exit.allows(Some(ShippedCrate::Std)));
        assert!(!exit.allows(None));
        assert!(!exit.allows(Some(ShippedCrate::Core)));
        let arena = intrinsic(intrinsic_by_name("arena_alloc").unwrap());
        assert!(arena.allows(Some(ShippedCrate::Bumpalo)));
        assert!(!arena.allows(Some(ShippedCrate::Std)));
        assert!(!arena.allows(Some(ShippedCrate::Memchr)));
    }

    /// Shipped crate hashes are distinct, so privilege by disambiguator
    /// cannot alias two crates.
    #[test]
    fn shipped_crate_hashes_are_distinct() {
        let mut hashes: Vec<u64> = ShippedCrate::ALL.iter().map(|k| k.stable_hash().0).collect();
        hashes.sort_unstable();
        hashes.dedup();
        assert_eq!(hashes.len(), ShippedCrate::ALL.len());
    }

    /// The load trigger fires only for implemented source std fns.
    #[test]
    fn std_load_trigger() {
        assert!(needs_std_load("fn main() { std::process::exit(0); }"));
        assert!(!needs_std_load("fn main() { std::process::abort(); }"));
        assert!(!needs_std_load("fn main() { println!(\"hi\"); }"));
        assert!(needs_std_load("fn main() { let _ = Some(1).unwrap(); }"));
        assert!(needs_std_load("fn main() { let _ = x.is_ok(); }"));
        assert!(needs_std_load("fn main() { let _ = x\n    . unwrap(); }"));
        assert!(!needs_std_load("fn main() { let unwrap = 1; }"));
    }
}
