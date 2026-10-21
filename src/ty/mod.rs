// Semantic types, v2 (docs/ARCH.md section 2.1, serial refactor S3a).
//
// Types are interned to a `Ty` (u32). Signature types live in a global table that is frozen
// after collection. Each function body adds its own types in a local overlay, so bodies can
// be checked in parallel with no locks. Generic argument lists are slices, so they live in
// interned slice arenas next to the kind arena (`ArgsId`, `TysId`); with ids as payloads
// `TyKind` stays `Copy` and hashing a `Ty` stays O(1).
//
// `String`, `Vec<T>`, `Option<T>`, and `Chars` are `Adt` types with builtin defs
// (see `BuiltinDefs`), not `TyKind` cases. The special code paths for them in check, lower,
// and cgen stay until the minimal generic pipeline passes its gate (ARCH 9.3); those paths
// now reach the types through the compat helpers on `TyIntern` (`vec_elem`, `is_string_ty`,
// and kin), never by matching on a builtin `TyKind` case.
pub mod consteval;
pub mod constqual;
pub mod defs;
pub mod fmt;
pub mod hash;
pub mod iter;
pub mod lang;
pub mod layout;
pub mod sync;
pub use defs::{DefData, Defs, SigData};

use crate::def::{CrateId, DefId, StableCrateHash};
use crate::diag::Span;
use crate::check::spec;
use crate::intern::{FxMap, Sym};
use std::hash::Hash;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ty(pub u32);

/// The session-local dense index of a user struct or enum in `Program::adts`. `TyKind::Adt`
/// carries the stable `DefId`; this index stays as the compat handle that check side tables,
/// IR, and cgen use today. The store maps between the two (`local_adt_of`, `adt_ty`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdtId(pub u32);

/// Implemented by every interned id so one arena implementation serves all of them.
trait Idx: Copy + Eq + Hash {
    fn from_u32(v: u32) -> Self;
    fn to_u32(self) -> u32;
}

macro_rules! interned_id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub u32);
        impl Idx for $name {
            fn from_u32(v: u32) -> Self {
                $name(v)
            }
            fn to_u32(self) -> u32 {
                self.0
            }
        }
    };
}

impl Idx for Ty {
    fn to_u32(self) -> u32 {
        self.0
    }
    fn from_u32(v: u32) -> Self {
        Ty(v)
    }
}

interned_id! {
    /// An interned generic argument list (`&[GenericArg]`) in declared parameter order:
    /// lifetimes, types, and consts interleaved as written. One schema everywhere.
    ArgsId
}
interned_id! {
    /// An interned type list (`&[Ty]`): tuple elements and fn pointer inputs. Named apart
    /// from `ArgsId` so no code confuses a type list with a generic argument list.
    TysId
}
interned_id! {
    /// An interned const value (`ConstKind`): const generic args and const item values.
    /// The bounded const evaluator is ARCH 2.13; today only the interning exists.
    ConstId
}
interned_id! {
    /// An interned fn pointer signature, stored as `Binder<FnSig>`: `for<'a> fn(&'a T) -> U`
    /// is a binder of count 1 over a sig whose regions use `Bound(0)`.
    SigId
}
interned_id! {
    /// An interned `dyn` bound list (`DynBounds`).
    BoundsId
}
interned_id! {
    /// An interned associated-binding list: `(assoc DefId, GenericArg)` pairs, the
    /// `Item = u8` part of `Iterator<Item = u8>`. Every `TraitRef` has one, empty if unused.
    BindingsId
}
interned_id! {
    /// An interned elaborated param environment (`ParamEnvData`), owned by `defs::Defs`.
    ParamEnvId
}
interned_id! {
    /// The index of a generic parameter in the `Generics` of the item whose signature the
    /// type using it sits in.
    ParamId
}

/// The empty argument list, interned first in every global store.
pub const EMPTY_ARGS: ArgsId = ArgsId(0);
/// The empty type list, interned first in every global store.
pub const EMPTY_TYS: TysId = TysId(0);
/// The empty binding list, interned first in every global store.
pub const EMPTY_BINDINGS: BindingsId = BindingsId(0);

/// An associated item used in a projection: the `Assoc` in `<Self as Trait>::Assoc`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AssocId(pub DefId);

/// What an inference variable may bind to: any type, only an integer
/// type (an unsuffixed integer literal), or only a float type (an
/// unsuffixed float literal).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InferKind {
    General,
    Int,
    Float,
}

/// One body-local inference variable. Body-local only: an `Infer` type must never
/// enter the global store.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InferId(pub u32, pub InferKind);

impl InferId {
    /// The index into the checking body's variable table.
    pub fn index(self) -> u32 {
        self.0
    }
    /// True if this variable may only bind to an integer type.
    pub fn is_int(self) -> bool {
        self.1 == InferKind::Int
    }
    /// True if this variable may only bind to a float type.
    pub fn is_float(self) -> bool {
        self.1 == InferKind::Float
    }
}

#[allow(dead_code)] // The 128-bit variants are representation only until W-CORELANG.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    // Two-word values in codegen (tcc has no __int128); suffix, name, and
    // literal support landed with W-CORELANG in wave A. Variants stay at
    // the end (ARCH 9.2 freeze). Literals above u64::MAX still fail to lex.
    I128,
    U128,
}

impl IntTy {
    pub const ALL: [IntTy; 12] = [
        IntTy::I8,
        IntTy::I16,
        IntTy::I32,
        IntTy::I64,
        IntTy::Isize,
        IntTy::U8,
        IntTy::U16,
        IntTy::U32,
        IntTy::U64,
        IntTy::Usize,
        IntTy::I128,
        IntTy::U128,
    ];
    /// The integer types this compiler supports today (the subset of `ALL` up to 64 bits).
    pub const ALL_SUPPORTED: [IntTy; 12] = [
        IntTy::I8,
        IntTy::I16,
        IntTy::I32,
        IntTy::I64,
        IntTy::Isize,
        IntTy::U8,
        IntTy::U16,
        IntTy::U32,
        IntTy::U64,
        IntTy::Usize,
        IntTy::I128,
        IntTy::U128,
    ];
    pub fn signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::Isize | IntTy::I128)
    }
    /// The same-width integer type of the other signedness
    /// (`u32` <-> `i32`), for `cast_signed` and `cast_unsigned`.
    pub fn counterpart(self) -> IntTy {
        use IntTy::*;
        match self {
            I8 => U8,
            I16 => U16,
            I32 => U32,
            I64 => U64,
            Isize => Usize,
            I128 => U128,
            U8 => I8,
            U16 => I16,
            U32 => I32,
            U64 => I64,
            Usize => Isize,
            U128 => I128,
        }
    }
    pub fn bits(self) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            IntTy::I128 | IntTy::U128 => 128,
            _ => 64,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::Isize => "isize",
            IntTy::U8 => "u8",
            IntTy::U16 => "u16",
            IntTy::U32 => "u32",
            IntTy::U64 => "u64",
            IntTy::Usize => "usize",
            IntTy::I128 => "i128",
            IntTy::U128 => "u128",
        }
    }
    /// Largest value, as u64. Used for literal range checks. The 128-bit types saturate:
    /// no literal can carry them yet, and their real range check lands with W-CORELANG.
    pub fn max(self) -> u64 {
        if self.bits() >= 128 {
            u64::MAX
        } else if self.signed() {
            (1u64 << (self.bits() - 1)) - 1
        } else if self.bits() == 64 {
            u64::MAX
        } else {
            (1u64 << self.bits()) - 1
        }
    }
    /// Largest value, as u128. The full-width version of `max`.
    pub fn max128(self) -> u128 {
        if self.signed() {
            if self.bits() >= 128 { i128::MAX as u128 } else { (1u128 << (self.bits() - 1)) - 1 }
        } else if self.bits() >= 128 {
            u128::MAX
        } else {
            (1u128 << self.bits()) - 1
        }
    }
    pub fn from_suffix(s: crate::lexer::IntSuffix) -> IntTy {
        use crate::lexer::IntSuffix as S;
        match s {
            S::I8 => IntTy::I8,
            S::I16 => IntTy::I16,
            S::I32 => IntTy::I32,
            S::I64 => IntTy::I64,
            S::Isize => IntTy::Isize,
            S::U8 => IntTy::U8,
            S::U16 => IntTy::U16,
            S::U32 => IntTy::U32,
            S::U64 => IntTy::U64,
            S::Usize => IntTy::Usize,
            S::I128 => IntTy::I128,
            S::U128 => IntTy::U128,
        }
    }
}

/// Floating point types (W-CORELANG wave A).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    /// The Rust name of this float type.
    pub fn name(self) -> &'static str {
        match self {
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
        }
    }
}

/// Reference mutability: `&T` is `Shared`, `&mut T` is `Mut`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mut {
    Shared,
    Mut,
}

impl Mut {
    /// The `Mut` for an AST `mut` flag.
    pub fn from_bool(mutable: bool) -> Mut {
        if mutable { Mut::Mut } else { Mut::Shared }
    }
    /// True for `&mut`.
    pub fn is_mut(self) -> bool {
        self == Mut::Mut
    }
}

/// A region (lifetime). Section 5 of ARCH owns the rules; this is the frozen form.
/// In milestone 4 every region in a checked type is `Erased`; the other forms exist so
/// signatures, binders, and proofs can be written against the final representation.
#[allow(dead_code)] // Non-erased forms are constructed from milestone 6 (and in unit tests).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Region {
    /// `'static`.
    Static,
    /// A lifetime parameter of the item whose signature the type sits in, by index
    /// among that item's lifetime params.
    Param(u32),
    /// A de Bruijn index into the nearest enclosing `Binder`: `for<'a, 'b>` binds
    /// indices 0 and 1 in order.
    Bound(u32),
    /// A fresh universal region that exists only during a higher-ranked proof (ARCH 5.5).
    /// It is distinct from every other region, never unifies with one, must not escape
    /// the proof, and is not an inference variable.
    Placeholder(u32),
    /// A body-local region inference variable (milestone 6).
    Infer(u32),
    /// No region information. The only form after borrow checking, at mono and codegen,
    /// and the only form milestone 4 produces.
    Erased,
}

/// One generic argument. An `ArgsId` list stores these in declared parameter order,
/// lifetimes, types, and consts interleaved as written: one schema everywhere.
#[allow(dead_code)] // Lifetime and const args are formed by generic collect in wave A.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
    Const(ConstId),
}

impl GenericArg {
    /// This argument as a type, if it is one.
    pub fn as_ty(self) -> Option<Ty> {
        match self {
            GenericArg::Ty(t) => Some(t),
            _ => None,
        }
    }
}

/// An interned const value. Aggregate const values join at the end when the bounded
/// const evaluator lands (ARCH 2.13); anything outside that bound in const position
/// is a reject there (the reserved const code of ARCH 2.13), not a new form here.
#[allow(dead_code)] // Formed by the const evaluator and const generics in wave A.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstKind {
    Int(u128),
    Bool(bool),
    Char(char),
    /// A const parameter of the current `Generics`, by param index.
    Param(u32),
    /// A body-local const inference variable. Never in the global store.
    Infer(u32),
}

/// A value under `for<'a, ...>`: `count` regions are bound, named inside `value` by
/// `Region::Bound(i)` de Bruijn indices. Only rank-1 binders exist: a `Binder` inside
/// a `Binder` value is a reject (ARCH 5.5). Instantiating a binder replaces
/// each `Bound(i)` with a fresh region var at a call site, or with a `Placeholder`
/// region in a proof; the two are never mixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Binder<T> {
    pub count: u32,
    pub value: T,
}

impl<T> Binder<T> {
    /// A binder with no bound regions, for values that are not higher-ranked.
    #[allow(dead_code)] // The spelling generic collect uses from wave A.
    pub fn plain(value: T) -> Binder<T> {
        Binder { count: 0, value }
    }
}

/// A fn pointer signature, interned as `Binder<FnSig>` under a `SigId`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FnSig {
    pub inputs: TysId,
    pub output: Ty,
    pub is_unsafe: bool,
    /// True for `extern "C"`. No other ABI is in the subset.
    pub extern_c: bool,
    /// W-BORROW3: for a fn pointer type that names a lifetime of the
    /// enclosing item (`fn(&mut Parser<'a>) -> Node`), bit `k` is set when
    /// region slot `k` of the signature (the borrow checker's slot order
    /// over the inputs, then the output) is that free region. Every other
    /// slot is `'static` where written, else late-bound. 0 for all other
    /// signatures.
    pub free_slots: u32,
    /// The free region of `free_slots`: `Erased` in check's types, the
    /// item's lifetime (`Region::Param`) in region signatures.
    pub free_region: Region,
    /// Bit `k` is set when region slot `k` of the output (borrowck's slot
    /// order over the output alone) is the signature's one higher-ranked
    /// input region, as the pointer type writes it (elided, or `for<'a>
    /// fn(&'a D) -> (&'a U, &'static V)`): a closure coerced to it may
    /// return borrows of that input there (`ClosureInfo::bound_output`).
    /// 0 when the written output holds a projection.
    pub own_out: u32,
    /// The number of region slots of the written output (`own_out`'s
    /// width). A type parameter there has none; when a substitution gives
    /// the output more slots, they came from a type argument and the mask
    /// no longer lines up, so `own_out` does not apply. `u8::MAX` when
    /// unknown (a pointer type lust builds, a free region, several input
    /// regions): every elided output slot is the one input's then.
    pub out_slots: u8,
    /// A `for<..>` binder lifetime written in several places
    /// (`for<'s> fn(&mut Ctx<'s>, &'s [u8]) -> Cow<'s, [u8]>`): four bits
    /// per region slot (borrowck's slot order over the inputs, then the
    /// output), slot `k`'s binder group in bits `4k..4k + 4`. Group 0 is
    /// none: the slot is its own late-bound region (an elided input), or
    /// as `free_slots` and `'static` say. Each group `g > 0` is one binder
    /// lifetime, the same region at all its slots. 0 for every signature
    /// elision can write.
    pub binders: u64,
    /// The number of region slots `binders` covers (the written
    /// signature's). A substitution that gives the signature another
    /// count moved the slots, so `binders` no longer lines up.
    pub binder_slots: u8,
}

impl FnSig {
    /// A signature with no free region (`free_slots` 0).
    pub fn plain(inputs: TysId, output: Ty) -> FnSig {
        FnSig { inputs, output, is_unsafe: false, extern_c: false, free_slots: 0, free_region: Region::Erased, own_out: 0, out_slots: u8::MAX, binders: 0, binder_slots: 0 }
    }

    /// The binder group of each of `slots` region slots (`binders`), or
    /// None when the signature has no shared binder, or its slots moved.
    pub fn binder_groups(&self, slots: usize) -> Option<Vec<u8>> {
        (self.binders != 0 && slots == self.binder_slots as usize).then(|| (0..slots).map(|k| (self.binders >> (4 * k) & 0xF) as u8).collect())
    }

    /// True when the output has `actual` region slots and the written one
    /// had another count (`out_slots`): a type argument filled them
    /// (`fn(&u8) -> T` with `T = &'x u8`), so they are no binder's
    /// (rustc E0308 "one type is more general than the other" when a fn
    /// that returns its argument's borrow meets that type).
    pub fn out_substituted(&self, actual: usize) -> bool {
        self.free_slots == 0 && self.out_slots != u8::MAX && actual != self.out_slots as usize
    }
}

/// A trait reference: `Self` is `args[0]`. `bindings` is the interned list of
/// associated bindings written at the use (`Item = u8`, `Output = C`); no trait ref
/// exists without a place for its bindings, even when the list is empty.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TraitRef {
    pub def: DefId,
    pub args: ArgsId,
    pub bindings: BindingsId,
}

/// The equality facts of one associated binding: the assoc item, the trait args it
/// was written under (Self first), and the type it is bound to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AssocEqData {
    pub assoc: DefId,
    pub trait_args: ArgsId,
    pub ty: Ty,
}

/// One bound fact. Bounds written as `T: A + B`, in `where` clauses, and on assoc
/// types all become predicates in source order; source order is observable only in
/// error messages, and is kept anyway.
#[allow(dead_code)] // Formed by generic collect in wave A (and in unit tests).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    /// Binder count is 0 when the bound is not higher-ranked.
    Trait(Binder<TraitRef>),
    /// The equality stays under the binder of the bound that wrote it: the `Output`
    /// binding of `for<'a> Fn(&'a T) -> &'a U` lives inside the `for<'a>`. Moving an
    /// equality out of its binder loses the region and is a bug (ARCH 2.1, 2.5).
    AssocEq(Binder<AssocEqData>),
    Outlives(Region, Region),
    TypeOutlives(Ty, Region),
}

/// What sort of thing a generic parameter is. A const param carries its type.
#[allow(dead_code)] // Lifetime and const params are collected in later waves.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ParamKind {
    Lifetime,
    Type,
    Const(Ty),
}

/// One declared generic parameter.
#[allow(dead_code)] // Fields are read by generic collect and diagnostics in wave A.
#[derive(Clone, Copy, Debug)]
pub struct ParamDef {
    pub name: Sym,
    pub kind: ParamKind,
    pub span: Span,
}

/// The generics every def that can be generic owns: its params in declared order and
/// its written predicates in source order. `parent` is the impl or trait for a method.
#[allow(dead_code)] // Params are read by generic collect in wave A; predicates via `Defs::param_env`.
#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub parent: Option<DefId>,
    pub params: Vec<ParamDef>,
    pub predicates: Vec<Predicate>,
}

/// Auto trait bits on a `dyn` bound list. Auto traits a supertrait requires are part
/// of the bounds (ARCH 2.1, 2.8).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct AutoTraits {
    pub send: bool,
    pub sync: bool,
    pub unpin: bool,
}

/// A `dyn` bound list: one principal trait ref under its binder (a `dyn for<'a>`
/// principal keeps count 1, with its associated bindings under the same binder),
/// the supertrait trait refs in declaration order, and the auto trait bits.
///
/// The principal is existential: its Self slot (`args[0]`) holds `DYN_SELF`,
/// never a `Param`, so a dyn type is closed under substitution of the generics
/// around it. `resolve_dyn` keeps `supertraits` empty and `auto` as written:
/// both derived sets come from the trait's dyn info (`check::object`) once trait
/// tables exist, so one written dyn type always interns to one `BoundsId`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DynBounds {
    pub principal: Option<Binder<TraitRef>>,
    pub supertraits: Box<[Binder<TraitRef>]>,
    pub auto: AutoTraits,
}

/// An elaborated param environment: the written predicates plus their elaboration
/// (supertraits and associated equalities to a fixpoint, deduplicated, first
/// occurrence order kept). Computed by `elaborate`, interned by `defs::Defs`.
/// Selection and normalization read the param env through `Defs` queries only.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParamEnvData {
    pub predicates: Box<[Predicate]>,
}

/// The open, interned type form (ARCH 2.1). New variants go at the end only; this
/// enum is on the ARCH 9.2 interface-freeze list. Every payload is an id or a small
/// `Copy` value, so `TyKind` stays `Copy`.
#[allow(dead_code)] // Variants for syntax not yet in the subset are formed by their feature waves.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    /// Placeholder after an error. Unifies with anything, so one mistake gives one error.
    Error,
    Unit,
    Bool,
    Char,
    Never,
    Int(IntTy),
    Float(FloatTy),
    /// Unsized `str`.
    Str,
    Ref(Region, Mut, Ty),
    /// Raw pointers: std and shim code only at first.
    RawPtr(Mut, Ty),
    Slice(Ty),
    Array(Ty, ConstId),
    Tuple(TysId),
    /// A user or std struct, enum, or union (no unions in the subset), applied to
    /// generic args. `String`, `Vec<T>`, and `Option<T>` are Adts with builtin defs.
    Adt(DefId, ArgsId),
    FnPtr(SigId),
    /// A fn item used as a value, before coercion to a fn pointer.
    FnDef(DefId, ArgsId),
    Closure(DefId, ArgsId),
    Dyn(BoundsId, Region),
    /// An `impl Trait` return type.
    Opaque(DefId, ArgsId),
    /// A generic parameter of the item whose signature this type sits in.
    Param(ParamId),
    /// `<Self as Trait>::Assoc`, unnormalized. Args are the trait ref, Self first.
    Projection(AssocId, ArgsId),
    /// A body-local inference variable. Never in the global store.
    Infer(InferId),
}

impl TyKind {
    /// True for an unbound integer-literal variable (the `{integer}` of error messages).
    pub fn is_int_infer(self) -> bool {
        matches!(self, TyKind::Infer(v) if v.is_int())
    }
    /// True for an unbound float-literal variable (the `{float}` of error messages).
    pub fn is_float_infer(self) -> bool {
        matches!(self, TyKind::Infer(v) if v.1 == InferKind::Float)
    }
}

/// The late-bound region of a `dyn Fn*` type's sugar (R11): an elided
/// lifetime of its inputs or output, which the object binds itself (`dyn
/// Fn(&u8)` is `dyn for<'r> Fn(&'r u8)`). Check's types and region
/// signatures mark it in the object's trait args; it is no region slot.
/// A plain `Region::Bound` elsewhere (an `Fn*` bound's elided lifetime)
/// keeps its own meaning.
pub const DYN_LATE: Region = Region::Bound(u32::MAX);

pub const ERROR: Ty = Ty(0);
/// The Self slot of an existential dyn principal (see `DynBounds`). It is the
/// error type, which no code reads as a real Self: callers that need a trait
/// ref for a dyn value put the dyn type itself in that slot.
pub const DYN_SELF: Ty = ERROR;
pub const UNIT: Ty = Ty(1);
pub const BOOL: Ty = Ty(2);
pub const CHAR: Ty = Ty(3);
pub const STR: Ty = Ty(4);
/// `String`: `Adt(BuiltinDefs::string, EMPTY_ARGS)`, pre-interned at this index.
pub const STRING: Ty = Ty(5);
pub const NEVER: Ty = Ty(6);
/// `std::env::Args`: `Adt(BuiltinDefs::args, EMPTY_ARGS)`, pre-interned at this index.
pub const ARGS: Ty = Ty(7);
pub const REF_STR: Ty = Ty(8);
const FIRST_INT: u32 = 9;
/// `str::Chars`: `Adt(BuiltinDefs::chars, EMPTY_ARGS)`, interned right after the ints.
/// It borrows the string it came from; borrow checking tracks that, not the type.
pub const CHARS: Ty = Ty(FIRST_INT + IntTy::ALL.len() as u32);

/// The pre-interned `Ty` of an integer type. `IntTy::ALL` order is the index order.
pub fn int(t: IntTy) -> Ty {
    Ty(FIRST_INT + IntTy::ALL.iter().position(|&x| x == t).unwrap() as u32)
}
pub const I32: Ty = Ty(FIRST_INT + 2);
/// The pre-interned float types follow the ints and CHARS in the global store;
/// use `float_ty` through an interner instead of naming their indexes here.
pub const USIZE: Ty = Ty(FIRST_INT + 9);

/// The session-local crate id of the builtin defs. It is a sentinel outside every
/// real session crate space; builtin `DefId`s never enter disk or slot keys, so the
/// ARCH 1.7 rule against disk use of a whole `DefId` is not weakened by it.
pub const BUILTIN_CRATE: CrateId = CrateId(u32::MAX);

/// The stable crate hash the builtin def paths are hashed under.
fn builtin_crate_hash() -> StableCrateHash {
    crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false)
}

/// One builtin Adt def: hashed from its std path, like any other def (ARCH 1.7).
fn builtin_def(module: &[&str], name: &str) -> DefId {
    DefId { krate: BUILTIN_CRATE, hash: crate::def::item_hash(builtin_crate_hash(), module, crate::def::DefKind::Adt, name, 0) }
}

/// The marker def a primitive builtin method's item type names
/// (`u8::is_ascii_digit` used as a value, TRIAGE T12): its `FnDef`
/// args are `[Ty(self), Const(name sym), Const(builtin code),
/// extra tys..]` (check's `prim_item_value` and `prim_item_res`).
pub fn prim_fn_def() -> DefId {
    builtin_def(&["__lust"], "PrimFn")
}

/// The def of `core::num::NonZero<T>` (TRIAGE T5): a synthetic
/// std Adt (check/collect.rs registers it like `Bound`), named
/// here so layout can give it the zero niche.
pub fn nonzero_def() -> DefId {
    builtin_def(&["core", "num"], "NonZero")
}

/// The def of `core::mem::MaybeUninit<T>` (TRIAGE T5): a
/// synthetic std Adt like `NonZero`, named here so layout can
/// drop the field's niche (a union has none).
pub fn maybe_uninit_def() -> DefId {
    builtin_def(&["core", "mem"], "MaybeUninit")
}

/// The defs of the types that were closed `TyKind` cases before S3a. They become real
/// std-crate defs when source std lands (ARCH 3.1); until then the builtin code paths
/// in check, lower, and cgen recognize them through the `TyIntern` compat helpers.
#[derive(Clone, Copy, Debug)]
pub struct BuiltinDefs {
    pub string: DefId,
    pub vec: DefId,
    pub option: DefId,
    pub result: DefId,
    pub boxed: DefId,
    pub rc: DefId,
    /// `str::Chars`, the iterator from `s.chars()`.
    pub chars: DefId,
    /// The builtin iterator structs, by `IterKind` index (ty/iter.rs).
    pub iters: [DefId; iter::IterKind::ALL.len()],
    /// The `core::fmt` structs, by `FmtTy` index (ty/fmt.rs).
    pub fmt_tys: [DefId; fmt::FmtTy::ALL.len()],
    /// `std::rc::Weak`, `std::cell::{RefCell, Cell}`, and the
    /// `RefCell` guards `Ref` and `RefMut` (W-STD-A phase 3).
    pub weak: DefId,
    pub refcell: DefId,
    pub cell: DefId,
    pub ref_guard: DefId,
    pub ref_mut_guard: DefId,
    /// `std::process::ExitCode`, a `main` result (W-STD-A phase 3).
    pub exit_code: DefId,
    /// The `std::sync` and `std::thread` types, by `SyncTy` index
    /// (ty/sync.rs, W-THREADS).
    pub sync_tys: [DefId; sync::SyncTy::ALL.len()],
    /// `std::thread::LocalKey` and `std::thread::AccessError`
    /// (thread_local!, check/tls.rs).
    pub local_key: DefId,
    pub access_error: DefId,
    /// The hashed collections and hasher types, by `HashTy` index
    /// (ty/hash.rs).
    pub hash_tys: [DefId; hash::HashTy::ALL.len()],
}

impl BuiltinDefs {
    /// Which builtin a def is, if it is one of these. Every builtin def
    /// is in `BUILTIN_CRATE`, so a user def answers after one compare.
    pub fn kind_of(&self, def: DefId) -> Option<BuiltinTy> {
        if def.krate != BUILTIN_CRATE {
            None
        } else if def == self.string {
            Some(BuiltinTy::String)
        } else if def == self.vec {
            Some(BuiltinTy::Vec)
        } else if def == self.option {
            Some(BuiltinTy::Option)
        } else if def == self.boxed {
            Some(BuiltinTy::Boxed)
        } else if def == self.rc {
            Some(BuiltinTy::Rc)
        } else if def == self.result {
            Some(BuiltinTy::Result)
        } else if def == self.chars {
            Some(BuiltinTy::Chars)
        } else if let Some(i) = self.fmt_tys.iter().position(|&d| d == def) {
            Some(BuiltinTy::Fmt(fmt::FmtTy::ALL[i]))
        } else if def == self.weak {
            Some(BuiltinTy::Weak)
        } else if def == self.refcell {
            Some(BuiltinTy::RefCell)
        } else if def == self.cell {
            Some(BuiltinTy::Cell)
        } else if def == self.ref_guard {
            Some(BuiltinTy::RefGuard)
        } else if def == self.ref_mut_guard {
            Some(BuiltinTy::RefMutGuard)
        } else if def == self.exit_code {
            Some(BuiltinTy::ExitCode)
        } else if let Some(i) = self.sync_tys.iter().position(|&d| d == def) {
            Some(BuiltinTy::Sync(sync::SyncTy::ALL[i]))
        } else if let Some(i) = self.hash_tys.iter().position(|&d| d == def) {
            Some(BuiltinTy::Hash(hash::HashTy::ALL[i]))
        } else if def == self.local_key {
            Some(BuiltinTy::LocalKey)
        } else if def == self.access_error {
            Some(BuiltinTy::AccessError)
        } else {
            self.iters.iter().position(|&d| d == def).map(|i| BuiltinTy::Iter(iter::IterKind::ALL[i]))
        }
    }
}

/// A builtin type recognized by the compat helpers. Named apart from `check::Builtin`
/// (builtin methods), which is a different list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinTy {
    String,
    Vec,
    Option,
    Result,
    Boxed,
    Rc,
    Chars,
    /// A std iterator struct (ty/iter.rs).
    Iter(iter::IterKind),
    /// A `core::fmt` struct (ty/fmt.rs).
    Fmt(fmt::FmtTy),
    Weak,
    RefCell,
    Cell,
    /// `cell::Ref<T>`, a shared `RefCell` borrow guard.
    RefGuard,
    /// `cell::RefMut<T>`, a mutable `RefCell` borrow guard.
    RefMutGuard,
    /// `process::ExitCode`.
    ExitCode,
    /// A `std::sync` or `std::thread` type (ty/sync.rs).
    Sync(sync::SyncTy),
    /// `std::thread::LocalKey<T>`, the type of a `thread_local!` static.
    LocalKey,
    /// `std::thread::AccessError`, `LocalKey::try_with`'s error.
    AccessError,
    /// A hashed collection or std hasher type (ty/hash.rs).
    Hash(hash::HashTy),
}

/// What a type contains, computed once at intern time and cached per `Ty`. Substitution,
/// normalization, and zonking read the bits to return the input `Ty` unchanged when the
/// type holds nothing they would rewrite (ARCH 2.1: both stay allocation-light).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TyFlags(u8);

impl TyFlags {
    const PARAM: u8 = 1;
    const PROJECTION: u8 = 2;
    const INFER: u8 = 4;
    const STATIC_REGION: u8 = 8;
    const LOOSE_BOUND: u8 = 16;
    /// True if some subterm is a generic `Param`.
    pub fn contains_param(self) -> bool {
        self.0 & Self::PARAM != 0
    }
    /// True if some subterm is an unnormalized `Projection`.
    #[allow(dead_code)] // Read by normalization when trait selection lands (ARCH 2.5).
    pub fn contains_projection(self) -> bool {
        self.0 & Self::PROJECTION != 0
    }
    /// True if some subterm is an inference variable.
    pub fn contains_infer(self) -> bool {
        self.0 & Self::INFER != 0
    }
    /// True if some subterm is a dyn type or a reference with a
    /// `'static` region (the only regions lust keeps; see
    /// `check::object`): coercions skip the region checks without one.
    pub fn contains_static_region(self) -> bool {
        self.0 & Self::STATIC_REGION != 0
    }
    /// True if a `DYN_LATE` region sits outside every dyn type's trait
    /// args (a late-bound region of `dyn Fn*` sugar that left its object;
    /// see `unbind`).
    pub fn contains_loose_bound(self) -> bool {
        self.0 & Self::LOOSE_BOUND != 0
    }
    fn union(self, other: TyFlags) -> TyFlags {
        TyFlags(self.0 | other.0)
    }
}

/// A type store: interning and lookup for kinds and every supporting arena. The two
/// implementations are the frozen `GlobalTys` and a body's overlay `Tys`. The default
/// methods are the compat helpers the builtin code paths use; new code should prefer
/// the general `TyKind` forms and reach a builtin only through them.
pub trait TyIntern {
    fn intern(&mut self, k: TyKind) -> Ty;
    fn kind(&self, t: Ty) -> TyKind;
    /// The already-interned `Ty` for a kind, if any. Never interns.
    fn get(&self, k: TyKind) -> Option<Ty>;
    /// The intern-time containment bits of a type.
    fn flags(&self, t: Ty) -> TyFlags;
    fn intern_args(&mut self, args: &[GenericArg]) -> ArgsId;
    fn args(&self, id: ArgsId) -> &[GenericArg];
    /// The already-interned id of this argument list, if any. Never interns.
    fn get_args(&self, _args: &[GenericArg]) -> Option<ArgsId> {
        None
    }
    fn intern_tys(&mut self, tys: &[Ty]) -> TysId;
    fn tys_of(&self, id: TysId) -> &[Ty];
    /// The already-interned id of this type list, if any. Never interns.
    fn get_tys(&self, _tys: &[Ty]) -> Option<TysId> {
        None
    }
    #[allow(dead_code)] // Formed by array lengths and const generics in wave A.
    fn intern_const(&mut self, c: ConstKind) -> ConstId;
    #[allow(dead_code)] // See `intern_const`.
    fn const_kind(&self, id: ConstId) -> ConstKind;
    fn intern_sig(&mut self, s: Binder<FnSig>) -> SigId;
    fn sig(&self, id: SigId) -> Binder<FnSig>;
    fn intern_dyn_bounds(&mut self, b: DynBounds) -> BoundsId;
    fn dyn_bounds(&self, id: BoundsId) -> &DynBounds;
    fn intern_bindings(&mut self, b: &[(DefId, GenericArg)]) -> BindingsId;
    fn bindings(&self, id: BindingsId) -> &[(DefId, GenericArg)];
    /// The builtin Adt defs this store's global table was built with.
    /// By reference: the table holds about a hundred defs, and the type
    /// queries below (`builtin_of`) run on every hot path.
    fn builtins(&self) -> &BuiltinDefs;
    /// The param env of the body this store belongs to: empty for the
    /// global store and concrete bodies (see `Tys::env`).
    fn param_env(&self) -> &[Predicate] {
        &[]
    }
    /// The session-local index of the user Adt with this def, if this store knows it.
    fn local_adt_of(&self, def: DefId) -> Option<AdtId>;
    /// The def of the user Adt with this session-local index, if registered.
    fn def_of_local_adt(&self, local: AdtId) -> Option<DefId>;
    /// The unsized field of an unsized newtype Adt (W-SHIM; see
    /// `GlobalTys::unsized_adts`), None for every other def. For a
    /// generic one this is the template's field (it names the params).
    fn unsized_field(&self, _def: DefId) -> Option<Ty> {
        None
    }
    /// The field of one instance of a generic unsized newtype, made by
    /// mono (`register_unsized_inst`); None before that.
    fn unsized_inst_field(&self, _def: DefId, _args: ArgsId) -> Option<Ty> {
        None
    }
    /// True when `t` lives in the global store, so a fresh store over
    /// `GlobalTys` (a `PureCx`) reads it the same way. Body-local
    /// types answer false.
    fn is_global_ty(&self, _t: Ty) -> bool {
        true
    }

    /// The `f32` or `f64` type.
    fn float_ty(&mut self, f: FloatTy) -> Ty {
        self.intern(TyKind::Float(f))
    }
    /// `&T` or `&mut T` with an erased region (the only milestone 4 form).
    fn mk_ref(&mut self, mutable: bool, t: Ty) -> Ty {
        self.intern(TyKind::Ref(Region::Erased, Mut::from_bool(mutable), t))
    }
    /// An Adt applied to generic args, in declared parameter order.
    fn mk_adt(&mut self, def: DefId, args: &[GenericArg]) -> Ty {
        let a = self.intern_args(args);
        self.intern(TyKind::Adt(def, a))
    }
    /// The full applied type of a registered user Adt: for a
    /// monomorphized instance that is `Adt(def, concrete args)`,
    /// for a plain Adt `Adt(def, EMPTY_ARGS)`.
    fn adt_ty(&mut self, local: AdtId) -> Ty {
        if let Some(t) = self.full_adt_ty_of(local) {
            return t;
        }
        let def = self.def_of_local_adt(local).expect("user ADT defs are registered during collection");
        self.intern(TyKind::Adt(def, EMPTY_ARGS))
    }
    /// The already-interned type of a registered user Adt, if any. Never interns.
    fn get_adt_ty(&self, local: AdtId) -> Option<Ty> {
        if let Some(t) = self.full_adt_ty_of(local) {
            return Some(t);
        }
        self.get(TyKind::Adt(self.def_of_local_adt(local)?, EMPTY_ARGS))
    }
    /// The registered full type of a session-local Adt, if the
    /// store keeps one (the global store does; overlays read it).
    fn full_adt_ty_of(&self, _local: AdtId) -> Option<Ty> {
        None
    }
    /// `Vec<elem>` as an Adt application of the builtin def. Implemented per store
    /// over a one-entry application cache: these two applications are by far the
    /// most common in signatures, and the cache keeps them at one map probe
    /// instead of an arg-slice intern plus a kind intern.
    fn mk_vec(&mut self, elem: Ty) -> Ty;
    /// `Option<elem>` as an Adt application of the builtin def. See `mk_vec`.
    fn mk_option(&mut self, elem: Ty) -> Ty;
    /// `Box<elem>` as an Adt application of the builtin def.
    fn mk_boxed(&mut self, elem: Ty) -> Ty {
        let def = self.builtins().boxed;
        self.mk_adt(def, &[GenericArg::Ty(elem)])
    }
    /// `Rc<elem>` as an Adt application of the builtin def.
    fn mk_rc(&mut self, elem: Ty) -> Ty {
        let def = self.builtins().rc;
        self.mk_adt(def, &[GenericArg::Ty(elem)])
    }
    /// `Result<t, e>` as an Adt application of the builtin def. No
    /// one-arg cache: the plain intern path dedups it.
    fn mk_result(&mut self, t: Ty, e: Ty) -> Ty {
        let def = self.builtins().result;
        self.mk_adt(def, &[GenericArg::Ty(t), GenericArg::Ty(e)])
    }
    /// The `(def, args)` of an Adt type, builtin or user.
    fn adt_parts(&self, t: Ty) -> Option<(DefId, ArgsId)> {
        match self.kind(t) {
            TyKind::Adt(d, a) => Some((d, a)),
            _ => None,
        }
    }
    /// Which builtin type this is, if it is one.
    fn builtin_of(&self, t: Ty) -> Option<BuiltinTy> {
        self.builtins().kind_of(self.adt_parts(t)?.0)
    }
    /// True if this type is `String`.
    fn is_string_ty(&self, t: Ty) -> bool {
        self.builtin_of(t) == Some(BuiltinTy::String)
    }
    /// True if this type is `str::Chars`.
    fn is_chars_ty(&self, t: Ty) -> bool {
        self.builtin_of(t) == Some(BuiltinTy::Chars)
    }
    /// The first type argument of an Adt type, if it has one.
    fn adt_first_ty_arg(&self, t: Ty) -> Option<Ty> {
        let (_, a) = self.adt_parts(t)?;
        self.args(a).first().and_then(|g| g.as_ty())
    }
    /// The element type of a `Vec<T>`.
    fn vec_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Vec)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// The element type of an `Option<T>`.
    fn option_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Option)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// The pointee type of a `Box<T>`.
    fn boxed_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Boxed)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// The element type of a boxed slice `Box<[T]>`.
    fn boxed_slice_elem(&self, t: Ty) -> Option<Ty> {
        match self.kind(self.boxed_elem(t)?) {
            TyKind::Slice(e) => Some(e),
            _ => None,
        }
    }
    /// The pointee type of a shared counted pointer: an `Rc<T>` or an
    /// `Arc<T>` (W-THREADS). Both deref to a shared `T` only, are
    /// `Clone` for every `T`, and convert to `&T` alike; the builtins
    /// that make one (`Rc::new`, `Arc::new`) keep their own types.
    fn rc_elem(&self, t: Ty) -> Option<Ty> {
        match self.builtin_of(t) {
            Some(BuiltinTy::Rc | BuiltinTy::Sync(sync::SyncTy::Arc)) => self.adt_first_ty_arg(t),
            _ => None,
        }
    }
    /// The pointee type of a `Box<T>`, an `Rc<T>`, or a `RefCell`
    /// guard (`Ref<T>`, `RefMut<T>`): the smart pointers method calls,
    /// fields, and coercions deref through.
    /// The value type `T` of a `LocalKey<T>`.
    fn local_key_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::LocalKey)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// `LocalKey<elem>` as an Adt application of the builtin def.
    fn mk_local_key(&mut self, elem: Ty) -> Ty {
        let def = self.builtins().local_key;
        self.mk_adt(def, &[GenericArg::Ty(elem)])
    }
    /// `std::thread::AccessError`.
    fn access_error_ty(&mut self) -> Ty {
        let def = self.builtins().access_error;
        self.mk_adt(def, &[])
    }
    /// The pointee type of a `Box<T>` or an `Rc<T>`: the smart
    /// pointers method calls, fields, and coercions deref through.
    fn smart_elem(&self, t: Ty) -> Option<Ty> {
        self.boxed_elem(t).or_else(|| self.rc_elem(t)).or_else(|| self.guard_elem(t).map(|g| g.0))
    }
    /// The element type of a `sync::Weak<T>` (W-THREADS).
    fn arc_weak_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Sync(sync::SyncTy::ArcWeak))).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// The value type of a `Mutex<T>` or `RwLock<T>`, with its kind.
    fn lock_elem(&self, t: Ty) -> Option<(sync::SyncTy, Ty)> {
        match self.builtin_of(t)? {
            BuiltinTy::Sync(k) if k.is_lock() => Some((k, self.adt_first_ty_arg(t)?)),
            _ => None,
        }
    }
    /// The type argument of a `sync::PoisonError<T>`.
    fn poison_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Sync(sync::SyncTy::PoisonError))).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// The value type of a guard (`Ref`, `RefMut`, or a lock guard) and
    /// whether it gives `&mut T`.
    fn guard_elem(&self, t: Ty) -> Option<(Ty, bool)> {
        match self.builtin_of(t)? {
            BuiltinTy::RefGuard => Some((self.adt_first_ty_arg(t)?, false)),
            BuiltinTy::RefMutGuard => Some((self.adt_first_ty_arg(t)?, true)),
            // The lock guards deref the same way (W-THREADS).
            BuiltinTy::Sync(k) => Some((self.adt_first_ty_arg(t)?, k.guard()?.1)),
            _ => None,
        }
    }
    /// The element type of a `Weak<T>`, `RefCell<T>`, or `Cell<T>`.
    fn weak_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Weak)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    fn refcell_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::RefCell)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    fn cell_elem(&self, t: Ty) -> Option<Ty> {
        (self.builtin_of(t) == Some(BuiltinTy::Cell)).then(|| self.adt_first_ty_arg(t)).flatten()
    }
    /// `std::process::ExitCode`.
    fn exit_code_ty(&mut self) -> Ty {
        let def = self.builtins().exit_code;
        self.mk_adt(def, &[])
    }
    fn is_exit_code(&self, t: Ty) -> bool {
        self.builtin_of(t) == Some(BuiltinTy::ExitCode)
    }
    /// One of the one-arg builtin Adts by its def field.
    fn mk_builtin1(&mut self, which: fn(&BuiltinDefs) -> DefId, elem: Ty) -> Ty {
        let def = which(self.builtins());
        self.mk_adt(def, &[GenericArg::Ty(elem)])
    }
    /// The `(T, E)` type arguments of a `Result<T, E>`.
    fn result_args(&self, t: Ty) -> Option<(Ty, Ty)> {
        if self.builtin_of(t) != Some(BuiltinTy::Result) {
            return None;
        }
        let (_, a) = self.adt_parts(t)?;
        let args = self.args(a);
        Some((args.first().and_then(|g| g.as_ty())?, args.get(1).and_then(|g| g.as_ty())?))
    }
    /// The session-local index of a monomorphized Adt instance
    /// (`Bag<u8>` next to `Bag<u16>`), registered by mono when it
    /// materializes the instance's `AdtDef`. None when this store
    /// has no instance registry or the instance is not made yet.
    fn local_adt_instance(&self, _def: DefId, _args: ArgsId) -> Option<AdtId> {
        None
    }
    /// The Adt whose C type `a` uses: `a` itself, or the instance that
    /// differs from it only in lifetimes and was registered first.
    fn c_adt(&self, a: AdtId) -> AdtId {
        a
    }
    /// The first instance registered under the region-free args `key`
    /// (`GlobalTys::adt_c_keys`). None when this store has no registry.
    fn c_instance(&self, _def: DefId, _key: ArgsId) -> Option<AdtId> {
        None
    }
    /// The session-local index of a user Adt type. None for builtin Adts and
    /// non-Adt types; builtin checks must run first where both can appear.
    /// The builtin def list answers without a table lookup, which keeps
    /// this at the old closed-kind match cost on builtin receivers. (Not
    /// the builtin crate as a whole: `core::cmp::Ordering` carries a
    /// builtin-crate def but is registered as a local Adt in collect,
    /// so it must answer here like a user enum.) A generic application
    /// answers with its materialized instance when mono has made one,
    /// and with the template otherwise.
    fn local_adt(&self, t: Ty) -> Option<AdtId> {
        let (def, args) = self.adt_parts(t)?;
        if self.builtins().kind_of(def).is_some() {
            return None;
        }
        if args != EMPTY_ARGS
            && let Some(inst) = self.local_adt_instance(def, args)
        {
            return Some(inst);
        }
        self.local_adt_of(def)
    }
}

/// The Adt whose C type the user Adt type `t` uses (`cgen::cty`). A
/// generic application with `'static` regions that mono never made (only
/// a dead fn's signature names it) takes the instance that differs from it
/// only in lifetimes, so a value moves between the two as one C type.
pub fn c_adt_of(tys: &impl TyIntern, t: Ty) -> Option<AdtId> {
    let a = tys.local_adt(t)?;
    if tys.flags(t).contains_static_region()
        && let Some((def, args)) = tys.adt_parts(t)
        && tys.local_adt_instance(def, args).is_none()
        && let Some(key) = region_free_args_get(tys, args)
        && let Some(inst) = tys.c_instance(def, key)
    {
        return Some(tys.c_adt(inst));
    }
    Some(tys.c_adt(a))
}

/// `GlobalTys::region_free` without interning: None when the region-free
/// form was never interned (then no instance has it).
fn region_free_get(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    if !tys.flags(t).contains_static_region() {
        return Some(t);
    }
    let k = match tys.kind(t) {
        TyKind::Ref(_, m, i) => TyKind::Ref(Region::Erased, m, region_free_get(tys, i)?),
        TyKind::Dyn(b, _) => TyKind::Dyn(b, Region::Erased),
        TyKind::RawPtr(m, i) => TyKind::RawPtr(m, region_free_get(tys, i)?),
        TyKind::Slice(e) => TyKind::Slice(region_free_get(tys, e)?),
        TyKind::Array(e, n) => TyKind::Array(region_free_get(tys, e)?, n),
        TyKind::Tuple(ts) => {
            let elems: Option<Vec<Ty>> = tys.tys_of(ts).iter().map(|&e| region_free_get(tys, e)).collect();
            TyKind::Tuple(tys.get_tys(&elems?)?)
        }
        TyKind::Adt(d, a) => TyKind::Adt(d, region_free_args_get(tys, a)?),
        _ => return Some(t),
    };
    tys.get(k)
}

/// `GlobalTys::region_free_args` without interning.
pub(crate) fn region_free_args_get(tys: &impl TyIntern, args: ArgsId) -> Option<ArgsId> {
    let old = tys.args(args);
    let new: Option<Vec<GenericArg>> = old
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(t) => region_free_get(tys, t).map(GenericArg::Ty),
            GenericArg::Lifetime(_) => Some(GenericArg::Lifetime(Region::Erased)),
            c => Some(c),
        })
        .collect();
    let new = new?;
    if new.as_slice() == old { Some(args) } else { tys.get_args(&new) }
}

/// The containment bits of a kind about to be interned. Children are already
/// interned, so their cached bits are read, never recomputed by walking terms.
/// `t` with each loose `DYN_LATE` region (`TyFlags::contains_loose_bound`)
/// made `Erased`. A type taken out of a `dyn Fn*` object (a call's
/// argument or result type, an inference variable) holds a plain region
/// where the object's sugar binds one. Trait args of a dyn type keep
/// theirs.
pub fn unbind(s: &mut impl TyIntern, t: Ty) -> Ty {
    if !s.flags(t).contains_loose_bound() {
        return t;
    }
    // An Adt's lifetime args in check's types are only `DYN_LATE` marks
    // (and their companions): they go (`adt`).
    fn args(s: &mut impl TyIntern, a: ArgsId, adt: bool) -> ArgsId {
        let new: Vec<GenericArg> = s
            .args(a)
            .to_vec()
            .into_iter()
            .filter(|g| !(adt && matches!(g, GenericArg::Lifetime(_))))
            .map(|g| if let GenericArg::Ty(e) = g { GenericArg::Ty(unbind(s, e)) } else { g })
            .collect();
        s.intern_args(&new)
    }
    match s.kind(t) {
        TyKind::Ref(r, m, inner) => {
            let i = unbind(s, inner);
            let r = if r == DYN_LATE { Region::Erased } else { r };
            s.intern(TyKind::Ref(r, m, i))
        }
        TyKind::Dyn(b, DYN_LATE) => s.intern(TyKind::Dyn(b, Region::Erased)),
        TyKind::RawPtr(m, e) => {
            let e = unbind(s, e);
            s.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = unbind(s, e);
            s.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = unbind(s, e);
            s.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let v: Vec<Ty> = s.tys_of(ts).to_vec().into_iter().map(|e| unbind(s, e)).collect();
            let ts = s.intern_tys(&v);
            s.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) | TyKind::FnDef(d, a) | TyKind::Closure(d, a) | TyKind::Opaque(d, a) => {
            let a = args(s, a, matches!(s.kind(t), TyKind::Adt(..)));
            s.intern(match s.kind(t) {
                TyKind::Adt(..) => TyKind::Adt(d, a),
                TyKind::FnDef(..) => TyKind::FnDef(d, a),
                TyKind::Closure(..) => TyKind::Closure(d, a),
                _ => TyKind::Opaque(d, a),
            })
        }
        TyKind::Projection(d, a) => {
            let a = args(s, a, false);
            s.intern(TyKind::Projection(d, a))
        }
        _ => t,
    }
}

fn compute_flags(s: &impl TyIntern, k: TyKind) -> TyFlags {
    let of_ty = |t: Ty| s.flags(t);
    let of_const = |c: ConstId| match s.const_kind(c) {
        ConstKind::Param(_) => TyFlags(TyFlags::PARAM),
        ConstKind::Infer(_) => TyFlags(TyFlags::INFER),
        _ => TyFlags::default(),
    };
    let of_args = |a: ArgsId| {
        s.args(a).iter().fold(TyFlags::default(), |f, g| match g {
            GenericArg::Ty(t) => f.union(of_ty(*t)),
            GenericArg::Const(c) => f.union(of_const(*c)),
            GenericArg::Lifetime(DYN_LATE) => f.union(TyFlags(TyFlags::LOOSE_BOUND)),
            GenericArg::Lifetime(_) => f,
        })
    };
    let of_trait_ref = |tr: &TraitRef| {
        let f = of_args(tr.args);
        s.bindings(tr.bindings).iter().fold(f, |f, (_, g)| match g.as_ty() {
            Some(t) => f.union(of_ty(t)),
            None => f,
        })
    };
    match k {
        TyKind::Param(_) => TyFlags(TyFlags::PARAM),
        TyKind::Infer(_) => TyFlags(TyFlags::INFER),
        TyKind::Projection(_, a) => TyFlags(TyFlags::PROJECTION).union(of_args(a)),
        TyKind::Ref(Region::Static, _, t) => of_ty(t).union(TyFlags(TyFlags::STATIC_REGION)),
        TyKind::Ref(DYN_LATE, _, t) => of_ty(t).union(TyFlags(TyFlags::LOOSE_BOUND)),
        TyKind::Ref(_, _, t) | TyKind::RawPtr(_, t) | TyKind::Slice(t) => of_ty(t),
        TyKind::Array(t, c) => of_ty(t).union(of_const(c)),
        TyKind::Tuple(ts) => s.tys_of(ts).iter().fold(TyFlags::default(), |f, &t| f.union(of_ty(t))),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => of_args(a),
        TyKind::FnPtr(sig) => {
            let sig = s.sig(sig).value;
            s.tys_of(sig.inputs).iter().fold(of_ty(sig.output), |f, &t| f.union(of_ty(t)))
        }
        TyKind::Dyn(b, r) => {
            let b = s.dyn_bounds(b);
            let mut f = b.principal.as_ref().map_or_else(TyFlags::default, |p| of_trait_ref(&p.value));
            for sup in &b.supertraits {
                f = f.union(of_trait_ref(&sup.value));
            }
            // The late-bound regions of the trait args are the object's own.
            f = TyFlags(f.0 & !TyFlags::LOOSE_BOUND);
            if r == Region::Static {
                f = f.union(TyFlags(TyFlags::STATIC_REGION));
            }
            if r == DYN_LATE {
                f = f.union(TyFlags(TyFlags::LOOSE_BOUND));
            }
            f
        }
        _ => TyFlags::default(),
    }
}

/// One interned arena. The same value always gets the same id; ids start at `base`
/// so a body overlay can continue the global arena's numbering (as `Ty` does today).
///
/// Membership is per collect (B1-PLAN.md): a global arena can outlive one collect (its
/// entries are immutable structure), and `seen` holds, per entry, the collect epoch that
/// last interned it. A lookup (`get_id`, `get_slice`) answers only for entries this epoch
/// interned, and the first intern of an older entry in this epoch counts as a new entry
/// (a window logs it as a write), so every membership answer is the one a fresh store
/// gives; ids stay as they were. The first `pre` entries (`GlobalTys::new`'s constants,
/// used without an intern call) are seen in every epoch. A body overlay's arenas start at
/// epoch 0 and are always seen.
#[derive(Clone)]
struct Arena<T, I> {
    items: Vec<T>,
    map: FxMap<T, I>,
    /// The global store's arenas log misses and new entries for window
    /// checks (check/spec.rs); a body overlay's log nothing (`tab::NONE`).
    tab: u8,
    seen: Vec<u32>,
    epoch: u32,
    pre: u32,
    /// The id of `items[0]` (an overlay's arenas continue the global numbering).
    base: u32,
}

impl<T, I> Default for Arena<T, I> {
    fn default() -> Arena<T, I> {
        Arena { items: Vec::new(), map: FxMap::default(), tab: spec::tab::NONE, seen: Vec::new(), epoch: 0, pre: 0, base: 0 }
    }
}

impl<T: Clone + Eq + Hash, I: Idx> Arena<T, I> {
    fn len(&self) -> u32 {
        self.items.len() as u32
    }
    /// True when this epoch interned the entry with id `id`.
    fn seen_now(&self, id: u32) -> bool {
        let i = id - self.base;
        i < self.pre || self.seen.get(i as usize) == Some(&self.epoch)
    }
    /// Starts a collect epoch: no entry but the first `pre` is a member until interned.
    fn next_epoch(&mut self) {
        self.epoch += 1;
    }
    fn get_id(&self, v: &T) -> Option<I> {
        let id = self.map.get(v).copied().filter(|id| self.seen_now(id.to_u32()));
        if id.is_none() && self.tab != spec::tab::NONE {
            spec::read(self.tab, v);
        }
        id
    }
    /// Marks the entry with id `id` interned in this epoch; true when it was not yet.
    fn see(&mut self, id: u32) -> bool {
        let i = id - self.base;
        match self.seen.get_mut(i as usize) {
            Some(e) if *e != self.epoch && i >= self.pre => {
                *e = self.epoch;
                true
            }
            _ => false,
        }
    }
    fn intern(&mut self, v: T, base: u32) -> I {
        if let Some(&id) = self.map.get(&v) {
            if self.see(id.to_u32()) && self.tab != spec::tab::NONE {
                spec::wrote(self.tab, &v);
            }
            return id;
        }
        if self.tab != spec::tab::NONE {
            spec::wrote(self.tab, &v);
        }
        self.base = base;
        let id = I::from_u32(base + self.items.len() as u32);
        self.map.insert(v.clone(), id);
        self.items.push(v);
        self.seen.push(self.epoch);
        id
    }
}

impl<X: Clone + Eq + Hash, I: Idx> Arena<Box<[X]>, I> {
    fn get_slice(&self, s: &[X]) -> Option<I> {
        let id = self.map.get(s).copied().filter(|id| self.seen_now(id.to_u32()));
        if id.is_none() && self.tab != spec::tab::NONE {
            spec::read(self.tab, s);
        }
        id
    }
    fn intern_slice(&mut self, s: &[X], base: u32) -> I {
        if let Some(&id) = self.map.get(s) {
            if self.see(id.to_u32()) && self.tab != spec::tab::NONE {
                spec::wrote(self.tab, s);
            }
            return id;
        }
        if self.tab != spec::tab::NONE {
            spec::wrote(self.tab, s);
        }
        let boxed: Box<[X]> = s.into();
        self.base = base;
        let id = I::from_u32(base + self.items.len() as u32);
        self.map.insert(boxed.clone(), id);
        self.items.push(boxed);
        self.seen.push(self.epoch);
        id
    }
}

/// The type store a session keeps from its last collect for the next one (B1-PLAN.md):
/// the interned structure only (`GlobalTys::begin_collect` drops every registration and
/// makes membership per collect). It serves a collect of the same crate identity and the
/// same string interner (a fn item type of a primitive keeps a `Sym` inside its
/// `ConstKind::Int`). It is not kept when the store holds more than twice the types its last
/// collect interned, so it stays within twice a fresh store. `LUST_TYPE_POOL=0` keeps none.
pub struct TypePool {
    tys: GlobalTys,
    krate: crate::def::CrateId,
    stable: crate::def::StableCrateHash,
    interner: usize,
}

impl TypePool {
    /// The pool of a program's store, when it may serve again.
    pub fn of(tys: GlobalTys, krate: crate::def::CrateId, stable: crate::def::StableCrateHash, interner: &std::sync::Arc<crate::intern::Interner>) -> Option<TypePool> {
        if std::env::var_os("LUST_TYPE_POOL").is_some_and(|v| v == "0") {
            return None;
        }
        let (members, total) = tys.member_counts();
        (total <= 2 * members.max(1)).then(|| TypePool { tys, krate, stable, interner: std::sync::Arc::as_ptr(interner) as usize })
    }
    /// The store for a new collect of crate `krate`/`stable` with `interner`, or None.
    pub fn take(self, krate: crate::def::CrateId, stable: crate::def::StableCrateHash, interner: &std::sync::Arc<crate::intern::Interner>) -> Option<GlobalTys> {
        let same = self.krate == krate && self.stable == stable && self.interner == std::sync::Arc::as_ptr(interner) as usize;
        same.then(|| {
            let mut tys = self.tys;
            tys.begin_collect();
            tys
        })
    }
}

/// The frozen signature store of one crate session, built during collection.
pub struct GlobalTys {
    kinds: Arena<TyKind, Ty>,
    flags: Vec<TyFlags>,
    args_a: Arena<Box<[GenericArg]>, ArgsId>,
    tys_a: Arena<Box<[Ty]>, TysId>,
    #[allow(dead_code)] // Read through `intern_const` from wave A; kept in lockstep with the other arenas.
    consts: Arena<ConstKind, ConstId>,
    sigs: Arena<Binder<FnSig>, SigId>,
    bounds: Arena<DynBounds, BoundsId>,
    bindings_a: Arena<Box<[(DefId, GenericArg)]>, BindingsId>,
    builtins: BuiltinDefs,
    /// One-argument Adt applications by (def, elem): the `mk_vec`/`mk_option` cache.
    adt1: spec::Logged<(DefId, Ty), Ty, { spec::tab::TY_ADT1 }>,
    adt_locals: spec::Logged<DefId, AdtId, { spec::tab::TY_ADT_LOCALS }>,
    adt_defs: Vec<DefId>,
    /// Materialized generic instances: (template def, concrete args)
    /// to the instance's session-local index. Filled by mono during
    /// collection; body overlays read it through the global store.
    adt_instances: spec::Logged<(DefId, ArgsId), AdtId, { spec::tab::TY_ADT_INSTANCES }>,
    /// Instances that differ only in lifetimes (`M<Rc<dyn Tr>>` next to
    /// `M<Rc<dyn Tr + 'static>>`) share one C type: the first registered
    /// instance under the region-free args (`region_free`), and each later
    /// one to it (`c_adt`).
    adt_c_keys: spec::Logged<(DefId, ArgsId), AdtId, { spec::tab::TY_ADT_C_KEYS }>,
    adt_c_canon: spec::Logged<AdtId, AdtId, { spec::tab::TY_ADT_C_CANON }>,
    /// The full applied type of each session-local Adt, in index
    /// order where registered: `Adt(def, args)` with the instance's
    /// args, not always `EMPTY_ARGS`.
    adt_full_tys: Vec<Option<Ty>>,
    /// Unsized newtypes (W-SHIM): a struct whose only field is unsized
    /// (`str`, `[T]`, or, non-generic only, another such struct), by
    /// def, to that field's type. `std::path::Path`, `std::ffi::OsStr`,
    /// and indexmap's generic `map::Slice<K, V>` are these.
    unsized_adts: spec::Logged<DefId, Ty, { spec::tab::TY_UNSIZED }>,
    /// The field of each mono instance of a generic unsized newtype.
    unsized_insts: spec::Logged<(DefId, ArgsId), Ty, { spec::tab::TY_UNSIZED_INSTS }>,
}

impl GlobalTys {
    pub fn new() -> GlobalTys {
        let builtins = BuiltinDefs {
            string: builtin_def(&["alloc", "string"], "String"),
            vec: builtin_def(&["alloc", "vec"], "Vec"),
            option: builtin_def(&["core", "option"], "Option"),
            result: builtin_def(&["core", "result"], "Result"),
            boxed: builtin_def(&["alloc", "boxed"], "Box"),
            rc: builtin_def(&["alloc", "rc"], "Rc"),
            chars: builtin_def(&["core", "str"], "Chars"),
            iters: iter::IterKind::ALL.map(iter::iter_def),
            fmt_tys: fmt::FmtTy::ALL.map(fmt::fmt_def),
            weak: builtin_def(&["alloc", "rc"], "Weak"),
            refcell: builtin_def(&["core", "cell"], "RefCell"),
            cell: builtin_def(&["core", "cell"], "Cell"),
            ref_guard: builtin_def(&["core", "cell"], "Ref"),
            ref_mut_guard: builtin_def(&["core", "cell"], "RefMut"),
            exit_code: builtin_def(&["std", "process"], "ExitCode"),
            sync_tys: sync::SyncTy::ALL.map(sync::sync_def),
            local_key: builtin_def(&["std", "thread"], "LocalKey"),
            access_error: builtin_def(&["std", "thread"], "AccessError"),
            hash_tys: hash::HashTy::ALL.map(hash::hash_def),
        };
        let mut g = GlobalTys {
            kinds: Arena::default(),
            flags: Vec::new(),
            args_a: Arena::default(),
            tys_a: Arena::default(),
            consts: Arena::default(),
            sigs: Arena::default(),
            bounds: Arena::default(),
            bindings_a: Arena::default(),
            builtins,
            adt1: Default::default(),
            adt_locals: Default::default(),
            adt_defs: Vec::new(),
            adt_instances: Default::default(),
            adt_c_keys: Default::default(),
            adt_c_canon: Default::default(),
            adt_full_tys: Vec::new(),
            unsized_adts: Default::default(),
            unsized_insts: Default::default(),
        };
        g.kinds.tab = spec::tab::KINDS;
        g.args_a.tab = spec::tab::ARGS;
        g.tys_a.tab = spec::tab::TYS_LIST;
        g.consts.tab = spec::tab::CONSTS;
        g.sigs.tab = spec::tab::SIGS;
        g.bounds.tab = spec::tab::BOUNDS;
        g.bindings_a.tab = spec::tab::BINDINGS;
        // The intern calls must stay out of the assertions: `debug_assert_eq!`
        // drops its arguments in release builds, which would skip the interning.
        let empty_args = g.intern_args(&[]);
        let empty_tys = g.intern_tys(&[]);
        let empty_bindings = g.intern_bindings(&[]);
        debug_assert_eq!((empty_args, empty_tys, empty_bindings), (EMPTY_ARGS, EMPTY_TYS, EMPTY_BINDINGS));
        let pre = [
            g.intern(TyKind::Error),
            g.intern(TyKind::Unit),
            g.intern(TyKind::Bool),
            g.intern(TyKind::Char),
            g.intern(TyKind::Str),
            g.intern(TyKind::Adt(builtins.string, EMPTY_ARGS)),
            g.intern(TyKind::Never),
            g.intern(TyKind::Adt(builtins.iters[iter::IterKind::Args as usize], EMPTY_ARGS)),
            g.mk_ref(false, STR),
        ];
        debug_assert_eq!(pre, [ERROR, UNIT, BOOL, CHAR, STR, STRING, NEVER, ARGS, REF_STR]);
        for t in IntTy::ALL {
            g.intern(TyKind::Int(t));
        }
        let chars = g.intern(TyKind::Adt(builtins.chars, EMPTY_ARGS));
        debug_assert_eq!(chars, CHARS);
        // The constants above are used without an intern call: members in every epoch.
        g.kinds.pre = g.kinds.len();
        g.args_a.pre = g.args_a.len();
        g.tys_a.pre = g.tys_a.len();
        g.consts.pre = g.consts.len();
        g.sigs.pre = g.sigs.len();
        g.bounds.pre = g.bounds.len();
        g.bindings_a.pre = g.bindings_a.len();
        g
    }
    /// Starts a new collect on this store (B1-PLAN.md): the interned structure stays, ids
    /// included, but no entry is a member until this collect interns it (`Arena`), and
    /// every live registration (the Adt rows' tables, instances, C keys, unsized fields,
    /// the one-argument Adt cache) starts empty, as in a fresh store.
    pub fn begin_collect(&mut self) {
        self.kinds.next_epoch();
        self.args_a.next_epoch();
        self.tys_a.next_epoch();
        self.consts.next_epoch();
        self.sigs.next_epoch();
        self.bounds.next_epoch();
        self.bindings_a.next_epoch();
        let GlobalTys {
            kinds: _,
            flags: _,
            args_a: _,
            tys_a: _,
            consts: _,
            sigs: _,
            bounds: _,
            bindings_a: _,
            builtins: _,
            adt1,
            adt_locals,
            adt_defs,
            adt_instances,
            adt_c_keys,
            adt_c_canon,
            adt_full_tys,
            unsized_adts,
            unsized_insts,
        } = self;
        *adt1 = Default::default();
        *adt_locals = Default::default();
        *adt_defs = Vec::new();
        *adt_instances = Default::default();
        *adt_c_keys = Default::default();
        *adt_c_canon = Default::default();
        *adt_full_tys = Vec::new();
        *unsized_adts = Default::default();
        *unsized_insts = Default::default();
    }
    /// True when this collect interned type `t` (always, without `begin_collect`).
    pub fn is_member(&self, t: Ty) -> bool {
        self.kinds.seen_now(t.0)
    }
    /// When this collect started from a kept store (`TypePool`): `member_counts`.
    pub fn pool_counts(&self) -> Option<(usize, usize)> {
        (self.kinds.epoch > 0).then(|| self.member_counts())
    }
    /// The types this collect interned, and all the store holds.
    pub fn member_counts(&self) -> (usize, usize) {
        let k = &self.kinds;
        let members = k.seen.iter().enumerate().filter(|&(i, &e)| (i as u32) < k.pre || e == k.epoch).count();
        (members, k.items.len())
    }
    /// Records the def of one user Adt, so `Adt(def, ..)` types can reach the local
    /// `AdtDef` compat data. Collection calls this once per struct and enum, in order.
    pub fn register_adt(&mut self, def: DefId, local: AdtId) {
        self.adt_locals.insert(def, local);
        let i = local.0 as usize;
        if i >= self.adt_defs.len() {
            self.adt_defs.resize(i + 1, DefId::PLACEHOLDER);
        }
        spec::wrote(spec::tab::TY_ADT_DEFS, &i);
        self.adt_defs[i] = def;
        if i >= self.adt_full_tys.len() {
            self.adt_full_tys.resize(i + 1, None);
        }
        let t = self.intern(TyKind::Adt(def, EMPTY_ARGS));
        spec::wrote(spec::tab::TY_ADT_FULL, &i);
        self.adt_full_tys[i] = Some(t);
    }
    /// `t` with every kept region (`'static`, the only one left after
    /// borrowck) erased, in references, dyn types and lifetime args: the
    /// key that makes instances differing only in lifetimes one C type.
    /// Fn pointers, closures and fn items keep theirs.
    fn region_free(&mut self, t: Ty) -> Ty {
        if !self.flags(t).contains_static_region() {
            return t;
        }
        match self.kind(t) {
            TyKind::Ref(_, m, i) => {
                let i = self.region_free(i);
                self.intern(TyKind::Ref(Region::Erased, m, i))
            }
            TyKind::Dyn(b, _) => self.intern(TyKind::Dyn(b, Region::Erased)),
            TyKind::RawPtr(m, i) => {
                let i = self.region_free(i);
                self.intern(TyKind::RawPtr(m, i))
            }
            TyKind::Slice(e) => {
                let e = self.region_free(e);
                self.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.region_free(e);
                self.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys_of(ts).to_vec();
                let elems: Vec<Ty> = elems.into_iter().map(|e| self.region_free(e)).collect();
                let ts = self.intern_tys(&elems);
                self.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let a = self.region_free_args(a);
                self.intern(TyKind::Adt(d, a))
            }
            _ => t,
        }
    }

    fn region_free_args(&mut self, args: ArgsId) -> ArgsId {
        let old: Vec<GenericArg> = self.args(args).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(t) => GenericArg::Ty(self.region_free(t)),
                GenericArg::Lifetime(_) => GenericArg::Lifetime(Region::Erased),
                c => c,
            })
            .collect();
        if new == old { args } else { self.intern_args(&new) }
    }

    /// Records an unsized newtype (see `unsized_adts`): collect calls it
    /// once its single field type is known to be unsized.
    pub fn register_unsized_adt(&mut self, def: DefId, field: Ty) {
        self.unsized_adts.insert(def, field);
    }
    /// Records the field of one instance of a generic unsized newtype
    /// (mono's `adt_instance`).
    pub fn register_unsized_inst(&mut self, def: DefId, args: ArgsId, field: Ty) {
        self.unsized_insts.insert((def, args), field);
    }
    /// Records one materialized generic Adt instance: its applied
    /// type (already interned) and its session-local index. The
    /// template's own registration stays untouched, so the template
    /// and every instance coexist in the compat tables.
    pub fn register_adt_instance(&mut self, def: DefId, args: ArgsId, local: AdtId) -> Ty {
        let t = self.intern(TyKind::Adt(def, args));
        self.adt_instances.insert((def, args), local);
        let key = self.region_free_args(args);
        let canon = *self.adt_c_keys.entry((def, key)).or_insert(local);
        if canon != local {
            self.adt_c_canon.insert(local, canon);
        }
        let i = local.0 as usize;
        if i >= self.adt_full_tys.len() {
            self.adt_full_tys.resize(i + 1, None);
        }
        spec::wrote(spec::tab::TY_ADT_FULL, &i);
        self.adt_full_tys[i] = Some(t);
        t
    }
    /// The already-interned id of one const value, if any.
    pub fn consts_get(&self, k: ConstKind) -> Option<ConstId> {
        self.consts.get_id(&k)
    }
    /// The already-interned id of one dyn bound list, if any.
    pub fn dyn_bounds_get(&self, b: &DynBounds) -> Option<BoundsId> {
        self.bounds.get_id(b)
    }
    /// The already-interned id of one binding list, if any.
    pub fn bindings_get(&self, b: &[(DefId, GenericArg)]) -> Option<BindingsId> {
        self.bindings_a.get_slice(b)
    }
    /// The full applied type of a session-local Adt, if registered.
    pub fn full_adt_ty(&self, local: AdtId) -> Option<Ty> {
        spec::read(spec::tab::TY_ADT_FULL, &(local.0 as usize));
        self.adt_full_tys.get(local.0 as usize).copied().flatten()
    }
}

impl TyIntern for GlobalTys {
    fn intern(&mut self, k: TyKind) -> Ty {
        if let Some(t) = self.kinds.get_id(&k) {
            return t;
        }
        // An entry an earlier collect interned (not a member yet, `Arena`) keeps its id
        // and flags; only a new entry gets flags.
        let f = compute_flags(&*self, k);
        let t = self.kinds.intern(k, 0);
        if t.0 as usize == self.flags.len() {
            self.flags.push(f);
        }
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.kinds.items[t.0 as usize]
    }
    fn get(&self, k: TyKind) -> Option<Ty> {
        self.kinds.get_id(&k)
    }
    fn flags(&self, t: Ty) -> TyFlags {
        self.flags[t.0 as usize]
    }
    fn intern_args(&mut self, args: &[GenericArg]) -> ArgsId {
        self.args_a.intern_slice(args, 0)
    }
    fn args(&self, id: ArgsId) -> &[GenericArg] {
        &self.args_a.items[id.0 as usize]
    }
    fn get_args(&self, args: &[GenericArg]) -> Option<ArgsId> {
        self.args_a.get_slice(args)
    }
    fn intern_tys(&mut self, tys: &[Ty]) -> TysId {
        self.tys_a.intern_slice(tys, 0)
    }
    fn tys_of(&self, id: TysId) -> &[Ty] {
        &self.tys_a.items[id.0 as usize]
    }
    fn get_tys(&self, tys: &[Ty]) -> Option<TysId> {
        self.tys_a.get_slice(tys)
    }
    fn intern_const(&mut self, c: ConstKind) -> ConstId {
        self.consts.intern(c, 0)
    }
    fn const_kind(&self, id: ConstId) -> ConstKind {
        self.consts.items[id.0 as usize]
    }
    fn intern_sig(&mut self, s: Binder<FnSig>) -> SigId {
        self.sigs.intern(s, 0)
    }
    fn sig(&self, id: SigId) -> Binder<FnSig> {
        self.sigs.items[id.0 as usize]
    }
    fn intern_dyn_bounds(&mut self, b: DynBounds) -> BoundsId {
        self.bounds.intern(b, 0)
    }
    fn dyn_bounds(&self, id: BoundsId) -> &DynBounds {
        &self.bounds.items[id.0 as usize]
    }
    fn intern_bindings(&mut self, b: &[(DefId, GenericArg)]) -> BindingsId {
        self.bindings_a.intern_slice(b, 0)
    }
    fn bindings(&self, id: BindingsId) -> &[(DefId, GenericArg)] {
        &self.bindings_a.items[id.0 as usize]
    }
    fn builtins(&self) -> &BuiltinDefs {
        &self.builtins
    }
    fn mk_vec(&mut self, elem: Ty) -> Ty {
        let def = self.builtins.vec;
        if let Some(&t) = self.adt1.get(&(def, elem)) {
            return t;
        }
        let t = self.mk_adt(def, &[GenericArg::Ty(elem)]);
        self.adt1.insert((def, elem), t);
        t
    }
    fn mk_option(&mut self, elem: Ty) -> Ty {
        let def = self.builtins.option;
        if let Some(&t) = self.adt1.get(&(def, elem)) {
            return t;
        }
        let t = self.mk_adt(def, &[GenericArg::Ty(elem)]);
        self.adt1.insert((def, elem), t);
        t
    }
    fn local_adt_of(&self, def: DefId) -> Option<AdtId> {
        self.adt_locals.get(&def).copied()
    }
    fn unsized_field(&self, def: DefId) -> Option<Ty> {
        self.unsized_adts.get(&def).copied()
    }
    fn unsized_inst_field(&self, def: DefId, args: ArgsId) -> Option<Ty> {
        self.unsized_insts.get(&(def, args)).copied()
    }
    fn def_of_local_adt(&self, local: AdtId) -> Option<DefId> {
        spec::read(spec::tab::TY_ADT_DEFS, &(local.0 as usize));
        self.adt_defs.get(local.0 as usize).copied().filter(|d| *d != DefId::PLACEHOLDER)
    }
    fn local_adt_instance(&self, def: DefId, args: ArgsId) -> Option<AdtId> {
        self.adt_instances.get(&(def, args)).copied()
    }
    fn c_adt(&self, a: AdtId) -> AdtId {
        self.adt_c_canon.get(&a).copied().unwrap_or(a)
    }
    fn c_instance(&self, def: DefId, key: ArgsId) -> Option<AdtId> {
        self.adt_c_keys.get(&(def, key)).copied()
    }
    fn full_adt_ty_of(&self, local: AdtId) -> Option<Ty> {
        self.full_adt_ty(local)
    }
}

/// A function's view of the type table: the frozen global table plus local additions.
/// Every arena numbers its local entries after the global entries, so a global id
/// means the same value in every body and bodies need no locks. Clone copies the
/// local additions (codegen's iterator expansion grows a copy, lower/iter.rs).
#[derive(Clone)]
pub struct Tys<'g> {
    pub global: &'g GlobalTys,
    /// The param env of the template body this store belongs to
    /// (empty for a concrete body). Structural trait queries
    /// (`is_copy`, `has_clone`, and kin) answer a `Param` or
    /// projection type from it: such a type is rigid and has
    /// exactly the traits its bounds give it (ARCH 4.1).
    pub env: &'g [Predicate],
    kinds: Arena<TyKind, Ty>,
    flags: Vec<TyFlags>,
    args_a: Arena<Box<[GenericArg]>, ArgsId>,
    tys_a: Arena<Box<[Ty]>, TysId>,
    #[allow(dead_code)] // See the `GlobalTys` field of the same name.
    consts: Arena<ConstKind, ConstId>,
    sigs: Arena<Binder<FnSig>, SigId>,
    bounds: Arena<DynBounds, BoundsId>,
    bindings_a: Arena<Box<[(DefId, GenericArg)]>, BindingsId>,
    /// Body-local `mk_vec`/`mk_option` cache; global hits are read from `global`.
    adt1: FxMap<(DefId, Ty), Ty>,
}

impl<'g> Tys<'g> {
    pub fn new(global: &'g GlobalTys) -> Tys<'g> {
        Tys {
            global,
            env: &[],
            kinds: Arena::default(),
            flags: Vec::new(),
            args_a: Arena::default(),
            tys_a: Arena::default(),
            consts: Arena::default(),
            sigs: Arena::default(),
            bounds: Arena::default(),
            bindings_a: Arena::default(),
            adt1: FxMap::default(),
        }
    }

    /// One-argument Adt application through the caches: global entries first
    /// (read-only), then this body's, then a fresh intern recorded locally.
    fn mk_adt1(&mut self, def: DefId, elem: Ty) -> Ty {
        if let Some(&t) = self.global.adt1.get(&(def, elem)) {
            return t;
        }
        if let Some(&t) = self.adt1.get(&(def, elem)) {
            return t;
        }
        let t = self.mk_adt(def, &[GenericArg::Ty(elem)]);
        self.adt1.insert((def, elem), t);
        t
    }
}

impl TyIntern for Tys<'_> {
    fn intern(&mut self, k: TyKind) -> Ty {
        if let Some(t) = self.global.kinds.get_id(&k) {
            return t;
        }
        if let Some(t) = self.kinds.get_id(&k) {
            return t;
        }
        spec::step(1);
        let f = compute_flags(&*self, k);
        let t = self.kinds.intern(k, self.global.kinds.len());
        debug_assert_eq!(self.flags.len(), (t.0 - self.global.kinds.len()) as usize);
        self.flags.push(f);
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        let g = self.global.kinds.len();
        if t.0 < g { self.global.kinds.items[t.0 as usize] } else { self.kinds.items[(t.0 - g) as usize] }
    }
    fn get(&self, k: TyKind) -> Option<Ty> {
        self.global.kinds.get_id(&k).or_else(|| self.kinds.get_id(&k))
    }
    fn flags(&self, t: Ty) -> TyFlags {
        let g = self.global.kinds.len();
        if t.0 < g { self.global.flags[t.0 as usize] } else { self.flags[(t.0 - g) as usize] }
    }
    fn intern_args(&mut self, args: &[GenericArg]) -> ArgsId {
        if let Some(id) = self.global.args_a.get_slice(args) {
            return id;
        }
        let base = self.global.args_a.len();
        self.args_a.intern_slice(args, base)
    }
    fn args(&self, id: ArgsId) -> &[GenericArg] {
        let g = self.global.args_a.len();
        if id.0 < g { &self.global.args_a.items[id.0 as usize] } else { &self.args_a.items[(id.0 - g) as usize] }
    }
    fn get_args(&self, args: &[GenericArg]) -> Option<ArgsId> {
        self.global.args_a.get_slice(args).or_else(|| self.args_a.get_slice(args))
    }
    fn intern_tys(&mut self, tys: &[Ty]) -> TysId {
        if let Some(id) = self.global.tys_a.get_slice(tys) {
            return id;
        }
        let base = self.global.tys_a.len();
        self.tys_a.intern_slice(tys, base)
    }
    fn tys_of(&self, id: TysId) -> &[Ty] {
        let g = self.global.tys_a.len();
        if id.0 < g { &self.global.tys_a.items[id.0 as usize] } else { &self.tys_a.items[(id.0 - g) as usize] }
    }
    fn get_tys(&self, tys: &[Ty]) -> Option<TysId> {
        self.global.tys_a.get_slice(tys).or_else(|| self.tys_a.get_slice(tys))
    }
    fn intern_const(&mut self, c: ConstKind) -> ConstId {
        if let Some(id) = self.global.consts.get_id(&c) {
            return id;
        }
        let base = self.global.consts.len();
        self.consts.intern(c, base)
    }
    fn const_kind(&self, id: ConstId) -> ConstKind {
        let g = self.global.consts.len();
        if id.0 < g { self.global.consts.items[id.0 as usize] } else { self.consts.items[(id.0 - g) as usize] }
    }
    fn intern_sig(&mut self, s: Binder<FnSig>) -> SigId {
        if let Some(id) = self.global.sigs.get_id(&s) {
            return id;
        }
        let base = self.global.sigs.len();
        self.sigs.intern(s, base)
    }
    fn sig(&self, id: SigId) -> Binder<FnSig> {
        let g = self.global.sigs.len();
        if id.0 < g { self.global.sigs.items[id.0 as usize] } else { self.sigs.items[(id.0 - g) as usize] }
    }
    fn intern_dyn_bounds(&mut self, b: DynBounds) -> BoundsId {
        if let Some(id) = self.global.bounds.get_id(&b) {
            return id;
        }
        let base = self.global.bounds.len();
        self.bounds.intern(b, base)
    }
    fn dyn_bounds(&self, id: BoundsId) -> &DynBounds {
        let g = self.global.bounds.len();
        if id.0 < g { &self.global.bounds.items[id.0 as usize] } else { &self.bounds.items[(id.0 - g) as usize] }
    }
    fn intern_bindings(&mut self, b: &[(DefId, GenericArg)]) -> BindingsId {
        if let Some(id) = self.global.bindings_a.get_slice(b) {
            return id;
        }
        let base = self.global.bindings_a.len();
        self.bindings_a.intern_slice(b, base)
    }
    fn bindings(&self, id: BindingsId) -> &[(DefId, GenericArg)] {
        let g = self.global.bindings_a.len();
        if id.0 < g { &self.global.bindings_a.items[id.0 as usize] } else { &self.bindings_a.items[(id.0 - g) as usize] }
    }
    fn builtins(&self) -> &BuiltinDefs {
        &self.global.builtins
    }
    fn param_env(&self) -> &[Predicate] {
        self.env
    }
    fn mk_vec(&mut self, elem: Ty) -> Ty {
        let def = self.global.builtins.vec;
        self.mk_adt1(def, elem)
    }
    fn mk_option(&mut self, elem: Ty) -> Ty {
        let def = self.global.builtins.option;
        self.mk_adt1(def, elem)
    }
    fn local_adt_of(&self, def: DefId) -> Option<AdtId> {
        self.global.local_adt_of(def)
    }
    fn unsized_field(&self, def: DefId) -> Option<Ty> {
        self.global.unsized_field(def)
    }
    fn unsized_inst_field(&self, def: DefId, args: ArgsId) -> Option<Ty> {
        self.global.unsized_inst_field(def, args)
    }
    fn is_global_ty(&self, t: Ty) -> bool {
        t.0 < self.global.kinds.len() && self.global.is_member(t)
    }
    fn def_of_local_adt(&self, local: AdtId) -> Option<DefId> {
        self.global.def_of_local_adt(local)
    }
    fn local_adt_instance(&self, def: DefId, args: ArgsId) -> Option<AdtId> {
        self.global.local_adt_instance(def, args)
    }
    fn c_adt(&self, a: AdtId) -> AdtId {
        self.global.c_adt(a)
    }
    fn c_instance(&self, def: DefId, key: ArgsId) -> Option<AdtId> {
        self.global.c_instance(def, key)
    }
    fn full_adt_ty_of(&self, local: AdtId) -> Option<Ty> {
        self.global.full_adt_ty(local)
    }
}

/// Pure substitution: replaces each `Param(i)` by `args[i]` and erases nothing
/// (ARCH 2.1). It takes no solver and records no reads, unlike normalization
/// (ARCH 2.5), which rewrites projections and lives with trait selection.
/// A type that contains no param is returned unchanged, with no interning.
/// A param with no type argument at its index is left as written. Regions are
/// not substituted here: region params use their own index space and milestone 6
/// owns their instantiation through binders.
#[allow(dead_code)] // First production callers are generic check and mono (W-TRAITS-CORE, W-MONO).
pub fn subst(s: &mut impl TyIntern, t: Ty, args: &[GenericArg]) -> Ty {
    if !s.flags(t).contains_param() {
        return t;
    }
    match s.kind(t) {
        TyKind::Param(p) => match args.get(p.0 as usize).and_then(|g| g.as_ty()) {
            Some(u) => u,
            None => t,
        },
        TyKind::Ref(r, m, e) => {
            let e = subst(s, e, args);
            s.intern(TyKind::Ref(r, m, e))
        }
        TyKind::RawPtr(m, e) => {
            let e = subst(s, e, args);
            s.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = subst(s, e, args);
            s.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = subst(s, e, args);
            let n = subst_const(s, n, args);
            s.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let old: Vec<Ty> = s.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.iter().map(|&e| subst(s, e, args)).collect();
            let ts = s.intern_tys(&new);
            s.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let a = subst_args(s, a, args);
            s.intern(TyKind::Adt(d, a))
        }
        TyKind::FnDef(d, a) => {
            let a = subst_args(s, a, args);
            s.intern(TyKind::FnDef(d, a))
        }
        TyKind::Closure(d, a) => {
            let a = subst_args(s, a, args);
            s.intern(TyKind::Closure(d, a))
        }
        TyKind::Opaque(d, a) => {
            let a = subst_args(s, a, args);
            s.intern(TyKind::Opaque(d, a))
        }
        TyKind::Projection(d, a) => {
            let a = subst_args(s, a, args);
            s.intern(TyKind::Projection(d, a))
        }
        TyKind::FnPtr(sig) => {
            let b = s.sig(sig);
            let old: Vec<Ty> = s.tys_of(b.value.inputs).to_vec();
            let new: Vec<Ty> = old.iter().map(|&e| subst(s, e, args)).collect();
            let inputs = s.intern_tys(&new);
            let output = subst(s, b.value.output, args);
            let sig = s.intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..b.value } });
            s.intern(TyKind::FnPtr(sig))
        }
        TyKind::Dyn(bounds, r) => {
            let old = s.dyn_bounds(bounds).clone();
            let principal = match old.principal {
                Some(p) => Some(Binder { count: p.count, value: subst_trait_ref(s, p.value, args) }),
                None => None,
            };
            let mut supertraits: Vec<Binder<TraitRef>> = Vec::new();
            for p in old.supertraits.iter() {
                supertraits.push(Binder { count: p.count, value: subst_trait_ref(s, p.value, args) });
            }
            let bounds = s.intern_dyn_bounds(DynBounds { principal, supertraits: supertraits.into(), auto: old.auto });
            s.intern(TyKind::Dyn(bounds, r))
        }
        _ => t,
    }
}

/// One const value under substitution: a const parameter takes
/// its argument when the argument is a const.
fn subst_const(s: &mut impl TyIntern, c: ConstId, args: &[GenericArg]) -> ConstId {
    match s.const_kind(c) {
        ConstKind::Param(i) => match args.get(i as usize) {
            Some(GenericArg::Const(k)) => *k,
            _ => c,
        },
        _ => c,
    }
}

/// One generic argument under substitution. Lifetimes pass through.
fn subst_one_arg(s: &mut impl TyIntern, g: GenericArg, args: &[GenericArg]) -> GenericArg {
    match g {
        GenericArg::Ty(t) => GenericArg::Ty(subst(s, t, args)),
        GenericArg::Const(c) => GenericArg::Const(subst_const(s, c, args)),
        other => other,
    }
}

/// A trait ref under substitution: its args and its bindings, binder kept by the caller.
fn subst_trait_ref(s: &mut impl TyIntern, tr: TraitRef, args: &[GenericArg]) -> TraitRef {
    let a = subst_args(s, tr.args, args);
    let old_b: Vec<(DefId, GenericArg)> = s.bindings(tr.bindings).to_vec();
    let new_b: Vec<(DefId, GenericArg)> = old_b.iter().map(|&(d, g)| (d, subst_one_arg(s, g, args))).collect();
    let bindings = s.intern_bindings(&new_b);
    TraitRef { def: tr.def, args: a, bindings }
}

/// An argument list under substitution, re-interned in the same store.
fn subst_args(s: &mut impl TyIntern, a: ArgsId, args: &[GenericArg]) -> ArgsId {
    let old: Vec<GenericArg> = s.args(a).to_vec();
    let new: Vec<GenericArg> = old.iter().map(|&g| subst_one_arg(s, g, args)).collect();
    s.intern_args(&new)
}

/// Param-env elaboration (ARCH 2.1 steps 1 to 5), as a pure fixpoint over written
/// predicates. `supertraits` returns, for one trait predicate, the predicates of its
/// trait def's own bounds with Self already substituted, binders included; it is a
/// `Defs` query in production and a closed table in tests. Each associated type
/// binding also adds its `AssocEq`, under the same binder as the trait ref that
/// carried it. The result is deduplicated with first occurrence order kept. The set
/// is finite: a supertrait cycle only re-adds facts that dedup then drops.
#[allow(dead_code)] // Reached through `Defs::param_env`; its production callers land with traits.
pub fn elaborate(s: &impl TyIntern, written: &[Predicate], supertraits: &dyn Fn(&TraitRef) -> Vec<Predicate>) -> Vec<Predicate> {
    let mut out: Vec<Predicate> = Vec::new();
    let mut work: Vec<Predicate> = written.to_vec();
    let mut i = 0;
    while i < work.len() {
        let p = work[i];
        i += 1;
        if out.contains(&p) {
            continue;
        }
        out.push(p);
        if let Predicate::Trait(b) = p {
            for &(assoc, arg) in s.bindings(b.value.bindings) {
                // Only type bindings become equalities; an assoc const binding is a
                // const value, read through the const evaluator (ARCH 2.5), not a `Ty`.
                if let GenericArg::Ty(ty) = arg {
                    work.push(Predicate::AssocEq(Binder { count: b.count, value: AssocEqData { assoc, trait_args: b.value.args, ty } }));
                }
            }
            work.extend(supertraits(&b.value));
        }
    }
    out
}

/// The owned type store lift (ARCH 2.1): when check finishes a body, lowering lifts
/// its local types into the crate session's append-only type store and rewrites every
/// `Ty` in the result, so a checked body owns stable session ids. Through S7 it is
/// the identity: a body's `Tys` overlay moves whole into `ir::Body`, which owns it,
/// and no result is cached or shared across crates yet. The session store that
/// makes this rewrite real lands with mono and the disk cache (W-MONO, W-DRIVER);
/// callers go through it now so the boundary stays fixed. Cross-crate readers must
/// translate by structural fingerprint (ARCH 8.4), never by raw id, identity or not.
pub fn lift_to_owned(tys: Tys<'_>) -> Tys<'_> {
    tys
}

/// One type through the owned store lift. Identity today; see `lift_to_owned`.
#[allow(dead_code)] // The session store (W-MONO) is the first user that rewrites ids.
pub fn lift_ty(t: Ty) -> Ty {
    t
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, LOCAL_CRATE};

    fn fake_def(hash: u64) -> DefId {
        DefId { krate: LOCAL_CRATE, hash: DefPathHash(hash) }
    }

    /// The pre-interned constants still name the same types, now as Adt applications
    /// of the builtin defs, and the compat helpers read them back.
    #[test]
    fn builtin_types_are_adt_applications() {
        let mut g = GlobalTys::new();
        let b = g.builtins();
        assert_eq!(g.kind(STRING), TyKind::Adt(b.string, EMPTY_ARGS));
        assert_eq!(g.kind(ARGS), TyKind::Adt(b.iters[iter::IterKind::Args as usize], EMPTY_ARGS));
        assert_eq!(g.kind(CHARS), TyKind::Adt(b.chars, EMPTY_ARGS));
        assert_eq!(g.kind(REF_STR), TyKind::Ref(Region::Erased, Mut::Shared, STR));
        assert_eq!(g.kind(I32), TyKind::Int(IntTy::I32));
        assert_eq!(g.kind(USIZE), TyKind::Int(IntTy::Usize));
        let v = g.mk_vec(BOOL);
        assert_eq!(g.vec_elem(v), Some(BOOL));
        assert_eq!(g.builtin_of(v), Some(BuiltinTy::Vec));
        let o = g.mk_option(v);
        assert_eq!(g.option_elem(o), Some(v));
        assert!(g.is_string_ty(STRING) && g.is_chars_ty(CHARS));
        assert_eq!(g.local_adt(STRING), None, "builtins are not user Adts");
        assert_eq!(g.mk_vec(I32), g.mk_vec(I32), "same application, same Ty");
    }

    /// One schema for generic args: lifetimes, types, and consts interleave as
    /// written, order is part of identity, and `TysId` is a separate list type.
    #[test]
    fn arg_interning_keeps_declared_order() {
        let mut g = GlobalTys::new();
        assert_eq!(g.intern_args(&[]), EMPTY_ARGS);
        assert_eq!(g.intern_tys(&[]), EMPTY_TYS);
        assert_eq!(g.intern_bindings(&[]), EMPTY_BINDINGS);
        let c = g.intern_const(ConstKind::Int(3));
        assert_eq!(g.const_kind(c), ConstKind::Int(3));
        let mixed = [GenericArg::Lifetime(Region::Static), GenericArg::Ty(I32), GenericArg::Const(c)];
        let a = g.intern_args(&mixed);
        assert_eq!(g.intern_args(&mixed), a);
        assert_eq!(g.args(a), mixed);
        let reordered = g.intern_args(&[GenericArg::Ty(I32), GenericArg::Lifetime(Region::Static), GenericArg::Const(c)]);
        assert_ne!(a, reordered);
        let ts = g.intern_tys(&[I32, BOOL]);
        assert_eq!(g.intern_tys(&[I32, BOOL]), ts);
        assert_eq!(g.tys_of(ts), [I32, BOOL]);
    }

    /// A body overlay interns its own slices and kinds without touching the global
    /// store, and still returns global ids for global values.
    #[test]
    fn overlay_interning_stays_local() {
        let mut g = GlobalTys::new();
        let global_vec = g.mk_vec(I32);
        let mut tys = Tys::new(&g);
        assert_eq!(tys.mk_vec(I32), global_vec);
        let var = tys.intern(TyKind::Infer(InferId(0, InferKind::General)));
        let local_vec = tys.mk_vec(var);
        assert_eq!(tys.vec_elem(local_vec), Some(var));
        assert_eq!(g.get(tys.kind(local_vec)), None, "body-local kinds never enter the global store");
        let lifted = lift_to_owned(tys);
        assert_eq!(lifted.vec_elem(local_vec), Some(var), "the identity lift keeps body ids valid");
    }

    /// Registered user Adts round-trip between `DefId` (in the type) and the
    /// session-local `AdtId` the compat tables use.
    #[test]
    fn user_adt_registration_round_trips() {
        let mut g = GlobalTys::new();
        let def = fake_def(7);
        g.register_adt(def, AdtId(0));
        let t = g.adt_ty(AdtId(0));
        assert_eq!(g.kind(t), TyKind::Adt(def, EMPTY_ARGS));
        assert_eq!(g.local_adt(t), Some(AdtId(0)));
        assert_eq!(g.get_adt_ty(AdtId(0)), Some(t));
        assert_eq!(g.builtin_of(t), None);
    }

    /// Intern-time flags drive substitution: a param-free type comes back unchanged,
    /// and params are replaced through Adt args and tuples.
    #[test]
    fn flags_and_subst() {
        let mut g = GlobalTys::new();
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let plain = g.mk_vec(I32);
        assert!(!g.flags(plain).contains_param());
        assert_eq!(subst(&mut g, plain, &[GenericArg::Ty(BOOL)]), plain);
        let generic = g.mk_vec(p0);
        assert!(g.flags(generic).contains_param());
        let want = g.mk_vec(BOOL);
        assert_eq!(subst(&mut g, generic, &[GenericArg::Ty(BOOL)]), want);
        let pair_args = g.intern_tys(&[p0, I32]);
        let pair = g.intern(TyKind::Tuple(pair_args));
        let want_args = g.intern_tys(&[BOOL, I32]);
        let want_pair = g.intern(TyKind::Tuple(want_args));
        assert_eq!(subst(&mut g, pair, &[GenericArg::Ty(BOOL)]), want_pair);
        let proj_args = g.intern_args(&[GenericArg::Ty(p0)]);
        let proj = g.intern(TyKind::Projection(AssocId(fake_def(9)), proj_args));
        assert!(g.flags(proj).contains_projection() && g.flags(proj).contains_param());
    }

    /// Elaboration adds supertraits to a fixpoint, adds each binding as an `AssocEq`
    /// under the binder that carried it, and deduplicates in first occurrence order.
    #[test]
    fn elaborate_keeps_assoceq_under_its_binder() {
        let mut g = GlobalTys::new();
        let (tr, assoc, sup) = (fake_def(100), fake_def(101), fake_def(102));
        let args = g.intern_args(&[GenericArg::Ty(I32)]);
        let bindings = g.intern_bindings(&[(assoc, GenericArg::Ty(BOOL))]);
        let pred = Predicate::Trait(Binder { count: 1, value: TraitRef { def: tr, args, bindings } });
        let super_pred = Predicate::Trait(Binder::plain(TraitRef { def: sup, args, bindings: EMPTY_BINDINGS }));
        let supertraits = |t: &TraitRef| {
            if t.def == tr {
                vec![super_pred]
            } else if t.def == sup {
                vec![super_pred]
            } else {
                Vec::new()
            }
        };
        let out = elaborate(&g, &[pred, pred], &supertraits);
        let eq = Predicate::AssocEq(Binder { count: 1, value: AssocEqData { assoc, trait_args: args, ty: BOOL } });
        assert_eq!(out, [pred, eq, super_pred]);
        match out[1] {
            Predicate::AssocEq(b) => assert_eq!(b.count, 1, "the equality stays inside the for<'a> that wrote it"),
            other => panic!("expected AssocEq, got {other:?}"),
        }
    }

    /// A placeholder region is a proof-only universal: distinct from every other
    /// region form and from other placeholders, and not an inference variable.
    #[test]
    fn placeholder_regions_are_distinct() {
        assert_ne!(Region::Placeholder(0), Region::Placeholder(1));
        assert_ne!(Region::Placeholder(0), Region::Static);
        assert_ne!(Region::Placeholder(0), Region::Erased);
        assert_ne!(Region::Placeholder(0), Region::Infer(0));
        assert_ne!(Region::Placeholder(0), Region::Bound(0));
        assert_ne!(Region::Placeholder(0), Region::Param(0));
    }
}
