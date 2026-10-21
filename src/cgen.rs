// C backend. Each function is generated on its own (in parallel). Type helpers ("glue": drop, clone,
// eq, debug) are requested by structural type and generated once, after all functions.
use crate::ast::{BinOp, FmtKind, FmtSpec, UnOp};
use crate::check::Builtin;
use crate::check::collect::*;
use crate::diag::{SourceMap, Span};
use crate::ir::dropflags::Store;
use crate::ir::*;
use crate::ty::lang::{self, SigTy};
use crate::ty::layout::{self, EnumTag, Layout, Niche, ReprKind, niche_tag_value};
use crate::ty::iter::IterKind;
use crate::ty::*;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write;

mod clonefrom;
mod fmt;
mod sync;
mod hash;
mod split;
mod bytes;
mod unwind;
pub mod names;
mod own;
pub mod record;
mod slices;
mod kconst;
pub mod ll;
use unwind::Unw;

/// A body-independent type, so glue can be shared across functions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CTy {
    Unit,
    Bool,
    Char,
    Int(IntTy),
    Str,
    String,
    Vec(Box<CTy>),
    Option(Box<CTy>),
    /// `Result<T, E>`: variant 0 is `Ok(T)`, variant 1 is `Err(E)`.
    Result(Box<CTy>, Box<CTy>),
    Ref(Box<CTy>),
    /// A raw pointer (w-cinterop): the same C pointer as `Ref`, but its
    /// glue compares, orders, hashes, and prints the address itself.
    Ptr(Box<CTy>),
    /// A raw pointer to `str`, `[T]` or `dyn Tr` (tf-fatptr): the same C
    /// struct as the reference (`Str`, `Slice(T)` or `Dyn` inside), but
    /// no niche, and glue that compares the address and the metadata.
    FatPtr(Box<CTy>),
    Adt(AdtId),
    Chars,
    /// A tuple, emitted as a generated struct with fields f0, f1, ... (W-CORELANG).
    Tuple(Vec<CTy>),
    /// An array, emitted as a generated struct holding `v[len]` (W-CORELANG).
    Array(Box<CTy>, u64),
    /// A slice reference value or slice place: a generated fat struct holding
    /// `ptr` and `len` (W-CORELANG), the same role `lust_str` plays for `&str`.
    Slice(Box<CTy>),
    /// A float, as a C `float` or `double` (W-CORELANG).
    Float(FloatTy),
    /// A function pointer value: parameter types and return type.
    /// Emitted as a generated typedef that carries the out-pointer
    /// return convention for large returns (W-CGEN).
    FnPtr(Vec<CTy>, Box<CTy>),
    /// A `Box<T>`: a plain owning `T*` (never null, so it keeps
    /// the pointer niche).
    Boxed(Box<CTy>),
    /// An `Rc<T>`: a pointer to the generated counted header
    /// (`strong`, `weak`, then the value), also never null.
    Rc(Box<CTy>),
    /// A `&dyn Trait` or `&mut dyn Trait` value, or a dyn place (the
    /// fat value stands for it, as for slices): the runtime's
    /// `lust_dyn` (data pointer and vtable, ARCH 2.8).
    Dyn,
    /// A `Box<dyn Trait>`: an owning `lust_dyn` whose data points at
    /// the heap value (distinct from `Boxed(Dyn)`, a `Box<&dyn Tr>`).
    BoxDyn,
    /// An `Rc<dyn Trait>`: an owning `lust_dyn` whose data points at
    /// the value inside the Rc allocation, right after its two counts.
    RcDyn,
    /// A `rc::Weak<T>`: the same counted-header pointer as `Rc<T>`, or
    /// `UINTPTR_MAX` for `Weak::new()` (W-STD-A).
    Weak(Box<CTy>),
    /// A `rc::Weak<dyn Trait>` (false) or `sync::Weak<dyn Trait>`
    /// (true): the `lust_dyn` of the `Rc<dyn Trait>` or `Arc<dyn
    /// Trait>` it came from, its data `UINTPTR_MAX` when dangling
    /// (cgen/own.rs).
    WeakDyn(bool),
    /// A `rc::Weak<str>`/`rc::Weak<[T]>` (false) or `sync::Weak<..>`
    /// (true): the fat value of the `Rc` or `Arc` it came from, as
    /// `CTy::Own` holds it (cgen/own.rs). There is no dangling form: std
    /// has no `Weak::new()` for an unsized value.
    WeakOwn(bool, Box<CTy>),
    /// A `RefCell<T>`: the generated struct `RCL_..` of the borrow
    /// flag `f0` (as Rust's `isize`) and the value `f1`.
    RefCell(Box<CTy>),
    /// A `Cell<T>`: the value itself in C; its own type for glue.
    Cell(Box<CTy>),
    /// A `Ref<T>` (false) or `RefMut<T>` (true) guard: a pointer to the
    /// `RefCell`'s struct; drop gives the borrow back.
    Guard(Box<CTy>, bool),
    /// A `vec::IntoIter<T>` (W-STD-A): the runtime's `lust_VecIter`,
    /// the moved-in buffer plus the front index of what it still owns.
    VecIter(Box<CTy>),
    /// An `array::IntoIter<T, N>` (fx-array-iter): a generated struct
    /// of the array itself and the front and back indexes of what it
    /// still owns (`f0`, `f1`, `f2`, as the tuple form held them).
    /// Its own type so drop and clone glue touch only that range.
    ArrayIter(Box<CTy>, u64),
    /// An `option::IntoIter<T>` (false) or `result::IntoIter<T>` (true):
    /// a generated struct of the one stored `Option<T>` (`f0`, as the
    /// tuple form held it). Its own type so its Debug glue writes core's
    /// text (`IntoIter { inner: Item { opt: .. } }`), not a tuple's.
    OptIter(bool, Box<CTy>),
    /// A `vec::Drain<T>`: the runtime's `lust_VecDrain`, a pointer to
    /// the drained Vec plus its range bookkeeping.
    VecDrain(Box<CTy>),
    /// A `string::Drain`: the same runtime struct over the String.
    StrDrain,
    /// A `core::fmt` struct (W-STD-B): the runtime's `lust_Formatter`
    /// or Debug builder (src/runtime/fmt.h).
    Fmt(crate::ty::fmt::FmtTy),
    /// A `process::ExitCode`: its status byte as a `uint8_t`.
    ExitCode,
    /// A `Box<[T]>`: the slice's fat `{ptr, len}` struct, owning its
    /// elements and buffer; a deref is the slice place itself.
    BoxSlice(Box<CTy>),
    /// An owning pointer to an unsized value (w-unsized, cgen/own.rs):
    /// `Box<str>`, `Rc<str>`, `Arc<[T]>`, `Arc<dyn Tr>`. The second
    /// part is the pointee place (`Str`, `Slice(T)`, or `Dyn`), and the
    /// C value is that place's fat form; a deref is the place itself.
    /// The Rc and Arc forms point at the value, with the two counts in
    /// the 16 bytes before it.
    Own(own::Owner, Box<CTy>),
    /// A `RefCell<dyn Tr>` place, or a reference to one (w-unsized,
    /// cgen/own.rs): `lust_dyn` whose data points at the cell (borrow
    /// flag first, then the value) and whose vtable is the value's.
    DynCell,
    /// A `Ref<dyn Tr>` (false) or `RefMut<dyn Tr>` (true): the same fat
    /// form as `DynCell`; a deref is the value's dyn place.
    DynGuard(bool),
    /// A `Mutex<dyn Tr>` place or reference, and a `MutexGuard<dyn Tr>`
    /// (true): `lust_dyn` whose data points at the lock (the futex word,
    /// the poison byte, then the value), with the value's vtable.
    DynLock(bool),
    /// A `std::sync` or `std::thread` type and its type argument (`Unit`
    /// for the atomics), emitted by cgen/sync.rs (W-THREADS).
    Sync(crate::ty::sync::SyncTy, Box<CTy>),
    /// An unsized newtype (W-SHIM: `OsStr`, `Path`) and a reference to
    /// it: the C form of its unsized field (the second part), as `Str`
    /// stands for both `str` and `&str`. The Adt keeps its identity for
    /// glue (Debug, PartialEq, Ord call the newtype's own impls).
    Unsized(AdtId, Box<CTy>),
    /// `std::thread::AccessError` (W-TLS): a unit struct (`lust_Unit`)
    /// whose Debug text is its name.
    AccessError,
    /// A hashed collection or std hasher (W-STD-B, cgen/hash.rs), with
    /// its type args: `HashMap [K, V, S]` and `HashSet [T, S]` are a
    /// generated `{ lust_hash_table t; S s; }`; the hashers are runtime
    /// structs.
    Hash(crate::ty::hash::HashTy, Vec<CTy>),
}

/// One step of a move path in codegen (see `FnGen::move_paths`): a
/// field of a struct, tuple, `Option` payload, or of the variant a
/// `Downcast` chose; a variant view; or an array element at a
/// constant index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    Field(u32),
    Downcast(u32),
    Elem(u64),
    /// Through a `Box`: the one deref a move can go through.
    Deref,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Glue {
    Drop,
    Clone,
    /// `void clonefrom_T(T *d, T *s)`: `Clone::clone_from` by
    /// structure or core's body (cgen/clonefrom.rs).
    CloneFrom,
    Eq,
    Debug,
    /// Three-way comparison by structure: `int8_t cmp_T(T *a, T *b)`
    /// gives -1 (less), 0 (equal), 1 (greater), or 2 (unordered: a
    /// float NaN decided it), as derived and core `PartialOrd` order.
    Cmp,
    /// Like `Cmp`, but `PartialOrd::partial_cmp` order where it can
    /// differ from `Ord::cmp`: a written `partial_cmp` is called even
    /// when an `Ord` impl exists, and composite types compare their
    /// parts with `PCmp`. Only the sort adapters ask for it (std's
    /// sort compares with `lt`).
    PCmp,
    /// `T default_T(void)`: the value derived and core `Default` build.
    Default,
    /// Display of a type with a user `impl Display` (cgen/fmt.rs).
    Display,
    /// The slow path of a `thread_local!` access, keyed by the cell
    /// type `(u8, T)` (state byte, value; runtime/thread.c):
    /// `C *tlsinit_C(C *c, void *init)` makes the value with `init` (an
    /// `fn() -> T` pointer) and returns the cell, or NULL once destroyed.
    TlsInit,
    /// `void tlsdtor_C(void *c)`: a cell's thread-exit destructor (state
    /// destroyed, then the value's drop), keyed like `TlsInit`.
    TlsDtor,
    /// The hashed collections (cgen/hash.rs, W-STD-B): `hv_<T,H,..>`
    /// feeds a value to a hasher (key `(T, H, &[u8])`); per table,
    /// `hk_` hashes a key with the map's builder, `hof_`/`heq_`/`hcl_`
    /// are the core's hash-of, equality, and clone callbacks; per
    /// (table, lookup type Q), `hkq_` and `heqq_` (key `(table, Q)`).
    HashValue,
    HashKey,
    HashOf,
    HashEq,
    HashClone,
    HashKeyQ,
    HashEqQ,
    /// `heqe_`: the Entry search's equality, `stored == probe`.
    HashEqEntry,
    /// `hdr_`: the core's element drop callback.
    HashDrop,
    /// `hone_`: `BuildHasher::hash_one` of a value with a builder (key
    /// `(S, T)`).
    HashOne,
}

/// Maps a semantic type to its body-independent C form. Builtin Adts reach this
/// through the v2 compat helpers; kinds the subset cannot form yet map to `Unit`,
/// as inference leftovers did before. They gain real C forms with their features.
pub fn cty(tys: &impl TyIntern, t: Ty) -> CTy {
    match tys.kind(t) {
        TyKind::Bool => CTy::Bool,
        TyKind::Char => CTy::Char,
        TyKind::Int(i) => CTy::Int(i),
        TyKind::Float(f) => CTy::Float(f),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            CTy::FnPtr(tys.tys_of(b.value.inputs).iter().map(|&e| cty(tys, e)).collect(), Box::new(cty(tys, b.value.output)))
        }
        TyKind::FnDef(..) => CTy::Unit,
        TyKind::Str => CTy::Str,
        TyKind::Tuple(ts) => CTy::Tuple(tys.tys_of(ts).iter().map(|&e| cty(tys, e)).collect()),
        // A closure value is exactly a tuple of its captures (ARCH 4.5);
        // a closure with no captures is zero-sized like `()`.
        TyKind::Closure(_, a) => {
            let fields: Vec<CTy> = tys.args(a).iter().filter_map(|g| g.as_ty()).map(|e| cty(tys, e)).collect();
            if fields.is_empty() { CTy::Unit } else { CTy::Tuple(fields) }
        }
        TyKind::Array(e, c) => {
            let n = match tys.const_kind(c) {
                ConstKind::Int(n) => n as u64,
                _ => 0,
            };
            CTy::Array(Box::new(cty(tys, e)), n)
        }
        TyKind::Slice(e) => CTy::Slice(Box::new(cty(tys, e))),
        TyKind::Dyn(..) => CTy::Dyn,
        TyKind::Ref(_, _, e) => ref_cty(tys, e),
        TyKind::RawPtr(_, e) => match tys.kind(e) {
            TyKind::Str => CTy::FatPtr(Box::new(CTy::Str)),
            TyKind::Slice(el) => CTy::FatPtr(Box::new(CTy::Slice(Box::new(cty(tys, el))))),
            TyKind::Dyn(..) => CTy::FatPtr(Box::new(CTy::Dyn)),
            _ => CTy::Ptr(Box::new(cty(tys, e))),
        },
        // An unsized newtype is laid out as its field (W-SHIM).
        TyKind::Adt(d, a) if let Some(f) = tys.unsized_field(d) => {
            // A generic one lays out as its instance's field.
            let f = if tys.args(a).is_empty() { f } else { tys.unsized_inst_field(d, a).unwrap_or(f) };
            match tys.local_adt(t) {
                Some(a) => CTy::Unsized(a, Box::new(cty(tys, f))),
                None => cty(tys, f),
            }
        }
        TyKind::Adt(..) => match tys.builtin_of(t) {
            Some(BuiltinTy::String) => CTy::String,
            Some(BuiltinTy::Vec) => CTy::Vec(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            _ if let Some(o) = own::own_cty(tys, t) => o,
            _ if let Some(w) = own::weak_dyn_cty(tys, t) => w,
            Some(BuiltinTy::Boxed | BuiltinTy::Rc) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                if tys.builtin_of(t) == Some(BuiltinTy::Boxed) { CTy::BoxDyn } else { CTy::RcDyn }
            }
            Some(BuiltinTy::Boxed) => match tys.boxed_slice_elem(t) {
                Some(e) => CTy::BoxSlice(Box::new(cty(tys, e))),
                None => CTy::Boxed(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            },
            Some(BuiltinTy::Rc) => CTy::Rc(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Option) => CTy::Option(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Result) => {
                let (a, b) = tys.result_args(t).unwrap_or((ERROR, ERROR));
                CTy::Result(Box::new(cty(tys, a)), Box::new(cty(tys, b)))
            }
            Some(BuiltinTy::Chars) => CTy::Chars,
            Some(BuiltinTy::ExitCode) => CTy::ExitCode,
            Some(BuiltinTy::Iter(k)) => iter_cty(tys, t, k),
            Some(BuiltinTy::Fmt(k)) => CTy::Fmt(k),
            Some(BuiltinTy::Weak) => CTy::Weak(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::RefCell) if crate::check::own::dyn_cell_elem(tys, t).is_some() => CTy::DynCell,
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Mutex)) if crate::check::own::dyn_lock_elem(tys, t).is_some() => CTy::DynLock(false),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::MutexGuard)) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                CTy::DynLock(true)
            }
            Some(BuiltinTy::RefGuard | BuiltinTy::RefMutGuard) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                CTy::DynGuard(tys.builtin_of(t) == Some(BuiltinTy::RefMutGuard))
            }
            Some(BuiltinTy::RefCell) => CTy::RefCell(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Cell) => CTy::Cell(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::RefGuard) => CTy::Guard(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR))), false),
            Some(BuiltinTy::RefMutGuard) => CTy::Guard(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR))), true),
            Some(BuiltinTy::Sync(k)) => CTy::Sync(k, Box::new(tys.adt_first_ty_arg(t).map_or(CTy::Unit, |e| cty(tys, e)))),
            // A `thread_local!` key is its slot word (runtime/thread.c);
            // `AccessError` is a unit struct.
            Some(BuiltinTy::LocalKey) => CTy::Int(IntTy::U64),
            Some(BuiltinTy::AccessError) => CTy::AccessError,
            Some(BuiltinTy::Hash(k)) => {
                let args = tys
                    .adt_parts(t)
                    .map(|(_, a)| tys.args(a).iter().filter_map(|g| g.as_ty()).map(|e| cty(tys, e)).collect())
                    .unwrap_or_default();
                CTy::Hash(k, args)
            }
            None => match crate::ty::c_adt_of(tys, t) {
                Some(a) => CTy::Adt(a),
                None => CTy::Unit,
            },
        },
        _ => CTy::Unit,
    }
}

/// The address of a raw pointer value `v` of C type `t` as a `void*`:
/// the data word of a fat pointer (tf-fatptr), the pointer itself
/// otherwise.
fn ptr_addr(v: &str, t: &CTy) -> String {
    match t {
        CTy::FatPtr(e) if **e == CTy::Dyn => format!("(({v}).data)"),
        CTy::FatPtr(_) => format!("((void*)({v}).ptr)"),
        _ => format!("((void*)({v}))"),
    }
}

/// True when `t` is a reference to an owning pointer whose C value is
/// the fat view of its data (`Rc<dyn Tr>`, `Box<dyn Tr>`, `Rc<str>`,
/// `Arc<[T]>`): its `as_ptr` is a copy of that value.
fn owning_fat_ref(t: &CTy) -> bool {
    match t {
        CTy::Ref(inner) => match &**inner {
            CTy::RcDyn | CTy::BoxDyn | CTy::BoxSlice(_) => true,
            CTy::Own(_, x) => matches!(**x, CTy::Str | CTy::Slice(_) | CTy::Dyn),
            _ => false,
        },
        _ => false,
    }
}

/// The C form of a reference to `e`: a slice or dyn reference is its
/// fat value, a reference to an unsized newtype is the newtype's own
/// fat form (W-SHIM), anything else a pointer.
fn ref_cty(tys: &impl TyIntern, e: Ty) -> CTy {
    match tys.kind(e) {
        TyKind::Slice(el) => CTy::Slice(Box::new(cty(tys, el))),
        TyKind::Dyn(..) => CTy::Dyn,
        TyKind::Adt(d, _) if tys.unsized_field(d).is_some() => cty(tys, e),
        _ if crate::check::own::dyn_cell_elem(tys, e).is_some() => CTy::DynCell,
        _ if crate::check::own::dyn_lock_elem(tys, e).is_some() => CTy::DynLock(false),
        _ => CTy::Ref(Box::new(cty(tys, e))),
    }
}

/// The C form of a builtin iterator (ty/iter.rs): a tuple of its
/// stored fields, built structurally (no type interning here), or the
/// runtime's `lust_VecIter` for `vec::IntoIter`.
fn iter_cty(tys: &impl TyIntern, t: Ty, k: IterKind) -> CTy {
    use crate::ty::iter::Field;
    let args: Vec<Ty> = tys.adt_parts(t).map(|(_, a)| tys.args(a).iter().map(|g| g.as_ty().unwrap_or(ERROR)).collect()).unwrap_or_default();
    let arg = |i: u8| args.get(i as usize).copied().unwrap_or(ERROR);
    if k == IterKind::VecIntoIter {
        return CTy::VecIter(Box::new(cty(tys, arg(0))));
    }
    if k == IterKind::OptionIntoIter || k == IterKind::ResultIntoIter {
        return CTy::OptIter(k == IterKind::ResultIntoIter, Box::new(cty(tys, arg(0))));
    }
    if k == IterKind::ArrayIntoIter {
        let n = match tys.kind(arg(1)) {
            crate::ty::TyKind::Array(_, c) => match tys.const_kind(c) {
                crate::ty::ConstKind::Int(n) => n as u64,
                _ => 0,
            },
            _ => 0,
        };
        return CTy::ArrayIter(Box::new(cty(tys, arg(0))), n);
    }
    // The hash iterators' state is the core's (cgen/hash.rs).
    if k.is_hash() {
        return CTy::Hash(crate::ty::hash::HashTy::of_iter(k), args.iter().map(|&a| cty(tys, a)).collect());
    }
    if k == IterKind::VecDrain {
        return CTy::VecDrain(Box::new(cty(tys, arg(0))));
    }
    if k == IterKind::StringDrain {
        return CTy::StrDrain;
    }
    let fields = k
        .fields()
        .iter()
        .map(|&f| match f {
            Field::Arg(i) => cty(tys, arg(i)),
            Field::Usize => CTy::Int(IntTy::Usize),
            Field::Bool => CTy::Bool,
            Field::OptArg(i) => CTy::Option(Box::new(cty(tys, arg(i)))),
            Field::OptRef(i, _) => CTy::Option(Box::new(CTy::Ref(Box::new(cty(tys, arg(i)))))),
            Field::SliceRef(i, _) => CTy::Slice(Box::new(cty(tys, arg(i)))),
            Field::VecArg(i) => CTy::Vec(Box::new(cty(tys, arg(i)))),
            Field::VecRefMut(i) => CTy::Ref(Box::new(CTy::Vec(Box::new(cty(tys, arg(i)))))),
            Field::StringRefMut => CTy::Ref(Box::new(CTy::String)),
            Field::PeekSlot(i) => CTy::Option(Box::new(CTy::Option(Box::new(iter_item_cty(tys, arg(i)))))),
            Field::Recv(i, owned) => {
                let r = CTy::Sync(crate::ty::sync::SyncTy::Receiver, Box::new(cty(tys, arg(i))));
                if owned { r } else { CTy::Ref(Box::new(r)) }
            }
            Field::Chars => CTy::Chars,
            Field::Str => CTy::Ref(Box::new(CTy::Str)),
        })
        .collect();
    CTy::Tuple(fields)
}

/// The C form of an iterator type's item, built without interning.
fn iter_item_cty(tys: &impl TyIntern, t: Ty) -> CTy {
    use IterKind as K;
    if tys.is_chars_ty(t) {
        return CTy::Char;
    }
    let Some((k, a)) = crate::ty::iter::iter_parts(tys, t) else { return CTy::Unit };
    let ref_to = |e: Ty| match tys.kind(e) {
        TyKind::Slice(el) => CTy::Slice(Box::new(cty(tys, el))),
        _ => CTy::Ref(Box::new(cty(tys, e))),
    };
    match k {
        K::SliceIter | K::SliceIterMut => ref_to(a[0]),
        K::Windows => CTy::Slice(Box::new(cty(tys, a[0]))),
        K::CharIndices => CTy::Tuple(vec![CTy::Int(IntTy::Usize), CTy::Char]),
        K::Flatten => iter_item_cty(tys, a[1]),
        K::OptionIntoIter => cty(tys, a[0]),
        K::VecIntoIter | K::Range | K::RangeInclusive | K::RangeFrom | K::VecDrain => cty(tys, a[0]),
        K::StringDrain => CTy::Char,
        K::Map | K::FilterMap | K::MapWhile => cty(tys, a[2]),
        K::Enumerate => CTy::Tuple(vec![CTy::Int(IntTy::Usize), iter_item_cty(tys, a[0])]),
        K::Zip => CTy::Tuple(vec![iter_item_cty(tys, a[0]), iter_item_cty(tys, a[1])]),
        K::Copied | K::Cloned => cty(tys, a[1]),
        K::MapIter | K::MapIterMut => CTy::Tuple(vec![CTy::Ref(Box::new(cty(tys, a[0]))), CTy::Ref(Box::new(cty(tys, a[1])))]),
        K::MapKeys | K::SetIter => CTy::Ref(Box::new(cty(tys, a[0]))),
        K::MapValues | K::MapValuesMut => CTy::Ref(Box::new(cty(tys, a[1]))),
        K::MapIntoIter | K::MapDrain => CTy::Tuple(vec![cty(tys, a[0]), cty(tys, a[1])]),
        K::MapIntoKeys | K::SetIntoIter | K::SetDrain | K::RepeatN | K::ArrayIntoIter => cty(tys, a[0]),
        K::MapIntoValues | K::ByNext => cty(tys, a[1]),
        K::StrSplit => CTy::Ref(Box::new(CTy::Str)),
        K::Args => CTy::String,
        K::SliceSplit | K::SliceSplitMut | K::ChunkBy | K::ChunkByMut => CTy::Slice(Box::new(cty(tys, a[0]))),
        // As `ty::iter::item_ty`: the chunk slices, the matches' `&str`
        // (with the byte offset for the indexed modes), UTF-16 units.
        K::Chunks | K::ChunksMut | K::ChunksExact | K::ChunksExactMut => CTy::Slice(Box::new(cty(tys, a[0]))),
        K::StrMatches => match crate::ty::iter::matches_mode(tys, a[1]) {
            Some(m) if m.indexed() => CTy::Tuple(vec![CTy::Int(IntTy::Usize), CTy::Ref(Box::new(CTy::Str))]),
            _ => CTy::Ref(Box::new(CTy::Str)),
        },
        K::EncodeUtf16 => CTy::Int(IntTy::U16),
        _ => iter_item_cty(tys, a[0]),
    }
}

/// The pointee of a reference CTy (a `&Rc<T>` argument's `Rc<T>`).
fn deref_cty(t: &CTy) -> CTy {
    match t {
        CTy::Ref(inner) => (**inner).clone(),
        other => other.clone(),
    }
}

fn int_c(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "int8_t",
        IntTy::I16 => "int16_t",
        IntTy::I32 => "int32_t",
        IntTy::I64 | IntTy::Isize => "int64_t",
        IntTy::U8 => "uint8_t",
        IntTy::U16 => "uint16_t",
        IntTy::U32 => "uint32_t",
        IntTy::U64 | IntTy::Usize => "uint64_t",
        // tcc has no __int128: the runtime's two-word structs (runtime.h).
        IntTy::I128 => "lust_i128",
        IntTy::U128 => "lust_u128",
    }
}

fn is128(i: IntTy) -> bool {
    matches!(i, IntTy::I128 | IntTy::U128)
}

/// A `lust_loc` naming a line of Rust 1.99's own std source, for a panic
/// rustc reports there (no `#[track_caller]`): `file` indexes
/// `lust_std_files` in panic.c (0 core/src/num/mod.rs, 1
/// core/src/char/methods.rs, 2 core/src/char/convert.rs, 3
/// alloc/src/vec/mod.rs, 4 core/src/cmp.rs, 5
/// core/src/iter/adapters/step_by.rs, 6
/// alloc/src/vec/spec_from_iter_nested.rs, 7
/// core/src/iter/traits/accum.rs, 8 core/src/iter/range.rs, 9
/// core/src/cell.rs, 10 std/src/thread/local.rs, 11 core/src/ops/arith.rs, 12
/// core/src/slice/index.rs, 13 core/src/iter/traits/exact_size.rs, 14
/// core/src/slice/mod.rs, 15 core/src/ops/function.rs, 16 std/src/env.rs,
/// and the std source markers' files after them: `stdloc::STD_FILES`),
/// plus 0x40 for `pow`. Lowering names one with `Span::std_site`.
/// `stdloc::STD_FILES` indexes of alloc's rc.rs and sync.rs (`collect`
/// into `Rc<[T]>` and `Arc<[T]>` panics there).
const STD_RC_RS: u64 = 30;
const STD_SYNC_RS: u64 = 31;

fn std_loc(file: u64, line: u64, col: u64) -> String {
    format!("{}ull", ((0xFF_FF00u64 + file) << 40) | (line << 20) | col)
}

/// The std location of an integer method that panics inside core
/// (`abs`, `pow`, signed wrapping/overflowing/saturating division):
/// the `int_impl!` or `uint_impl!` line for its type in
/// core/src/num/mod.rs.
fn num_loc(i: IntTy, pow: bool) -> String {
    let line = match i {
        IntTy::I8 => 379,
        IntTy::I16 => 404,
        IntTy::I32 => 429,
        IntTy::I64 => 454,
        IntTy::I128 => 479,
        IntTy::Isize => 559,
        IntTy::U8 => 586,
        IntTy::U16 => 1234,
        IntTy::U32 => 1290,
        IntTy::U64 => 1322,
        IntTy::U128 => 1354,
        IntTy::Usize => 1452,
    };
    std_loc(if pow { 0x40 } else { 0 }, line, 5)
}

/// Suffix of the runtime's checked-math helpers for this type.
fn int_fn(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 | IntTy::Isize => "i64",
        IntTy::U8 => "u8",
        IntTy::U16 => "u16",
        IntTy::U32 => "u32",
        IntTy::U64 | IntTy::Usize => "u64",
        IntTy::I128 => "i128",
        IntTy::U128 => "u128",
    }
}

pub fn ctype(t: &CTy) -> String {
    match t {
        CTy::Unit => "lust_Unit".into(),
        CTy::Bool => "uint8_t".into(),
        CTy::Char => "uint32_t".into(),
        CTy::Int(i) => int_c(*i).into(),
        CTy::Str => "lust_str".into(),
        CTy::String => "lust_String".into(),
        CTy::Vec(_) => "lust_Vec".into(),
        CTy::Ref(inner) if **inner == CTy::Str => "lust_str".into(),
        // `Box<dyn Tr>` and `Rc<dyn Tr>` are owning fat pointers whose
        // data points at the value (ARCH 2.8).
        CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => "lust_dyn".into(),
        CTy::Boxed(inner) => format!("{}*", ctype(inner)),
        CTy::Rc(inner) => format!("RcI_{}*", mangle(inner)),
        CTy::VecIter(_) => "lust_VecIter".into(),
        CTy::ArrayIter(..) => format!("AI_{}", mangle(t)),
        CTy::OptIter(..) => format!("OI_{}", mangle(t)),
        CTy::VecDrain(_) | CTy::StrDrain => "lust_VecDrain".into(),
        CTy::Weak(inner) => format!("RcI_{}*", mangle(inner)),
        CTy::RefCell(inner) => format!("RCL_{}", mangle(inner)),
        CTy::Cell(inner) => ctype(inner),
        CTy::Guard(inner, _) => format!("RCL_{}*", mangle(inner)),
        CTy::Ref(inner) => format!("{}*", ctype(inner)),
        CTy::Ptr(inner) => format!("{}*", ctype(inner)),
        CTy::FatPtr(inner) => ctype(inner),
        CTy::Adt(a) => names::adt(*a),
        CTy::Option(_) => format!("O_{}", mangle(t)),
        CTy::Result(..) => format!("R_{}", mangle(t)),
        CTy::ExitCode => "uint8_t".into(),
        CTy::AccessError => "lust_Unit".into(),
        CTy::BoxSlice(e) => ctype(&CTy::Slice(e.clone())),
        CTy::Own(_, x) | CTy::WeakOwn(_, x) => ctype(x),
        CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) => "lust_dyn".into(),
        CTy::Sync(k, e) => sync::sync_ctype(*k, e),
        CTy::Chars => "lust_Chars".into(),
        CTy::Tuple(_) => format!("Tup_{}", mangle(t)),
        CTy::Array(..) => format!("Arr_{}", mangle(t)),
        CTy::Slice(_) => format!("Sl_{}", mangle(t)),
        CTy::Float(f) => (*f).name().replace("f64", "double").replace("f32", "float"),
        CTy::FnPtr(..) => format!("Fp_{}", mangle(t)),
        CTy::Dyn => "lust_dyn".into(),
        CTy::Fmt(k) => fmt_ctype(*k).into(),
        CTy::Unsized(_, inner) => ctype(inner),
        CTy::Hash(k, _) => hash::hash_ctype(*k, &mangle(t)),
    }
}

/// The (size, align) of the runtime struct of one `core::fmt` type
/// (src/runtime/fmt.h, x86_64 and aarch64 alike).
fn fmt_size_align(k: crate::ty::fmt::FmtTy) -> (u64, u64) {
    use crate::ty::fmt::FmtTy as F;
    match k {
        F::Formatter | F::DebugTuple => (24, 8),
        F::Arguments => (40, 8),
        F::DebugStruct | F::DebugList | F::DebugSet | F::DebugMap => (16, 8),
    }
}

/// The runtime struct of one `core::fmt` type.
fn fmt_ctype(k: crate::ty::fmt::FmtTy) -> &'static str {
    use crate::ty::fmt::FmtTy as F;
    match k {
        F::Formatter => "lust_Formatter",
        // A `format_args!` value: its site's formatter fn and arguments
        // (cgen/fmt.rs `format_args_value`).
        F::Arguments => "lust_Arguments",
        F::DebugStruct => "lust_DebugStruct",
        F::DebugTuple => "lust_DebugTuple",
        F::DebugList | F::DebugSet => "lust_DebugList",
        F::DebugMap => "lust_DebugMap",
    }
}

/// The C name fragment of `t`, used in type names (`O_<m>`, `Tup_<m>`) and glue names
/// (`drop_<m>`, `clone_<m>`). It must be injective: two different types with one fragment
/// give two C definitions with one name. Every type constructor gets its own token, every
/// token ends in `_` and has no other `_`, and each token fixes how many child tokens follow
/// (tuples and fn pointers encode their arity, arrays their length). So the fragment is a
/// prefix (Polish) code: splitting on `_` gives one token list, which parses one way only.
fn mangle(t: &CTy) -> String {
    let mut s = String::new();
    mangle_into(t, &mut s);
    s
}

/// Appends the tokens of `t` to `s` (see `mangle`).
fn mangle_into(t: &CTy, s: &mut String) {
    let tok = |s: &mut String, code: &str, kids: &[&CTy]| {
        s.push_str(code);
        s.push('_');
        kids.iter().for_each(|k| mangle_into(k, s));
    };
    match t {
        CTy::Unit => tok(s, "u", &[]),
        CTy::Bool => tok(s, "b", &[]),
        CTy::Char => tok(s, "c", &[]),
        CTy::Int(i) => tok(s, i.name(), &[]),
        CTy::Float(f) => tok(s, f.name(), &[]),
        CTy::Str => tok(s, "str", &[]),
        CTy::String => tok(s, "S", &[]),
        CTy::Chars => tok(s, "Chars", &[]),
        CTy::Dyn => tok(s, "dyn", &[]),
        CTy::BoxDyn => tok(s, "Bxdyn", &[]),
        CTy::RcDyn => tok(s, "Rcdyn", &[]),
        CTy::WeakDyn(arc) => tok(s, if *arc { "AWkdyn" } else { "Wkdyn" }, &[]),
        CTy::ExitCode => tok(s, "XC", &[]),
        CTy::AccessError => tok(s, "AE", &[]),
        CTy::Fmt(k) => tok(s, &format!("Fmt{}", *k as u8), &[]),
        // The kind fixes how many type arguments follow.
        CTy::Hash(k, args) => tok(s, &format!("H{}", *k as u8), &args.iter().collect::<Vec<_>>()),
        CTy::Adt(a) => tok(s, &names::adt(*a), &[]),
        CTy::Vec(e) => tok(s, "V", &[e]),
        CTy::Boxed(e) => tok(s, "Bx", &[e]),
        CTy::Rc(e) => tok(s, "Rc", &[e]),
        CTy::VecIter(e) => tok(s, "VI", &[e]),
        CTy::ArrayIter(e, n) => tok(s, &format!("AI{n}"), &[e]),
        CTy::OptIter(r, e) => tok(s, if *r { "RI" } else { "OI" }, &[e]),
        CTy::VecDrain(e) => tok(s, "VD", &[e]),
        CTy::StrDrain => tok(s, "SDr", &[]),
        CTy::Weak(e) => tok(s, "Wk", &[e]),
        CTy::RefCell(e) => tok(s, "RCL", &[e]),
        CTy::Cell(e) => tok(s, "Cl", &[e]),
        CTy::Guard(e, m) => tok(s, if *m { "GdM" } else { "Gd" }, &[e]),
        CTy::BoxSlice(e) => tok(s, "BS", &[e]),
        CTy::Own(k, e) => tok(s, k.code(), &[e]),
        CTy::WeakOwn(arc, e) => tok(s, if *arc { "AWkO" } else { "WkO" }, &[e]),
        CTy::DynCell => tok(s, "DCl", &[]),
        CTy::DynGuard(m) => tok(s, if *m { "DGdM" } else { "DGd" }, &[]),
        CTy::DynLock(g) => tok(s, if *g { "DLkG" } else { "DLk" }, &[]),
        CTy::Sync(k, e) => tok(s, &format!("Sy{}", *k as u32), &[e]),
        CTy::Ref(e) => tok(s, "R", &[e]),
        CTy::Ptr(e) => tok(s, "P", &[e]),
        CTy::FatPtr(e) => tok(s, "FP", &[e]),
        CTy::Option(e) => tok(s, "O", &[e]),
        CTy::Result(a, b) => tok(s, "Re", &[a, b]),
        CTy::Slice(e) => tok(s, "sl", &[e]),
        CTy::Array(e, n) => tok(s, &format!("Y{n}"), &[e]),
        CTy::Tuple(es) => tok(s, &format!("T{}", es.len()), &es.iter().collect::<Vec<_>>()),
        CTy::FnPtr(ps, r) => tok(s, &format!("fp{}", ps.len()), &ps.iter().chain([&**r]).collect::<Vec<_>>()),
        CTy::Unsized(a, e) => tok(s, &names::unsized_adt(*a), &[e]),
    }
}

/// Adds the named C types (structs, enums, Options) that `t` uses, including inside Vec and refs.
/// A `lust_str` expression for a `&str` or `&String` receiver.
fn str_of(v: &str, t: &CTy) -> String {
    match t {
        CTy::Ref(inner) if **inner == CTy::String => format!("lust_string_as_str({v})"),
        _ => v.to_string(),
    }
}

fn collect_types(t: &CTy, out: &mut HashSet<CTy>) {
    match t {
        CTy::Adt(_) => {
            out.insert(t.clone());
        }
        CTy::Option(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Result(a, b) => {
            out.insert(t.clone());
            collect_types(a, out);
            collect_types(b, out);
        }
        CTy::Tuple(es) => {
            out.insert(t.clone());
            es.iter().for_each(|e| collect_types(e, out));
        }
        CTy::Array(e, _) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Slice(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::FnPtr(ps, r) => {
            out.insert(t.clone());
            ps.iter().for_each(|e| collect_types(e, out));
            collect_types(r, out);
        }
        // A raw pointer names its pointee (`A2480*` for `*const Mapper`): its
        // forward typedef must be in the unit too.
        CTy::Vec(e) | CTy::Ref(e) | CTy::Ptr(e) | CTy::FatPtr(e) | CTy::Boxed(e) | CTy::VecIter(e) | CTy::VecDrain(e) | CTy::Cell(e) | CTy::Unsized(_, e) | CTy::Own(_, e) | CTy::WeakOwn(_, e) => {
            collect_types(e, out)
        }
        CTy::ArrayIter(e, n) => {
            out.insert(t.clone());
            collect_types(&CTy::Array(e.clone(), *n), out);
        }
        CTy::OptIter(_, e) => {
            out.insert(t.clone());
            collect_types(&CTy::Option(e.clone()), out);
        }
        CTy::Weak(e) => {
            out.insert(CTy::Rc(e.clone()));
            collect_types(e, out);
        }
        CTy::BoxSlice(e) => {
            out.insert(CTy::Slice(e.clone()));
            collect_types(e, out);
        }
        CTy::RefCell(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Guard(e, _) => {
            out.insert(CTy::RefCell(e.clone()));
            collect_types(e, out);
        }
        CTy::Rc(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Sync(k, e) => sync::sync_collect_types(*k, e, out),
        // Every hash type, so a unit that names one gets the core's
        // declarations (`type_decls`).
        CTy::Hash(k, args) => {
            out.insert(t.clone());
            if hash::has_struct(*k) {
                collect_types(&hash::elem_cty(t), out);
            }
            // The hash glue passes `&[u8]` to `Hasher::write`.
            if hash::is_table(*k) {
                collect_types(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))), out);
            }
            args.iter().for_each(|e| collect_types(e, out));
        }
        _ => {}
    }
}

/// Release C: a place reached through a pointer, as the pointer's C expression and a
/// byte offset (`FnGen::place`). `plain` is the ordinary deref, used while no field
/// offset has been added.
struct OffsetPlace {
    ptr: String,
    off: u64,
    fields: bool,
    plain: String,
}

impl OffsetPlace {
    /// The place as a C lvalue of type `t`.
    fn render(&self, t: &CTy) -> String {
        if self.fields { format!("(*({}*)((uint8_t*)({}) + {}))", ctype(t), self.ptr, self.off) } else { self.plain.clone() }
    }
}

/// The layout of `t` when its fields can be read by offset (a struct, enum or tuple
/// with a known C layout, not packed).
fn offset_layout(p: &Program, t: &CTy) -> Option<Layout> {
    match t {
        CTy::Adt(a) if p.adt(*a).repr.pack.is_none() => c_layout(p, t),
        CTy::Tuple(_) => c_layout(p, t),
        _ => None,
    }
}

/// The byte offset and C type of field `i` of `t` (in `variant` for an enum), when
/// it can be read by offset.
fn field_offset(p: &Program, t: &CTy, variant: Option<u32>, i: u32) -> Option<(u64, CTy)> {
    let l = offset_layout(p, t)?;
    match t {
        CTy::Adt(a) => {
            let adt = p.adt(*a);
            let v = variant.unwrap_or(0) as usize;
            let off = if adt.is_enum { *l.variant_offsets.get(v)?.get(i as usize)? } else { *l.field_offsets.get(i as usize)? };
            Some((off, cty(&p.tys, adt.variants.get(v)?.fields.get(i as usize)?.ty)))
        }
        CTy::Tuple(es) => Some((*l.field_offsets.get(i as usize)?, es.get(i as usize)?.clone())),
        _ => None,
    }
}

/// Builtins whose C opens nothing behind their operands: they read a container's own
/// fields (its length or emptiness: `->len`, a table's `->t`) or move values whole
/// (`drop`, `forget`, `swap`, `replace`), so release C defines no element or pointee type
/// for them (`FnGen::note_builtin`). `Vec::capacity` is not one: a zero-sized element's
/// capacity is `usize::MAX`, so it tests `sizeof`.
fn opens_nothing(b: Builtin) -> bool {
    use Builtin as B;
    matches!(
        b,
        B::MemDrop
            | B::MemForget
            | B::MemSwap
            | B::MemReplace
            | B::HintBlackBox
            | B::VecLen
            | B::VecIsEmpty
            | B::VecIterLen
            | B::VecDrainLen
            | B::SliceLen
            | B::SliceIsEmpty
            | B::HashLen
            | B::HashIsEmpty
            | B::HashCapacity
            | B::HashIterLen
            | B::StrLen
            | B::StrIsEmpty
            | B::StringLen
            | B::StringIsEmpty
            | B::StringCapacity
    )
}

/// Named types that `t` holds by value, so their C definitions must come first.
fn by_value_deps(t: &CTy, out: &mut Vec<CTy>) {
    match t {
        CTy::Adt(_) | CTy::Option(_) | CTy::Result(..) | CTy::Tuple(_) | CTy::Array(..) | CTy::Slice(_) | CTy::FnPtr(..) | CTy::RefCell(_) | CTy::ArrayIter(..) | CTy::OptIter(..) => {
            out.push(t.clone())
        }
        // `Rc`, `Weak`, and the `RefCell` guards are pointers to forward-
        // declared structs, so a recursive `Option<Rc<Node>>` field works.
        CTy::Cell(e) => by_value_deps(e, out),
        CTy::BoxSlice(e) => out.push(CTy::Slice(e.clone())),
        CTy::Own(_, e) | CTy::WeakOwn(_, e) => by_value_deps(e, out),
        // A lock holds its value; a `PoisonError` is its value's C type.
        CTy::Sync(k, _) if k.is_cell_struct() => out.push(t.clone()),
        CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => by_value_deps(e, out),
        // A pointer to a fn pointer still names its typedef, which has
        // no forward form (a closure capturing a fn pointer by ref, a
        // `Box<fn()>` inside an `Option` or a lock).
        CTy::Ref(inner) | CTy::Boxed(inner) if matches!(**inner, CTy::FnPtr(..) | CTy::Ref(_) | CTy::Boxed(_)) => by_value_deps(inner, out),
        CTy::Unsized(_, inner) | CTy::FatPtr(inner) => by_value_deps(inner, out),
        CTy::Hash(k, _) if hash::has_struct(*k) => out.push(t.clone()),
        _ => {}
    }
}

/// True when a value of `t` copies bitwise (Rust `Copy`). An Adt
/// instance copies only when its derive does and its own fields do: a
/// derived `Copy` on `Bound<T>` is `T: Copy` (`Bound<String>` clones
/// its string).
fn is_copy_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Unit
        | CTy::Bool
        | CTy::Char
        | CTy::Int(_)
        | CTy::Float(_)
        | CTy::FnPtr(..)
        | CTy::Ref(_)
        | CTy::Ptr(_)
        | CTy::FatPtr(_)
        | CTy::ExitCode
        | CTy::AccessError
        | CTy::Chars
        | CTy::Slice(_)
        | CTy::Unsized(..)
        | CTy::DynCell
        | CTy::DynLock(false)
        | CTy::Dyn => true,
        CTy::Option(e) => is_copy_c(p, e),
        CTy::Result(a, b) => is_copy_c(p, a) && is_copy_c(p, b),
        CTy::Tuple(es) => es.iter().all(|e| is_copy_c(p, e)),
        CTy::Array(e, _) => is_copy_c(p, e),
        CTy::ArrayIter(e, _) | CTy::OptIter(_, e) => is_copy_c(p, e),
        CTy::Adt(a) => {
            let adt = p.adt(*a);
            // A non-generic Adt's derive was checked against its fields.
            let instance = p.gx.adt_instance_of.get(a.0 as usize).is_some_and(|o| o.is_some());
            p.derives_of(*a).copy && (!instance || adt.variants.iter().all(|v| v.fields.iter().all(|f| is_copy_c(p, &cty(&p.tys, f.ty)))))
        }
        _ => false,
    }
}

/// True when a type holds no `Cell` or `RefCell` inline (Rust's
/// `Freeze`): pointers and buffers do not count, only by-value fields.
fn is_freeze_c(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> bool {
    match t {
        CTy::Cell(_) | CTy::RefCell(_) => false,
        // Every sync type holds an `UnsafeCell` inline.
        CTy::Sync(..) => false,
        CTy::Tuple(es) => es.iter().all(|e| is_freeze_c(p, e, seen)),
        CTy::Array(e, _) | CTy::Option(e) | CTy::ArrayIter(e, _) | CTy::OptIter(_, e) => is_freeze_c(p, e, seen),
        CTy::Result(a, b) => is_freeze_c(p, a, seen) && is_freeze_c(p, b, seen),
        CTy::Adt(a) => {
            if !seen.insert(*a) {
                return true;
            }
            p.adt(*a).variants.iter().all(|v| v.fields.iter().all(|f| is_freeze_c(p, &cty(&p.tys, f.ty), seen)))
        }
        _ => true,
    }
}

fn needs_drop_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::String | CTy::Vec(_) | CTy::Boxed(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::WeakOwn(..) | CTy::DynGuard(_) | CTy::DynLock(true) | CTy::Rc(_) | CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) | CTy::VecIter(_) | CTy::VecDrain(_) | CTy::StrDrain | CTy::Weak(_) | CTy::Guard(..) => true,
        CTy::RefCell(e) | CTy::Cell(e) => needs_drop_c(p, e),
        CTy::Sync(k, e) => sync::sync_needs_drop(p, *k, e),
        CTy::Hash(k, a) => {
            hash::is_table(*k)
                || k.is_owning_iter()
                || k.is_drain()
                || (matches!(*k, crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::VacantEntry) && a.first().is_some_and(|k| needs_drop_c(p, k)))
        }
        CTy::Option(e) => needs_drop_c(p, e),
        CTy::Result(a, b) => needs_drop_c(p, a) || needs_drop_c(p, b),
        CTy::Tuple(es) => es.iter().any(|e| needs_drop_c(p, e)),
        CTy::Array(e, _) => needs_drop_c(p, e),
        CTy::ArrayIter(e, _) | CTy::OptIter(_, e) => needs_drop_c(p, e),
        CTy::Adt(a) if p.is_manually_drop_adt(*a) => false,
        // `MaybeUninit<T>` never drops its bytes (a union in core).
        CTy::Adt(a) if p.def_of_adt(*a) == crate::ty::maybe_uninit_def() => false,
        CTy::Adt(a) => {
            p.gx.drop_methods.contains_key(a) || p.adt(*a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty)))
        }
        _ => false,
    }
}

/// A `&str` constant as a `lust_str`. An empty one points at address 1,
/// as rustc's dangling pointer of a zero-sized allocation (`"".as_ptr()`).
fn str_lit_c(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "((lust_str){(uint8_t*)(uintptr_t)1, 0})".into();
    }
    format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(bytes), bytes.len())
}

fn c_string_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() + 2);
    s.push('"');
    for &b in bytes {
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'?' => s.push_str("\\077"),
            0x20..=0x7e => s.push(b as char),
            _ => {
                let _ = write!(s, "\\{:03o}", b);
            }
        }
    }
    s.push('"');
    s
}

/// A byte blob as C string literal text, for one array initializer.
/// Adjacent literals of at most 256 source bytes each: C joins them
/// into one literal, and no single literal grows to megabyte size.
fn c_bytes_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() + bytes.len() / 64 + 2);
    s.push('"');
    let mut n = 0usize;
    for &b in bytes {
        if n == 256 {
            s.push_str("\" \"");
            n = 0;
        }
        n += 1;
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'?' => s.push_str("\\077"),
            0x20..=0x7e => s.push(b as char),
            _ => {
                let _ = write!(s, "\\{:03o}", b);
            }
        }
    }
    s.push('"');
    s
}

/// One blob as a C array value: a single generated array struct
/// whose `v` member takes the whole byte string at once.
fn bytes_array_lit(p: &Program, t: &CTy, bytes: &[u8]) -> String {
    if bytes.is_empty() { zero_lit(p, t) } else { format!("(({}){{ .v = {} }})", ctype(t), c_bytes_lit(bytes)) }
}

/// The generated code for one function, plus the glue it needs.
#[derive(Default)]
pub struct FnOut {
    /// The fn's C text (`code_text`, `code_len`, `has_code`).
    pub text: CText,
    pub glue: HashSet<(Glue, CTy)>,
    /// Named C types (structs, enums, Options) this function's code needs declared.
    pub types: HashSet<CTy>,
    /// A code generation failure the driver must report instead of
    /// using `text` (see `FnGen::bad_move`).
    pub error: Option<String>,
    /// Every fn slot `text` prints (`lust_fns[slot]`, `lust_tramps[slot]`,
    /// names built from a slot), its own included. Sorted, deduplicated.
    /// The daemon's slot-moved re-emit and dead-callee checks read it.
    pub used: Vec<u32>,
    /// Release C (`names`): the extern declarations `text` needs (callee and
    /// trampoline prototypes, location slots). Empty for numbered names.
    pub externs: BTreeSet<std::sync::Arc<str>>,
    /// Release C: types the code only points at (a `&T` local it never derefs):
    /// declared, not defined (`type_decls_with`). Empty for numbered names.
    pub named: HashSet<CTy>,
    /// The LLVM backend (cgen/ll.rs): the fn's LLVM IR definition and the declarations it
    /// names; `ll_c` holds its helpers' C (with the prelude and statics they read), and
    /// `text` only the C ABI wrapper and the trampoline. Empty for C bodies.
    pub ll: String,
    pub ll_decls: BTreeSet<String>,
    pub ll_c: String,
    /// The LLVM backend: the fn's size for cross-unit inlining (`ll::LlFn::cost`).
    pub ll_cost: u32,
    /// The LLVM backend: the fn ids whose C ABI wrapper or trampoline this fn's helpers' C
    /// names (`ll::CRefs`), read once here so a build does not scan every fn's C again.
    pub ll_c_refs: ll::CRefs,
    /// The fn's `#[inline]` attribute, which release C inline definitions follow.
    pub inline: InlineAttr,
    /// The digest of `text`, `ll` and `ll_c` (`FnOut::text_fp`), made on first use. B1 reads it
    /// instead of the texts, as a release build fingerprints every fn of the last build's units
    /// (`read_fp`); a front image keeps it with the fn. No text changes after `gen_fn` makes it.
    pub text_digest: std::sync::OnceLock<(u64, u64)>,
    /// `plain_fn_def`'s answer about the C text for inline copies (`FnOut::pick_info`), made on
    /// first use: `inline_pick` and B1's pick reads read it, not the text.
    pub pick: std::sync::OnceLock<Option<PickInfo>>,
    /// The ADTs whose layout the C text bakes in (`FnOut::layout_reads`), made on first use.
    pub layout: std::sync::OnceLock<BTreeSet<String>>,
}

/// What `inline_pick` and `inline_pick_hot` read of a fn's `plain_fn_def` (`FnOut::pick`).
#[derive(Clone, Copy)]
pub struct PickInfo {
    len: usize,
    code: usize,
    statics: bool,
    frame: bool,
}

/// A fn's C text: plain, as `gen_fn` makes it, or packed with other fns' texts in one zstd
/// frame (`pack_texts`). A front image save packs the plain ones, so a restore places far fewer
/// bytes, and a release build unpacks only the frames that hold the texts of the units it
/// assembles and of their inline copies (B1 reads `FnOut::text_fp`, inline picks
/// `FnOut::pick_info`).
pub enum CText {
    Plain(String),
    Packed { frame: std::sync::Arc<TextFrame>, at: u32, len: u32 },
}

impl Default for CText {
    fn default() -> CText {
        CText::Plain(String::new())
    }
}

/// Many fns' C texts, one after another, as one zstd frame (`CText::Packed`), with the text
/// unpacked on first use; `pack_texts` drops that before an image save.
pub struct TextFrame {
    z: Box<[u8]>,
    raw_len: u32,
    unpacked: std::sync::Mutex<Option<std::sync::Arc<String>>>,
}

impl TextFrame {
    /// The frame's text, unpacked once.
    fn text(&self) -> std::sync::Arc<String> {
        let mut u = self.unpacked.lock().unwrap_or_else(|e| e.into_inner());
        u.get_or_insert_with(|| {
            let raw = crate::image::unpack_bytes(&self.z, self.raw_len as usize);
            std::sync::Arc::new(String::from_utf8(raw).expect("a packed C text frame holds UTF-8"))
        })
        .clone()
    }
}

impl FnOut {
    /// The digest of the fn's texts (`text`, `ll`, `ll_c`), made once (`text_digest`).
    pub fn text_fp(&self) -> (u64, u64) {
        *self.text_digest.get_or_init(|| crate::driver::cache::hash128(&[self.code_text().as_bytes(), self.ll.as_bytes(), self.ll_c.as_bytes()], 12))
    }

    /// The fn's C text; a packed one is copied out of its unpacked frame.
    pub fn code_text(&self) -> std::borrow::Cow<'_, str> {
        match &self.text {
            CText::Plain(s) => std::borrow::Cow::Borrowed(s),
            CText::Packed { frame, at, len } => std::borrow::Cow::Owned(frame.text()[*at as usize..(*at + *len) as usize].to_string()),
        }
    }

    /// The length of the fn's C text.
    pub fn code_len(&self) -> usize {
        match &self.text {
            CText::Plain(s) => s.len(),
            CText::Packed { len, .. } => *len as usize,
        }
    }

    /// True when the fn has C text (a fn with none failed or has no body).
    pub fn has_code(&self) -> bool {
        self.code_len() > 0
    }

    /// `plain_fn_def`'s answer about the C text, made once (`pick`).
    pub fn pick_info(&self) -> Option<PickInfo> {
        *self.pick.get_or_init(|| plain_fn_def(&self.code_text()).map(|d| PickInfo { len: d.len, code: d.code, statics: d.statics, frame: d.frame.is_some() }))
    }

    /// The C names of the ADTs whose layout the fn's copy bakes in (`scan_layout_deps` of its
    /// definition and its frame's cleanup fn; `hot_pick`), made on first use.
    pub fn layout_reads(&self) -> &BTreeSet<String> {
        self.layout.get_or_init(|| {
            let code = self.code_text();
            let Some(d) = plain_fn_def(&code) else { return BTreeSet::new() };
            let mut out = scan_layout_deps(d.def);
            if let Some((_, post)) = d.frame {
                out.extend(scan_layout_deps(post));
            }
            out
        })
    }
}

/// The text of a frame (`TextFrame`) before packing: about 256 KB of C, so zstd finds the
/// repeats across fns, and a read of one fn unpacks no more than that.
const TEXT_FRAME: usize = 256 << 10;

/// Packs the plain C texts of `out` (indexed by slot) into zstd frames in slot order, and a frame
/// again with the plain texts when less than half of its text is still in use (the old texts of
/// changed fns stay in a frame until then). Then drops every frame's unpacked text. Run by a
/// front image save (`image::write_image`), in the saving process. Saves that do not pack (no
/// libzstd, `LUST_FRONT_ZSTD=0`) pack no texts.
pub fn pack_texts(out: &mut [FnOut]) {
    use std::sync::Arc;
    let packs = crate::image::packs();
    // The bytes of each frame that fns still use.
    let mut live: crate::intern::FxMap<*const TextFrame, u64> = Default::default();
    for f in out.iter() {
        if let CText::Packed { frame, len, .. } = &f.text {
            *live.entry(Arc::as_ptr(frame)).or_insert(0) += *len as u64;
        }
    }
    // The next frame's text, and its fns: (slot, offset, length).
    let mut all = String::new();
    let mut group: Vec<(usize, u32, u32)> = Vec::new();
    let flush = |out: &mut [FnOut], all: &mut String, group: &mut Vec<(usize, u32, u32)>| {
        // When libzstd fails, the texts stay as they are.
        if let Some(z) = crate::image::pack_bytes(all.as_bytes(), 3) {
            let frame = Arc::new(TextFrame { z, raw_len: all.len() as u32, unpacked: Default::default() });
            for &(slot, at, len) in group.iter() {
                out[slot].text = CText::Packed { frame: frame.clone(), at, len };
            }
        }
        all.clear();
        group.clear();
    };
    for slot in (0..out.len()).filter(|_| packs) {
        let take = match &out[slot].text {
            CText::Plain(s) => !s.is_empty(),
            CText::Packed { frame, .. } => live[&Arc::as_ptr(frame)] * 2 < frame.raw_len as u64,
        };
        if take {
            let at = all.len() as u32;
            all.push_str(&out[slot].code_text());
            group.push((slot, at, all.len() as u32 - at));
            if all.len() >= TEXT_FRAME {
                flush(out, &mut all, &mut group);
            }
        }
    }
    if !group.is_empty() {
        flush(out, &mut all, &mut group);
    }
    for f in out.iter() {
        if let CText::Packed { frame, .. } = &f.text {
            *frame.unpacked.lock().unwrap_or_else(|e| e.into_inner()) = None;
        }
    }
}

/// A fn's `#[inline]` attribute (`inline_attr`). rustc inlines a `#[inline]` fn into other
/// crates, and an `#[inline(always)]` one wherever it can; release C copies them past
/// the plain size limit (`inline_limit`), and never copies an `#[inline(never)]` fn.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum InlineAttr {
    #[default]
    None,
    Hint,
    Always,
    Never,
}

/// The LocalDefId to slot table cgen prints from, with a record of every
/// slot it gave out (`FnOut::used`, `GlueSet::used`). Read slots only
/// through `of`, so the record is complete.
pub(crate) struct Slots<'s> {
    map: &'s [u32],
    used: std::cell::RefCell<Vec<u32>>,
    externs: std::cell::RefCell<BTreeSet<String>>,
}

impl<'s> Slots<'s> {
    fn new(map: &'s [u32]) -> Self {
        Slots { map, used: Default::default(), externs: Default::default() }
    }

    /// The LocalDefId-to-slot table as a slice (`const_init` reads it).
    fn as_slice(&self) -> &[u32] {
        self.map
    }

    /// The slot of fn `f`, recorded as used.
    fn of(&self, f: LocalDefId) -> u32 {
        let s = self.map[f.0 as usize];
        self.used.borrow_mut().push(s);
        s
    }

    /// The callee text for a call of written fn `f` (`names::callee`).
    fn callee(&self, p: &Program, f: LocalDefId) -> String {
        let s = self.of(f);
        names::callee(p, f, s, &mut self.externs.borrow_mut())
    }

    /// A fn pointer value for fn `f` (`names::fn_value`).
    fn fn_value(&self, p: &Program, f: LocalDefId) -> String {
        let s = self.of(f);
        names::fn_value(p, f, s, &mut self.externs.borrow_mut())
    }

    /// A panic location in fn `f` (`names::loc`).
    fn loc(&self, f: LocalDefId, rel: u64, col: u64) -> String {
        let s = self.of(f);
        names::loc(s, rel, col, &mut self.externs.borrow_mut())
    }

    fn into_used(self) -> (Vec<u32>, BTreeSet<String>) {
        let mut v = self.used.into_inner();
        v.sort_unstable();
        v.dedup();
        (v, self.externs.into_inner())
    }
}

struct FnGen<'b, 'p> {
    p: &'p Program,
    body: &'b Body<'p>,
    out: String,
    glue: HashSet<(Glue, CTy)>,
    local_cty: Vec<CTy>,
    local_drop: Vec<bool>,
    /// Which whole-local drop flags stay runtime flags, and the value each test of a static
    /// one sees (`ir::dropflags`, drop elaboration): a static flag has no `d{l}`, no stores,
    /// and its tests are constants.
    dflags: crate::ir::dropflags::DropFlags,
    /// The (block, statement index) being emitted: where `dflags` looks up a static flag's
    /// value (an index equal to the statement count is the terminator).
    at: (u32, u32),
    /// Per local, the field paths the body moves out of it (partial
    /// moves) whose value needs a drop. Each has a C flag
    /// `m{local}_{index}` that a move clears; drops of the local
    /// read the flags and drop only what it still owns (Rust's drop
    /// elaboration). A zeroed field cannot stand for "moved": a type
    /// with a user `Drop` impl would run it on the zero value.
    move_paths: Vec<Vec<Vec<Step>>>,
    /// The body moves part of a drop-needing local in a way drop
    /// elaboration cannot track (through a reference or a
    /// non-constant index, or along a path that does not fit the
    /// local's type). The borrow checker rejects every such move
    /// today, so this is a backstop: it turns a silent double drop
    /// into a compile error if a future move form (for example a
    /// `Box` deref move) reaches code generation first.
    bad_move: bool,
    /// The first fn this body calls, takes as a fn pointer, or puts
    /// in a vtable that has no generated body (`has_generated_body`).
    /// Its slot would stay empty, so the call would read garbage or
    /// jump to null: `gen_fn` reports it as an internal error instead.
    bad_callee: Option<LocalDefId>,
    /// The first callable type a builtin's call cannot call
    /// (`sync::FnGen::callee_of_ty`: a `Box<dyn Fn>`, a `&&dyn Fn`):
    /// `gen_fn` reports it as an error instead of using the code.
    bad_callable: std::cell::Cell<Option<Ty>>,
    /// Locals that hold one constant array index (see
    /// `borrowck::const_index_locals`): a move out of `a[c]` is a
    /// partial move like a field move.
    const_index: std::collections::HashMap<Local, u64>,
    /// The panic location of each index local (see `Proj::Index`).
    index_spans: Vec<Option<Span>>,
    map: &'b SourceMap,
    /// Types in the signatures of called functions, needed for the call casts.
    sig_types: HashSet<CTy>,
    /// Release C: types the code names only behind a pointer (see `note_held`).
    sig_named: HashSet<CTy>,
    /// Line of the function's `fn` keyword. Locations are stored relative to it, so the C for
    /// an unchanged function stays valid when code above it moves.
    base_line: u32,
    /// LocalDefId to table slot. Slots are stable across edits; local ids are not.
    slots: &'b Slots<'b>,
    tmp: u32,
    /// This function's return value uses the out-pointer ABI (`ret_is_large`).
    ret_large: bool,
    /// R1 (`inplace`): local 0 is `(*out)`, the caller's storage (set in `function`).
    r1: bool,
    /// Locals whose address a `Ref`, `SliceOf` or `Subslice` rvalue takes somewhere in the
    /// body: a reference may reach them (R1's caller rule).
    borrowed: Vec<bool>,
    /// R3 (`inplace`): the assignment `emit_assign` writes now makes a value that cannot
    /// unwind at any point (`dropflags::may_panic_before_moves` is false).
    r3_value: bool,
    /// Vtable statics this function's unsizing coercions use, by vtable
    /// id, to their C names. Each function emits its own copies (named
    /// by its slot), so a unit never defines one twice.
    vtables: HashMap<u32, String>,
    /// Vtable statics and their method shims, emitted ahead of the function.
    prelude: String,
    /// Comparator adapters emitted so far (`sort_adapter`), for names.
    adapters: u32,
    /// Constructor fns this function's `ItemShim` values use, by item
    /// key (variant and fn pointer type), to their C names (`item_shim`).
    shims: HashMap<String, String>,
    /// panic=unwind state (cgen/unwind.rs); all empty under abort.
    /// The cleanup blocks, the cleanup entry of each statement by
    /// (block, index), and the action of the statement or call being
    /// emitted now.
    cleanup: Vec<bool>,
    stmt_unw: HashMap<(u32, u32), u32>,
    /// Per local, the one byte string blob it only holds
    /// (`ir::byte_blob_locals`): declared `static const` and never
    /// assigned, so a borrow of it has static storage.
    byte_blobs: Vec<Option<crate::ast::ByteBlob>>,
    unw: Option<Unw>,
    /// The value being assigned comes from a `Call` terminator.
    unw_call: bool,
    /// Unwind tables (`Program::unwind_tables`): this fn has a frame struct `L` (cgen/unwind.rs
    /// `frame_struct`), the ladder entry its block stored last in `L.st`, and whether the
    /// blocks being emitted are the cleanup fn's.
    zc_frame: bool,
    zc_st: Option<u32>,
    zc_in_cleanup: bool,
    /// Unwind tables: per block, the locals whose drop flag may be set at its terminator
    /// (`flags_maybe_set`), and the block being emitted.
    flags_at_term: Vec<Vec<bool>>,
    cur_bb: usize,
    /// A call's destination that `call_value` passes as the out-pointer of a large return
    /// instead of a temporary (`out_target`).
    call_out: Option<String>,
    /// Where the body's str literal caches go in `out` (the prologue's
    /// end), and the cache of each distinct literal (cgen/kconst.rs).
    kdecl_at: Option<usize>,
    kstrs: HashMap<Vec<u8>, usize>,
    /// Release builds: promoted locals whose value codegen computed at
    /// compile time (`kconst::eval_promoted`), with no float and no
    /// pointer but strs in it. Each is static data with that value
    /// (its assignment never runs), interned once at the fn's entry
    /// (`kconst::kbatch_local`). Empty in dev builds.
    kstatic: crate::intern::FxMap<Local, crate::ty::consteval::ConstValue>,
    /// The `const_init` state for those values (they hold no pointer
    /// but strs, which read the literal slots, so it defines no pointee).
    kcx: kconst::StaticCx,
    /// The C value the fn's entry writes into each `kstatic` local that
    /// holds strs (`kstatic_decl`).
    kentry: HashMap<Local, String>,
    /// The fn's constants are data named by content, with no run-time interning
    /// (`kconst::kdata_ok`); `knames` holds each constant local's name (a place
    /// reads it in place of the local).
    kdata: bool,
    knames: HashMap<Local, String>,
    /// Release C: the place being emitted is only borrowed (`Rvalue::Ref`), so its
    /// type needs no definition (`place`).
    addr_only: bool,
}

/// A layout with no field or niche detail, for runtime struct types whose
/// C form is fixed in runtime.h (`lust_String`, `lust_Vec`, and kin).
fn plain_layout(size: u64, align: u64) -> Layout {
    Layout { size, align, field_offsets: Vec::new(), variant_offsets: Vec::new(), niche: None, enum_tag: None, uninhabited: false }
}

/// True when `type_decls` can emit an enum of this layout with the exact
/// Rust size: the tag or niche scalar is a C integer of at most 8 bytes,
/// or a 16-byte two-word 128-bit struct. Niche tag values may wrap the
/// scalar range; the readers below compare with wrapping arithmetic.
fn enum_is_exact(l: &Layout, variants: usize) -> bool {
    match l.enum_tag {
        Some(EnumTag::Explicit { size, .. }) => size <= 16,
        Some(EnumTag::NicheFilled { niche, .. }) => matches!(niche.scalar_size, 1 | 2 | 4 | 8 | 16),
        Some(EnumTag::None(_)) => true,
        // An uninhabited enum (no variants, or only absent ones) is
        // zero-sized, as in Rust, so a type holding it keeps its size.
        None => l.uninhabited && l.size == 0,
    }
}

/// The bit mask of a tag or niche scalar of `size` bytes.
fn scalar_mask(size: u64) -> u128 {
    if size * 8 >= 128 { u128::MAX } else { (1u128 << (size * 8)) - 1 }
}

/// A C literal for the raw bit pattern `bits` of a tag or niche scalar.
fn scalar_lit(bits: u128, size: u64, signed: bool) -> String {
    let ct = tag_c_type(size, signed);
    if size >= 16 {
        return format!("(({ct}){{{}ULL, {}ULL}})", bits as u64, (bits >> 64) as u64);
    }
    if signed && (bits >> (size * 8 - 1)) & 1 == 1 {
        let v = (bits as i128) - (1i128 << (size * 8));
        if v == i64::MIN as i128 { format!("(({ct})(-9223372036854775807LL - 1))") } else { format!("(({ct})({v}LL))") }
    } else {
        format!("(({ct})({bits}ULL))")
    }
}

/// The Rust layout of a CTy, when this file can emit a C type of exactly
/// that size, alignment, and field offsets. `None` means the type keeps
/// the legacy declaration-order emission below, with its old (wrong)
/// sizes: today that is by-value cycles, and enum shapes
/// `enum_is_exact` rejects. Every `Some` result is checked in the
/// emitted C by _Static_assert on sizeof and _Alignof (see `type_decls`).
///
/// The layout is computed over CTy, not over `Ty`, so glue types that
/// never existed as a semantic type (an Option of a reference, say) get
/// one too. The fat-pointer and String/Vec pointer niches are sound
/// because empty buffers and empty slices always carry the dangling
/// aligned pointer (see lust_string_new and lust_vec_with_capacity),
/// never null. Each Adt's layout is computed once per call (`Seen::done`):
/// a struct DAG whose fields share sub-types would otherwise cost one walk
/// per path.
///
/// In release C, every Adt laid out on the way is a `Layout` read of the
/// body being made (`Program::note_adt_layout`): a body may hold the type
/// only behind a pointer, which its type reads do not cover
/// (`Program::record_type_layout_reads`), while its C reads a field at an
/// offset or its LLVM IR gives the pointee's size (`dereferenceable`). Dev
/// C names fields and types, so its body text holds no such layout and
/// takes no read (a warm dev build checks fewer bodies again).
fn c_layout(p: &Program, t: &CTy) -> Option<Layout> {
    let tag = phase_tag();
    if tag != 0
        && let Some(hit) = LAYOUTS.with(|c| {
            let mut c = c.borrow_mut();
            if c.0 != tag {
                *c = (tag, crate::intern::FxMap::default());
            }
            c.1.get(t).cloned()
        })
    {
        return hit;
    }
    let l = c_layout_walk(p, t);
    if tag != 0 {
        LAYOUTS.with(|c| c.borrow_mut().1.insert(t.clone(), l.clone()));
    }
    l
}

thread_local! {
    /// The codegen phase this thread works in (`in_layout_phase`), or 0.
    static LAYOUT_PHASE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// This thread's `c_layout` answers in that phase, by C type.
    static LAYOUTS: std::cell::RefCell<(u64, crate::intern::FxMap<CTy, Option<Layout>>)> = std::cell::RefCell::new((0, crate::intern::FxMap::default()));
}

/// A new codegen phase (`in_layout_phase`): one program, frozen while it
/// runs.
pub fn layout_phase() -> u64 {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Runs `f` in codegen phase `tag`: `c_layout` keeps its answers on this
/// thread for the rest of the phase. A layout is a function of the
/// program and the C type, and the program does not change in a phase
/// (the driver's codegen of every body); outside one, nothing is kept.
pub fn in_layout_phase<R>(tag: u64, f: impl FnOnce() -> R) -> R {
    struct Restore(u64);
    impl Drop for Restore {
        fn drop(&mut self) {
            LAYOUT_PHASE.with(|c| c.set(self.0));
        }
    }
    let _restore = Restore(LAYOUT_PHASE.with(|c| c.replace(tag)));
    f()
}

/// The codegen phase whose `c_layout` answers this thread keeps, or 0. It is 0 while
/// release C records `Layout` reads for the body being made (a session that records
/// reads, such as a front image build): an answer kept from another body would skip
/// that body's reads (`c_layout`), and the body would keep a stale layout when one moves.
fn phase_tag() -> u64 {
    if names::release() && crate::check::derive_delta::open() {
        return 0;
    }
    LAYOUT_PHASE.with(std::cell::Cell::get)
}

/// This thread's layout of `t` in its codegen phase, when one was found.
fn phase_layout(t: &CTy) -> Option<Layout> {
    if phase_tag() == 0 {
        return None;
    }
    LAYOUTS.with(|c| c.borrow().1.get(t).cloned().flatten())
}

/// `c_layout` without the phase cache.
fn c_layout_walk(p: &Program, t: &CTy) -> Option<Layout> {
    /// The Adts on the walk (a by-value cycle has no layout) and the
    /// finished ones.
    #[derive(Default)]
    struct Seen {
        on: HashSet<AdtId>,
        done: HashMap<AdtId, Layout>,
    }
    fn go(p: &Program, t: &CTy, seen: &mut Seen) -> Option<Layout> {
        match t {
            CTy::Unit => Some(layout::zst_layout(1)),
            CTy::Bool => Some(layout::bool_layout()),
            CTy::Char => Some(layout::char_layout()),
            CTy::Int(i) => Some(layout::int_layout(*i)),
            CTy::Float(f) => Some(layout::float_layout(*f)),
            CTy::FnPtr(..) => Some(layout::ptr_layout()),
            CTy::Str => Some(layout::fat_ptr_layout()),
            CTy::String | CTy::Vec(_) => {
                // (ptr, len, cap) in runtime order; the pointer word is
                // never null (empty buffers dangle), and the capacity
                // word is capped at isize::MAX: both are niches, and
                // the capacity is the larger one.
                layout::struct_layout(
                    &[layout::ptr_layout(), layout::int_layout(IntTy::Usize), layout::cap_layout()],
                    layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
                )
                .ok()
            }
            CTy::Chars => Some(plain_layout(24, 8)),
            CTy::Fmt(k) => {
                let (size, align) = fmt_size_align(*k);
                Some(plain_layout(size, align))
            }
            // The C structs of cgen/hash.rs (`struct_fields`) and the
            // runtime's hasher types.
            CTy::Hash(k, args) => {
                use crate::ty::hash::HashTy;
                let c = layout::Repr { kind: ReprKind::C, ..layout::Repr::default() };
                match k {
                    HashTy::RandomState => Some(plain_layout(16, 8)),
                    HashTy::DefaultHasher => Some(plain_layout(72, 8)),
                    HashTy::BuildHasherDefault => Some(layout::zst_layout(1)),
                    HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry => {
                        let key = go(p, args.first()?, seen)?;
                        layout::struct_layout(&[layout::ptr_layout(), layout::int_layout(IntTy::U64), layout::ptr_layout(), key], c).ok()
                    }
                    HashTy::HashMap | HashTy::HashSet => layout::struct_layout(&[plain_layout(64, 8), go(p, args.last()?, seen)?], c).ok(),
                    // `{ lust_hash_iter it; }`, owning: `{ table; it; }`.
                    HashTy::IterPairs | HashTy::IterKeys | HashTy::IterValues => Some(plain_layout(40, 8)),
                    HashTy::IntoPairs | HashTy::IntoKeys | HashTy::IntoValues => Some(plain_layout(104, 8)),
                    // `{ table; orig; it; }`.
                    HashTy::DrainPairs | HashTy::DrainKeys => Some(plain_layout(112, 8)),
                }
            }
            CTy::ExitCode => Some(plain_layout(1, 1)),
            // A lock: its words, the poison flag, then the value (no
            // niche: `UnsafeCell`). `PoisonError<T>` is laid out as `T`.
            CTy::Sync(k, e) if k.is_cell_struct() => {
                let mut v = go(p, e, seen)?;
                v.niche = None;
                let mut fields: Vec<Layout> = sync::cell_words(*k).iter().map(|&i| layout::int_layout(i)).collect();
                fields.push(v);
                layout::struct_layout(&fields, layout::Repr { kind: ReprKind::C, ..layout::Repr::default() }).ok()
            }
            CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => go(p, e, seen),
            CTy::Sync(k, _) => sync::sync_layout(*k),
            CTy::AccessError => Some(plain_layout(0, 1)),
            CTy::Weak(_) | CTy::Guard(..) => Some(layout::ptr_layout()),
            // `UnsafeCell` hides the value's niche, as in Rust.
            CTy::Cell(e) => go(p, e, seen).map(|mut l| {
                l.niche = None;
                l
            }),
            CTy::RefCell(e) => {
                let mut v = go(p, e, seen)?;
                v.niche = None;
                layout::struct_layout(&[layout::int_layout(IntTy::Isize), v], layout::Repr { kind: ReprKind::C, ..layout::Repr::default() }).ok()
            }
            CTy::VecIter(_) => layout::struct_layout(
                &[layout::ptr_layout(), layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize)],
                layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
            )
            .ok(),
            CTy::VecDrain(_) | CTy::StrDrain => layout::struct_layout(
                &[
                    layout::ptr_layout(),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                ],
                layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
            )
            .ok(),
            CTy::Ref(inner) if **inner == CTy::Str => Some(layout::fat_ptr_layout()),
            CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => Some(layout::fat_ptr_layout()),
            CTy::Boxed(_) | CTy::Rc(_) => Some(layout::ptr_layout()),
            CTy::Ref(_) => Some(layout::ptr_layout()),
            // A raw pointer may be null: no niche (w-cinterop).
            CTy::Ptr(_) => Some(layout::raw_ptr_layout()),
            CTy::FatPtr(e) if **e == CTy::Dyn => Some(layout::dyn_raw_ptr_layout()),
            CTy::FatPtr(_) => Some(layout::fat_raw_ptr_layout()),
            CTy::Slice(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::WeakOwn(..) | CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) | CTy::Dyn | CTy::Unsized(..) => {
                Some(layout::fat_ptr_layout())
            }
            CTy::Tuple(es) => {
                let fields: Option<Vec<Layout>> = es.iter().map(|e| go(p, e, seen)).collect();
                layout::tuple_layout(&fields?).ok()
            }
            // As the tuple of its stored fields (array, front, back).
            CTy::ArrayIter(e, n) => {
                let arr = go(p, &CTy::Array(e.clone(), *n), seen)?;
                layout::tuple_layout(&[arr, layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize)]).ok()
            }
            // As the one-field tuple form it replaces.
            CTy::OptIter(_, e) => go(p, &CTy::Tuple(vec![CTy::Option(e.clone())]), seen),
            CTy::Array(e, 0) => Some(plain_layout(0, go(p, e, seen).map_or(1, |l| l.align))),
            CTy::Array(e, n) => layout::array_layout(&go(p, e, seen)?, *n).ok(),
            CTy::Option(e) => {
                let l = layout::enum_layout(&[vec![], vec![go(p, e, seen)?]], &[0, 1], layout::Repr::default()).ok()?;
                enum_is_exact(&l, 2).then_some(l)
            }
            CTy::Result(a, b) => {
                let l = layout::enum_layout(&[vec![go(p, a, seen)?], vec![go(p, b, seen)?]], &[0, 1], layout::Repr::default()).ok()?;
                enum_is_exact(&l, 2).then_some(l)
            }
            CTy::Adt(a) => {
                if let Some(l) = seen.done.get(a) {
                    return Some(l.clone());
                }
                // An Adt's layout, once found, holds in any walk of this
                // phase (`c_layout`); a cycle's None depends on the walk.
                if let Some(l) = phase_layout(t) {
                    return Some(l);
                }
                if !seen.on.insert(*a) {
                    return None;
                }
                if names::release() {
                    p.note_adt_layout(*a);
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let mut variants = Vec::with_capacity(adt.variants.len());
                    for v in &adt.variants {
                        let mut fields = Vec::with_capacity(v.fields.len());
                        for f in &v.fields {
                            fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                        }
                        variants.push(fields);
                    }
                    let discs: Vec<i128> = adt.variants.iter().map(|v| v.disc).collect();
                    match layout::enum_layout(&variants, &discs, adt.repr) {
                        Ok(l) if enum_is_exact(&l, adt.variants.len()) => Some(l),
                        _ => None,
                    }
                } else {
                    let mut fields = Vec::with_capacity(adt.variants[0].fields.len());
                    for f in &adt.variants[0].fields {
                        fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                    }
                    // `NonZero<T>` has zero as its niche and `MaybeUninit<T>`
                    // none (a union), as ty/layout.rs gives them.
                    let def = p.def_of_adt(*a);
                    layout::struct_layout(&fields, adt.repr).ok().map(|mut l| {
                        if def == crate::ty::nonzero_def() {
                            l.niche = Some(Niche { offset: 0, scalar_size: l.size, free: 1, start: 0 });
                        } else if def == crate::ty::maybe_uninit_def() {
                            l.niche = None;
                        }
                        l
                    })
                };
                seen.on.remove(a);
                if let Some(l) = &r {
                    seen.done.insert(*a, l.clone());
                }
                r
            }
        }
    }
    go(p, t, &mut Seen::default())
}

/// `Vec::capacity` of the `lust_Vec` or `lust_VecIter` that the C pointer
/// `v` points to, with C element type `et`. A zero-sized element stores
/// capacity 0, as RawVec does (so the capacity word stays a valid niche
/// source), and reports usize::MAX.
fn vec_cap(et: &str, v: &str) -> String {
    format!("(sizeof({et}) ? ({v})->cap : 0xffffffffffffffffULL)")
}

/// A C condition that is true when zeroed memory, read as `t`, is the
/// same value as the C lvalue `e`: Rust's `IsZero` test, which lets
/// `vec![e; n]` take zeroed memory and skip every clone. `z` names a
/// zeroed static of type `t` (the caller declares it when the condition
/// mentions it), for the discriminant zeroed memory holds. Scalars and
/// arrays of scalars test their bytes (no padding); tuples test each
/// field; an `Option` must hold the zeroed discriminant and, when that is
/// `Some`, a zero payload (so `None::<Box<T>>` passes when null is
/// `None`). None for other types: the caller fills by copy or clone.
fn zero_test(p: &Program, t: &CTy, e: &str, z: &str) -> Option<String> {
    let scalar = |t: &CTy| matches!(t, CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_));
    match t {
        CTy::Unit => Some("1".into()),
        _ if scalar(t) => Some(format!("lust_is_zeroed(&{e}, sizeof({e}))")),
        CTy::Array(el, _) if scalar(el) => Some(format!("lust_is_zeroed(&{e}, sizeof({e}))")),
        CTy::Tuple(es) => {
            let fs = es.iter().enumerate().map(|(i, el)| zero_test(p, el, &format!("{e}.f{i}"), &format!("{z}.f{i}")));
            let fs = fs.collect::<Option<Vec<_>>>()?;
            Some(if fs.is_empty() { "1".into() } else { format!("({})", fs.join(" && ")) })
        }
        CTy::Option(el) => {
            let (de, dz) = (disc_call(p, t, &format!("(&{e})")), disc_call(p, t, &format!("(&{z})")));
            let some = zero_test(p, el, &variant_field(p, t, e, 1, 0), &variant_field(p, t, z, 1, 0)).unwrap_or_else(|| "0".into());
            Some(format!("({de} == {dz} && ({de} == 0 || {some}))"))
        }
        _ => None,
    }
}

/// C integer type for an explicit enum tag or a niche scalar of `size`
/// bytes. Niche scalars are read and written as unsigned bit patterns.
fn tag_c_type(size: u64, signed: bool) -> &'static str {
    match (size, signed) {
        (1, false) => "uint8_t",
        (1, true) => "int8_t",
        (2, false) => "uint16_t",
        (2, true) => "int16_t",
        (4, false) => "uint32_t",
        (4, true) => "int32_t",
        (16, false) => "lust_u128",
        (16, true) => "lust_i128",
        (_, false) => "uint64_t",
        (_, true) => "int64_t",
    }
}

/// A zero compound literal of type `t`, in value position. Types the
/// layout path emits as structs or unions take the `{}` form: tcc
/// rejects `{0}` when the first member is an empty struct (size 0, or
/// a `lust_Unit` payload first in a niche-filled `Result<(), String>`).
/// Scalars keep `{0}`, which tcc needs for them.
fn zero_lit(p: &Program, t: &CTy) -> String {
    let ct = ctype(t);
    let aggregate = c_layout(p, t).is_some_and(|l| l.size == 0 || !l.field_offsets.is_empty() || !l.variant_offsets.is_empty());
    if aggregate { format!("(({ct}){{}})") } else { format!("(({ct}){{0}})") }
}

/// The discriminant values of an enum or Option CTy, in variant order.
fn adt_discs(p: &Program, t: &CTy) -> Vec<i128> {
    match t {
        CTy::Option(_) | CTy::Result(..) => vec![0, 1],
        CTy::Adt(a) => p.adt(*a).variants.iter().map(|v| v.disc).collect(),
        _ => Vec::new(),
    }
}

/// The integer type that holds the discriminant of an enum or Option
/// value of type `t` in rustc (`DiscriminantKind`): the enum's `repr`
/// type, else `isize`. None for a type that is not an enum.
fn disc_holder(p: &Program, t: &CTy) -> Option<IntTy> {
    match t {
        CTy::Option(_) | CTy::Result(..) => Some(IntTy::Isize),
        CTy::Adt(a) if p.adt(*a).is_enum => Some(p.adt(*a).repr.disc_holder()),
        _ => None,
    }
}

/// True when every discriminant equals its variant index, so a stored
/// tag value reads back as the index with no mapping.
fn discs_sequential(discs: &[i128]) -> bool {
    discs.iter().enumerate().all(|(i, &d)| d == i as i128)
}

/// A C literal for one discriminant value, cast to the tag type.
fn disc_lit(disc: i128, size: u64, signed: bool) -> String {
    scalar_lit((disc as u128) & scalar_mask(size), size, signed)
}

/// The C expression that reads the variant index of an enum or Option
/// value at the pointer expression `ptr`. The layout path stores the
/// discriminant value in the tag: sequential discriminants read
/// inline, the rest go through the generated `disc_` mapping helper.
/// Legacy types store the variant index in `tag` directly.
fn disc_call(p: &Program, t: &CTy, ptr: &str) -> String {
    match c_layout(p, t) {
        Some(l) => match l.enum_tag {
            // A 16-byte tag is a C struct: it cannot be read as one
            // integer, so it always goes through the helper.
            Some(EnumTag::Explicit { size, .. }) if size <= 8 && discs_sequential(&adt_discs(p, t)) => {
                format!("(({ptr})->u._tag)")
            }
            Some(EnumTag::Explicit { .. }) | Some(EnumTag::NicheFilled { .. }) => format!("disc_{}({ptr})", mangle(t)),
            Some(EnumTag::None(vi)) => vi.to_string(),
            _ => "0".into(),
        },
        None => format!("({ptr})->tag"),
    }
}

/// The `Utf8Error` value inside a std `FromUtf8Error` or `Utf8Error`
/// value `e` (synthetic std Adts, check/collect.rs); None for any other
/// type.
fn utf8_error_part(p: &Program, t: &CTy, e: &str) -> Option<String> {
    let CTy::Adt(a) = t else { return None };
    if p.tys.local_adt_of(crate::check::generics::from_utf8_error_def()) == Some(*a) {
        Some(format!("({e}).f1"))
    } else if p.tys.local_adt_of(crate::check::generics::utf8_error_def()) == Some(*a) {
        Some(format!("({e})"))
    } else {
        None
    }
}

/// The C field access for field `fi` of variant `vi` in the enum or
/// Option value expression `e`. Only Options differ between the layout
/// and legacy shapes; Adt enums keep `.u.v{vi}.f{fi}` in both.
fn variant_field(p: &Program, t: &CTy, e: &str, vi: usize, fi: usize) -> String {
    match t {
        CTy::Option(_) if c_layout(p, t).is_none() => format!("{e}.v"),
        _ => format!("{e}.u.v{vi}.f{fi}"),
    }
}

/// A C statement (no trailing newline) that stores variant `vi`'s
/// discriminant into the enum or Option value expression `e`. Empty
/// when the variant is the niche variant (its payload writes the niche
/// scalar) or the enum stores no tag.
fn disc_set(p: &Program, t: &CTy, e: &str, vi: usize) -> String {
    let Some(l) = c_layout(p, t) else { return format!("{e}.tag = {vi};") };
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => format!("{e}.u._tag = {};", disc_lit(adt_discs(p, t)[vi], size, signed)),
        Some(EnumTag::NicheFilled { variant, niche, first, start, .. }) => {
            if vi == variant {
                String::new()
            } else {
                format!("{e}.u._n._s = {};", scalar_lit(niche_tag_value(niche, first, start, vi), niche.scalar_size, false))
            }
        }
        _ => String::new(),
    }
}

/// Size and alignment of a CTy as the emitted C types lay it out under
/// the legacy emission: declaration order, natural alignment, a uint32
/// tag first in enums and Options. Used for the types `c_layout`
/// rejects, and only for the return-ABI threshold below, so it must
/// match the legacy C structs this file emits, nothing else.
fn c_size_align_legacy(p: &Program, t: &CTy) -> (u64, u64) {
    fn go(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> (u64, u64) {
        fn align_up(x: u64, a: u64) -> u64 {
            (x + a - 1) / a * a
        }
        fn fields(p: &Program, v: &Variant, seen: &mut HashSet<AdtId>) -> (u64, u64) {
            let (mut size, mut align) = (0u64, 1u64);
            for f in &v.fields {
                let (fs, fa) = go(p, &cty(&p.tys, f.ty), seen);
                size = align_up(size, fa) + fs;
                align = align.max(fa);
            }
            (align_up(size, align), align)
        }
        match t {
            CTy::Unit => (0, 1),
            CTy::Bool => (1, 1),
            CTy::Char => (4, 4),
            CTy::Int(i) => {
                let s = (i.bits() / 8) as u64;
                (s, if is128(*i) { 16 } else { s.min(8) })
            }
            CTy::Float(f) => match f {
                FloatTy::F32 => (4, 4),
                FloatTy::F64 => (8, 8),
            },
            CTy::FnPtr(..) => (8, 8),
            CTy::Str => (16, 8),
            CTy::String | CTy::Vec(_) | CTy::Chars => (24, 8),
            CTy::VecIter(_) => (32, 8),
            CTy::VecDrain(_) | CTy::StrDrain => (48, 8),
            CTy::Weak(_) | CTy::Guard(..) => (8, 8),
            CTy::Cell(e) => go(p, e, seen),
            CTy::RefCell(e) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(8);
                (align_up(align_up(8, ea) + es, align), align)
            }
            CTy::Fmt(k) => fmt_size_align(*k),
            CTy::ExitCode => (1, 1),
            CTy::Sync(k, e) if k.is_cell_struct() => {
                let (es, ea) = go(p, e, seen);
                let at = sync::cell_words(*k).iter().map(|i| i.bits() as u64 / 8).sum::<u64>();
                let align = ea.max(4);
                (align_up(align_up(at, ea) + es, align), align)
            }
            CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => go(p, e, seen),
            CTy::Sync(k, _) => sync::sync_layout(*k).map_or((8, 8), |l| (l.size, l.align)),
            CTy::AccessError => (0, 1),
            CTy::Hash(k, args) => match k {
                crate::ty::hash::HashTy::RandomState => (16, 8),
                crate::ty::hash::HashTy::DefaultHasher => (72, 8),
                crate::ty::hash::HashTy::BuildHasherDefault => (0, 1),
                k if k.is_owning_iter() => (104, 8),
                k if k.is_drain() => (112, 8),
                k if k.is_iter_form() => (40, 8),
                crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::OccupiedEntry | crate::ty::hash::HashTy::VacantEntry => {
                    // `{ table ptr, hash, slot ptr, K key }`
                    let (ks, ka) = args.first().map_or((0, 1), |k| go(p, k, seen));
                    let align = ka.max(8);
                    (align_up(align_up(24, ka) + ks, align), align)
                }
                _ => {
                    // `{ lust_hash_table t (8 words); S s; }`
                    let (ss, sa) = args.last().map_or((0, 1), |s| go(p, s, seen));
                    let align = sa.max(8);
                    (align_up(64 + ss, align), align)
                }
            },
            CTy::Ref(inner) if **inner == CTy::Str => (16, 8),
            CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => (16, 8),
            CTy::Boxed(_) | CTy::Rc(_) => (8, 8),
            CTy::Ref(_) | CTy::Ptr(_) => (8, 8),
            CTy::FatPtr(_) => (16, 8),
            CTy::Option(e) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(4);
                (align_up(align_up(4, ea) + es, align), align)
            }
            CTy::Result(a, b) => {
                // Legacy shape: a uint32 tag, then a union of the two
                // payloads, like a legacy two-variant Adt enum.
                let (as_, aa) = go(p, a, seen);
                let (bs, ba) = go(p, b, seen);
                let (es, ea) = (as_.max(bs), aa.max(ba));
                let align = ea.max(4);
                (align_up(align_up(4, ea) + es, align), align)
            }
            CTy::Tuple(es) => {
                if es.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    let (mut size, mut align) = (0u64, 1u64);
                    for e in es {
                        let (fs, fa) = go(p, e, seen);
                        size = align_up(size, fa) + fs;
                        align = align.max(fa);
                    }
                    (align_up(size, align), align)
                }
            }
            CTy::Array(e, n) => {
                let (es, ea) = go(p, e, seen);
                (es * (*n).max(1), ea)
            }
            CTy::OptIter(_, e) => go(p, &CTy::Tuple(vec![CTy::Option(e.clone())]), seen),
            CTy::ArrayIter(e, n) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(8);
                (align_up(align_up(es * (*n).max(1), 8) + 16, align), align)
            }
            CTy::Slice(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::WeakOwn(..) | CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) | CTy::Dyn | CTy::Unsized(..) => (16, 8),
            CTy::Adt(a) => {
                if !seen.insert(*a) {
                    // A by-value cycle has no finite size; check rejects
                    // it long before here. Report huge, never loop.
                    return (u64::MAX / 2, 8);
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let (mut usize_, mut ualign) = (0u64, 1u64);
                    for v in &adt.variants {
                        if !v.fields.is_empty() {
                            let (vs, va) = fields(p, v, seen);
                            usize_ = usize_.max(vs);
                            ualign = ualign.max(va);
                        }
                    }
                    if usize_ == 0 {
                        (4, 4)
                    } else {
                        let align = ualign.max(4);
                        (align_up(align_up(4, ualign) + usize_, align), align)
                    }
                } else if adt.variants[0].fields.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    fields(p, &adt.variants[0], seen)
                };
                seen.remove(a);
                r
            }
        }
    }
    go(p, t, &mut HashSet::new())
}

/// Size and alignment of a CTy as the emitted C types lay it out: the
/// Rust layout when `c_layout` is exact, the legacy layout otherwise.
fn c_size_align(p: &Program, t: &CTy) -> (u64, u64) {
    match c_layout(p, t) {
        Some(l) => (l.size, l.align),
        None => c_size_align_legacy(p, t),
    }
}

/// Returns over 32 bytes go through a hidden out-pointer (ARCH 4.5);
/// parameters stay by value, which keeps the slot cast simple.
fn ret_is_large(p: &Program, f: LocalDefId) -> bool {
    ret_by_out(p, &cty(&p.tys, p.fn_info(f).ret))
}

/// True when a C function returns `t` through a hidden out-pointer:
/// over 32 bytes, or a zero-sized type whose C struct holds an array
/// member (`[T; 0]`, `[No; 4]`, also in a tuple, struct, or `Cell`).
/// tcc 0.9.28 returns such a struct in a register, and the caller
/// stores a byte of it over its own frame (see `param_dropped` for the
/// same bug on parameters, and `zst_out_glue` for glue).
/// True when codegen may tell the C compiler that an exhaustive match's otherwise edge
/// (`Terminator::MatchExhausted`) never runs: release C of a build with neither debug
/// assertions nor overflow checks, unless LUST_RELEASE_UNREACHABLE=abort (a test switch; as
/// every LUST_RELEASE_ variable it is part of `release_c::codegen_key`).
fn assume_unreachable(p: &Program) -> bool {
    static ABORT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    names::release()
        && !p.debug_assertions
        && !p.overflow_checks
        && !*ABORT.get_or_init(|| std::env::var("LUST_RELEASE_UNREACHABLE").is_ok_and(|v| v == "abort"))
}

fn ret_by_out(p: &Program, t: &CTy) -> bool {
    let size = c_size_align(p, t).0;
    size > 32 || (size == 0 && zst_holds_array(p, t)) || split_ret_by_out(p, t, size)
}

/// `LUST_RELEASE_AGG_RET`: which 9-32 byte returns release C passes through the out pointer.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AggRet {
    /// `0`: none (the C ABI returns them).
    Off,
    /// Unset or `1`: the 9-16 byte ones that `crosses_eightbyte`.
    Split,
    /// `all`: every one (a stress switch for tests: every call site must agree).
    All,
}

fn agg_ret_mode() -> AggRet {
    static MODE: std::sync::OnceLock<AggRet> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("LUST_RELEASE_AGG_RET").as_deref() {
        Ok("0") => AggRet::Off,
        Ok("all") => AggRet::All,
        _ => AggRet::Split,
    })
}

/// Release C, outside the LLVM backend's C boundary (which keeps the C ABI): a 9-16 byte
/// return whose pieces do not follow the SysV split at byte 8 goes through the out pointer.
/// The C ABI returns it in two registers, bytes 0-7 and 8-15, so the caller rebuilds the
/// value from two 8-byte loads that span the narrower stores of its fields; after inlining,
/// SROA cannot split such a value (an access crosses byte 8), and the reload fails to
/// forward from the store buffer (`Option<TextRange>`: tag at 0, payload at 4-11).
fn split_ret_by_out(p: &Program, t: &CTy, size: u64) -> bool {
    let mode = agg_ret_mode();
    if mode == AggRet::Off || !(9..=32).contains(&size) || !names::release() || ll::on(p) {
        return false;
    }
    mode == AggRet::All || (size <= 16 && crosses_eightbyte(p, t, 0))
}

/// Release C (outside the LLVM backend) builds values in their final place, by the rules of
/// DEST-PROP-DESIGN.md. R1: a fn that returns through the out pointer builds its return value
/// in `(*out)` (no `l0`, no copy at the return), and a call passes as its out storage only a
/// fresh temporary or a whole local that holds no value and that no reference reaches. R3: an
/// assignment whose value cannot unwind, to a whole local that holds no value, writes the
/// local with no temporary. Both are on; `LUST_RELEASE_INPLACE` picks: `0` neither, `r1` or
/// `r3` one of them.
#[derive(Clone, Copy, Default)]
struct Inplace {
    r1: bool,
    r3: bool,
}

fn inplace(p: &Program) -> Inplace {
    static MODE: std::sync::OnceLock<Inplace> = std::sync::OnceLock::new();
    let mode = *MODE.get_or_init(|| match std::env::var("LUST_RELEASE_INPLACE").as_deref() {
        Ok("0") => Inplace::default(),
        Ok("r1") => Inplace { r1: true, r3: false },
        Ok("r3") => Inplace { r1: false, r3: true },
        _ => Inplace { r1: true, r3: true },
    });
    if names::release() && !ll::on(p) { mode } else { Inplace::default() }
}

/// True when a piece of a value of type `t`, placed at byte `base` of a larger value, starts
/// before byte 8 and ends after it. A piece is a scalar or an aggregate of at most 8 bytes,
/// which clang copies as one integer; a larger aggregate is looked into. A type this cannot
/// look into counts as crossing when it spans byte 8, unless it is made of 8-byte words.
fn crosses_eightbyte(p: &Program, t: &CTy, base: u64) -> bool {
    let (size, align) = c_size_align(p, t);
    if size == 0 || base >= 8 || base + size <= 8 {
        return false;
    }
    if size <= 8 {
        return true;
    }
    let Some(l) = c_layout(p, t) else { return true };
    let fields = |tys: &[CTy], offs: &[u64]| tys.len() != offs.len() || tys.iter().zip(offs).any(|(f, &o)| crosses_eightbyte(p, f, base + o));
    // An enum: its explicit tag (at byte 0), then every variant's fields.
    let variants = |vs: &[Vec<CTy>]| {
        let tag = matches!(l.enum_tag, Some(EnumTag::Explicit { size, .. }) if base + size > 8);
        tag || vs.len() != l.variant_offsets.len() || vs.iter().zip(&l.variant_offsets).any(|(tys, offs)| fields(tys, offs))
    };
    match t {
        CTy::Tuple(es) => fields(es, &l.field_offsets),
        CTy::Array(e, n) => {
            let stride = c_size_align(p, e).0;
            (0..*n).any(|i| crosses_eightbyte(p, e, base + i * stride))
        }
        CTy::Option(e) => variants(&[vec![], vec![(**e).clone()]]),
        CTy::Result(a, b) => variants(&[vec![(**a).clone()], vec![(**b).clone()]]),
        CTy::Adt(a) => {
            let adt = p.adt(*a);
            let tys: Vec<Vec<CTy>> = adt.variants.iter().map(|v| v.fields.iter().map(|f| cty(&p.tys, f.ty)).collect()).collect();
            if adt.is_enum {
                variants(&tys)
            } else {
                tys.first().is_none_or(|f| fields(f, &l.field_offsets))
            }
        }
        CTy::Cell(e) => crosses_eightbyte(p, e, base),
        // Pointers, lengths and counts: 8-byte words, which cross byte 8 only off an
        // 8-byte boundary (in a packed struct).
        _ if align >= 8 => base % 8 != 0,
        _ => true,
    }
}

/// True when the C struct of zero-sized type `t` holds an array member.
/// Every array in a zero-sized type has size 0, whatever its length.
/// Only the forms that embed a zero-sized value by value matter here:
/// the others (Option's tag, RefCell's flag, ...) are never size 0.
fn zst_holds_array(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Array(..) | CTy::ArrayIter(..) => true,
        CTy::Tuple(es) => es.iter().any(|e| zst_holds_array(p, e)),
        CTy::Cell(e) => zst_holds_array(p, e),
        CTy::Adt(a) => p.adt(*a).variants.iter().any(|v| v.fields.iter().any(|f| zst_holds_array(p, &cty(&p.tys, f.ty)))),
        _ => false,
    }
}

/// True when a by-value parameter of C type `t` is dropped from the C
/// signature and from every call. A zero-sized value carries no bits,
/// so the callee makes its local from a zero literal instead (see
/// `FnGen::function`). This is not optional: tcc 0.9.28 misplaces the
/// parameters after a zero-sized struct parameter that has a
/// zero-length array member, such as `[T; 0]` or `[[T; 0]; N]`, so
/// the callee reads garbage. Drop glue still runs once, in the
/// callee, through the local's drop flag.
fn param_dropped(p: &Program, t: &CTy) -> bool {
    c_size_align(p, t).0 == 0
}

/// True when a by-value parameter of C type `t` crosses the C call as a
/// pointer to a caller copy: its alignment is over 16, or it is a big
/// aggregate in release C (`big_param_by_ptr`). tcc 0.9.28 puts an
/// over-aligned argument on the stack 8-aligned, while the callee rounds
/// the parameter's offset up to the alignment, so the callee reads garbage
/// (fx-overalign). Every C signature and fn pointer type says `T *`
/// (`param_ctype`), every call passes the address of a fresh copy
/// (`FnGen::spill_by_ptr`), forwarding shims pass the pointer on, and
/// the body copies the value into its local on entry (`FnGen::function`).
fn param_by_ptr(p: &Program, t: &CTy) -> bool {
    let (size, align) = c_size_align(p, t);
    align > 16 || big_param_by_ptr(p, size)
}

/// `LUST_RELEASE_AGG_PARAM`: which by-value parameters of release C go by pointer besides the
/// over-aligned ones.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AggParam {
    /// `0`: none.
    Off,
    /// Unset or `1`: those over 16 bytes.
    Big,
    /// `all`: every one of 9 bytes or more (a stress switch for tests: every call site,
    /// shim and glue call must agree).
    All,
}

fn agg_param_mode() -> AggParam {
    static MODE: std::sync::OnceLock<AggParam> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("LUST_RELEASE_AGG_PARAM").as_deref() {
        Ok("0") => AggParam::Off,
        Ok("all") => AggParam::All,
        _ => AggParam::Big,
    })
}

/// Release C, outside the LLVM backend's C boundary (which keeps the C ABI): a parameter over
/// 16 bytes goes by pointer to a fresh copy. The C ABI passes it in memory ("byval"): the
/// caller builds the value in a temporary with field-sized stores, and the call copies it to
/// the argument area in the backend, with 16-byte loads that fail to forward from those
/// stores. A copy in C is one clang can merge with its source or split into field loads.
fn big_param_by_ptr(p: &Program, size: u64) -> bool {
    let mode = agg_param_mode();
    mode != AggParam::Off && (size > 16 || (mode == AggParam::All && size >= 9)) && names::release() && !ll::on(p)
}

/// The C type of a parameter of type `t` in a signature: `T *` when the
/// value goes by pointer (`param_by_ptr`).
fn param_ctype(p: &Program, t: &CTy) -> String {
    if param_by_ptr(p, t) { format!("{}*", ctype(t)) } else { ctype(t) }
}

/// Declares local `l{i}` of C type `ct` whose alignment is over 16, with
/// `decl` its declarator (`l{i}` or `l{i} = init`). tcc never realigns
/// the stack, so a frame slot is only 16-aligned: the value lives at the
/// first aligned address in a char buffer, and `l{i}` is a macro for it
/// up to the `#undef` after the function (fx-overalign). Dev C only: the
/// release C compilers (clang, gcc, zig cc) realign the frame, and a plain
/// local stays visible to their copy and scalar optimizations, which a
/// local behind integer pointer arithmetic is not (every copy of a
/// `#[repr(align(64))]` struct was a real copy).
fn overaligned_local(out: &mut String, i: usize, ct: &str, decl: &str) {
    let _ = writeln!(
        out,
        "  char l{i}_b[sizeof({ct}) + _Alignof({ct})]; {ct} *l{i}_p = ({ct} *)(((uintptr_t)l{i}_b + _Alignof({ct}) - 1) & ~(uintptr_t)(_Alignof({ct}) - 1));\n#define l{i} (*l{i}_p)"
    );
    if decl.contains('=') {
        let _ = writeln!(out, "  {decl};");
    }
}

/// True when `f` gets C of its own: a plain fn, an instance, or a
/// closure body fn, with a source body. A template or a trait
/// method stub is never generated, and an instance of a trait method
/// declaration has nothing to generate, so their slots stay empty.
fn has_generated_body(p: &Program, f: LocalDefId) -> bool {
    use crate::check::generics::FnClass;
    let concrete = matches!(p.gx.fn_class.get(f.0 as usize), None | Some(FnClass::Plain | FnClass::Instance | FnClass::Closure));
    concrete && p.fn_def(f).body.is_some()
}

/// The driver-facing message for `FnGen::bad_callee`: `f` (the body
/// being generated or its callee) has no generated body.
fn no_body_error(p: &Program, body: &Body, f: LocalDefId) -> String {
    let class = p.gx.fn_class.get(f.0 as usize).copied().unwrap_or_default();
    format!(
        "internal: code generation for `{}`: `{}` ({class:?}) has no generated body, so its fn slot would be empty",
        p.display_path(p.fn_info(body.fn_id).name),
        p.display_path(p.fn_info(f).name)
    )
}

/// `(RET (*)(PARAMS))`, the cast that calls function `f` through the table.
/// A large return becomes `(void (*)(RET*, PARAMS))` (see `ret_is_large`).
fn fn_ptr_cast(p: &Program, f: LocalDefId) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret}*"));
    }
    params.extend(info.params.iter().map(|&t| cty(&p.tys, t)).filter(|t| !param_dropped(p, t)).map(|t| param_ctype(p, &t)));
    // `#[track_caller]`: the caller's location (check/caller.rs, `names::hot_loc`).
    if crate::check::caller::is_track_caller(p, f) {
        params.push("const uint64_t *, uint64_t".to_string());
    }
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("(void (*)({params}))") } else { format!("({ret} (*)({params}))") }
}

/// The C signature of function `f`, defined under the C name of its body in `slot`
/// (`names::body`: `f<slot>`, or `f_<id>` in release C).
fn fn_sig(p: &Program, f: LocalDefId, slot: u32) -> String {
    fn_sig_named(p, f, &names::body(slot))
}

/// The C signature of function `f` under the C name `name`.
fn fn_sig_named(p: &Program, f: LocalDefId, name: &str) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret} *out"));
    }
    params.extend(
        info.params
            .iter()
            .enumerate()
            .map(|(i, &t)| (i, cty(&p.tys, t)))
            .filter(|(_, t)| !param_dropped(p, t))
            .map(|(i, t)| format!("{} p{}", param_ctype(p, &t), i + 1)),
    );
    // `#[track_caller]`: the caller's location, which `FnGen::loc`
    // reports for every panic in the body (check/caller.rs): the address
    // of its slot constant and its line and column bits (`names::hot_loc`).
    if crate::check::caller::is_track_caller(p, f) {
        params.push("const uint64_t *ltc_so, uint64_t ltc_low".to_string());
    }
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("void {name}({params})") } else { format!("{ret} {name}({params})") }
}

/// The slot trampoline for function `f` (ARCH 4.5): a tiny forwarder
/// with a stable address, stored in fn pointer values through
/// `lust_tramps`. It forwards through `lust_fns`, so an overlay swap
/// of the body keeps old fn pointer values calling the new body.
/// Emitted in the function's own unit today; the table-unit home in
/// 4.5 needs the driver to pass signatures to `table_unit`.
fn trampoline(p: &Program, f: LocalDefId, slot: u32) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let cast = fn_ptr_cast(p, f);
    // Release C: an extern trampoline that calls its body (defined just above it) by name.
    let (linkage, target, tr) = if names::release() {
        ("", names::body(slot), names::tramp(slot))
    } else {
        ("static ", format!("lust_fns[{slot}]"), format!("tramp{slot}"))
    };
    // The body fn of a closure that captures nothing (W-CHECK-G): a fn
    // pointer to it takes only the call args, so the trampoline supplies
    // the zero-sized env (by reference for `Fn` and `FnMut`).
    if p.gx.closure_fns.contains_key(&f)
        && let Some(&env_ty) = info.params.first()
    {
        let env_c = cty(&p.tys, env_ty);
        let by_ref = matches!(env_c, CTy::Ref(ref inner) if **inner == CTy::Unit);
        if by_ref || env_c == CTy::Unit {
            let kept: Vec<usize> =
                (1..info.params.len()).filter(|&i| !param_dropped(p, &cty(&p.tys, info.params[i]))).collect();
            let names: Vec<String> = kept.iter().map(|i| format!("p{}", i + 1)).collect();
            let decls: Vec<String> =
                kept.iter().map(|&i| format!("{} p{}", param_ctype(p, &cty(&p.tys, info.params[i])), i + 1)).collect();
            // A by-value Unit env is a dropped parameter; a by-ref env stays.
            let mut all: Vec<String> = if by_ref { vec!["&env".to_string()] } else { Vec::new() };
            all.extend(names);
            if ret_is_large(p, f) {
                let mut params = vec![format!("{ret} *out")];
                params.extend(decls);
                let rest = if all.is_empty() { String::new() } else { format!(", {}", all.join(", ")) };
                return format!(
                    "{linkage}void {tr}({}) {{ lust_Unit env; ({cast}{target})(out{rest}); }}\n",
                    params.join(", ")
                );
            }
            let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
            return format!(
                "{linkage}{ret} {tr}({params}) {{ lust_Unit env; return ({cast}{target})({}); }}\n",
                all.join(", ")
            );
        }
    }
    let kept: Vec<usize> = (0..info.params.len()).filter(|&i| !param_dropped(p, &cty(&p.tys, info.params[i]))).collect();
    let mut names: Vec<String> = kept.iter().map(|i| format!("p{}", i + 1)).collect();
    let decls: Vec<String> = kept.iter().map(|&i| format!("{} p{}", param_ctype(p, &cty(&p.tys, info.params[i])), i + 1)).collect();
    // Check never lets a `#[track_caller]` fn become a value; this keeps
    // the trampoline well formed all the same.
    if crate::check::caller::is_track_caller(p, f) {
        names.push("&lust_so_none, 0".to_string());
    }
    if ret_is_large(p, f) {
        let mut params = vec![format!("{ret} *out")];
        params.extend(decls);
        let mut all = vec!["out".to_string()];
        all.extend(names);
        format!("{linkage}void {tr}({}) {{ ({cast}{target})({}); }}\n", params.join(", "), all.join(", "))
    } else {
        let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
        format!("{linkage}{ret} {tr}({params}) {{ return ({cast}{target})({}); }}\n", names.join(", "))
    }
}

/// Generates C for one function body. `base_line` is the line of its `fn` keyword, in the
/// file that defines it; `slots` maps every LocalDefId to its slot in `lust_fns`.
pub fn gen_fn(p: &Program, body: &Body, map: &SourceMap, base_line: u32, slots: &[u32]) -> FnOut {
    if !has_generated_body(p, body.fn_id) {
        return FnOut { error: Some(no_body_error(p, body, body.fn_id)), ..Default::default() };
    }
    // `LocalKey` calls become plain IR first (lower/tls.rs); their
    // closures never hold iterator builtins the next step would miss.
    let tls_expanded;
    let body = match crate::lower::tls::expand(p, body) {
        Ok(Some(b)) => {
            tls_expanded = b;
            &tls_expanded
        }
        Ok(None) => body,
        Err(e) => return FnOut { error: Some(e), ..Default::default() },
    };
    // Iterator builtins become plain IR first (W-STD-A, lower/iter.rs).
    let expanded;
    let body = match crate::lower::iter::expand(p, body) {
        Ok(Some(b)) => {
            expanded = b;
            &expanded
        }
        Ok(None) => body,
        Err(e) => return FnOut { error: Some(e), ..Default::default() },
    };
    let slots = Slots::new(slots);
    let mut g = FnGen::new(p, body, map, base_line, &slots);
    g.collect_move_paths();
    if g.bad_move {
        return FnOut { error: Some(bad_move_error(p, body)), ..Default::default() };
    }
    // The LLVM backend writes the C side (prelude and trampoline included) itself.
    let mut llfn = None;
    if ll::on(p) {
        match g.function_ll() {
            Ok(f) => llfn = Some(f),
            Err(e) => return FnOut { error: Some(e), ..Default::default() },
        }
    } else {
        g.function();
    }
    if g.bad_move {
        return FnOut { error: Some(bad_move_error(p, body)), ..Default::default() };
    }
    if let Some(f) = g.bad_callee {
        return FnOut { error: Some(no_body_error(p, body, f)), ..Default::default() };
    }
    if let Some(t) = g.bad_callable.get() {
        return FnOut { error: Some(bad_callable_error(p, body, t)), ..Default::default() };
    }
    if llfn.is_none() {
        if !g.prelude.is_empty() {
            g.out = std::mem::take(&mut g.prelude) + &g.out;
        }
        g.out.push_str(&trampoline(p, body.fn_id, slots.of(body.fn_id)));
    }
    // A `main` returning `Result` gets a Termination entry in its
    // unit (see `fn_unit`): it needs the error type's Debug glue
    // and the Result's own drop glue.
    if Some(body.fn_id) == p.main
        && let Some((_, err_t)) = p.tys.result_args(p.fn_info(body.fn_id).ret)
    {
        let rc = cty(&p.tys, p.fn_info(body.fn_id).ret);
        g.want(Glue::Debug, &cty(&p.tys, err_t));
        if needs_drop_c(p, &rc) {
            g.want(Glue::Drop, &rc);
        }
    }
    let mut types = std::mem::take(&mut g.sig_types);
    let mut named = std::mem::take(&mut g.sig_named);
    let release = names::release();
    // An LLVM fn without a C side (no helpers, cgen/ll.rs) holds no local in C: only its
    // wrapper's signature (the return value, the parameters) needs definitions. The C
    // prototypes of its native callees still name its other locals' types.
    let c_side = llfn.as_ref().is_none_or(|f| f.c_side);
    for (i, t) in g.local_cty.iter().enumerate() {
        if release {
            // Release C: a local needs defined only what it holds by value; what it
            // points at (through `&`, `Box`, `Rc`, `Vec`, ...) it only names. A deref
            // records what it opens (`place`), and so does a builtin (`call_value`).
            if c_side || i <= body.arg_count {
                let mut held = Vec::new();
                by_value_deps(t, &mut held);
                types.extend(held);
            }
            collect_types(t, &mut named);
        } else {
            collect_types(t, &mut types);
        }
    }
    // Release C units call glue through prototypes, which only name their types.
    for (_, t) in &g.glue {
        collect_types(t, if release { &mut named } else { &mut types });
    }
    let (code, glue) = (g.out, g.glue);
    let (used, externs) = slots.into_used();
    named.retain(|t| !types.contains(t));
    let (ll, ll_decls, ll_c, ll_cost) = llfn.map(|f| (f.def, f.decls, f.helpers, f.cost)).unwrap_or_default();
    let inline = if release { inline_attr(p, body.fn_id) } else { InlineAttr::None };
    let mut ll_c_refs = ll::CRefs::default();
    if !ll.is_empty() {
        ll_c_refs.scan(&ll_c);
        if ll.contains("@f_") || ll.contains("@tramp_") {
            ll_c_refs.scan(&ll);
        }
    }
    // A session keeps every FnOut (the front image saves them whole):
    // no growth slack.
    let (mut code, mut glue, mut used, mut ll, mut ll_c) = (code, glue, used, ll, ll_c);
    code.shrink_to_fit();
    glue.shrink_to_fit();
    types.shrink_to_fit();
    named.shrink_to_fit();
    used.shrink_to_fit();
    ll.shrink_to_fit();
    ll_c.shrink_to_fit();
    let externs = externs.into_iter().map(shared_extern).collect();
    FnOut {
        text: CText::Plain(code),
        glue,
        types,
        error: None,
        used,
        externs,
        named,
        ll,
        ll_decls,
        ll_c,
        ll_cost,
        ll_c_refs,
        inline,
        text_digest: Default::default(),
        pick: Default::default(),
        layout: Default::default(),
    }
}

/// The extern declarations of the codegen phase running now, each kept once
/// (`shared_extern`): fns that call the same callee hold one copy of its
/// prototype.
static EXTERN_POOL: std::sync::LazyLock<Vec<std::sync::Mutex<std::collections::HashSet<std::sync::Arc<str>, std::hash::BuildHasherDefault<crate::intern::FxHasher>>>>> =
    std::sync::LazyLock::new(|| (0..64).map(|_| Default::default()).collect());

/// One extern declaration of a new FnOut, as the pool's copy.
fn shared_extern(e: String) -> std::sync::Arc<str> {
    use std::hash::{Hash, Hasher};
    let mut h = crate::intern::FxHasher::default();
    e.hash(&mut h);
    let shard = &EXTERN_POOL[(h.finish() >> 58) as usize];
    let mut set = shard.lock().unwrap_or_else(|p| p.into_inner());
    if let Some(a) = set.get(e.as_str()) {
        return a.clone();
    }
    let a: std::sync::Arc<str> = e.into();
    set.insert(a.clone());
    a
}

/// Empties the extern pool (the driver, before and after a codegen phase):
/// FnOuts keep their copies; the pool keeps nothing past the phase.
pub fn clear_extern_pool() {
    for shard in EXTERN_POOL.iter() {
        *shard.lock().unwrap_or_else(|p| p.into_inner()) = Default::default();
    }
}

/// `f`'s `#[inline]` attribute (an instance has its template's). A closure body counts as
/// `#[inline]`: it has one caller (the generic instance it is passed to), and rustc
/// inlines it there. A trait method stub has none.
fn inline_attr(p: &Program, f: LocalDefId) -> InlineAttr {
    use crate::ast::AttrInput;
    use crate::lexer::{Tok, TokenTree};
    if p.gx.closure_fns.contains_key(&f) {
        return InlineAttr::Hint;
    }
    if matches!(p.gx.fn_class.get(f.0 as usize), Some(crate::check::generics::FnClass::Stub)) {
        return InlineAttr::None;
    }
    let mut out = InlineAttr::None;
    for a in p.fn_info(f).def(&p.ast).attrs.iter().filter(|a| a.path.len() == 1 && p.name(a.path[0].name) == "inline") {
        out = match &a.input {
            AttrInput::List(_, t) => match t.as_slice() {
                [TokenTree::Token(x)] if matches!(x.tok, Tok::Ident(s) if p.name(s) == "always") => InlineAttr::Always,
                _ => InlineAttr::Never,
            },
            _ => InlineAttr::Hint,
        };
    }
    out
}

/// Static drop flags (`ir::dropflags`): on for the C backends, with their runtime flags' static
/// tests folded and their dead stores left out (`fine`); off for the LLVM backend, whose
/// optimizer folds constant flags itself (with the pass, tsgo's LLVM build ran about 1% slower:
/// small drop glue is called out of line more often). `LUST_DROPFLAGS=0` turns the pass off
/// (every drop flag a runtime flag, as before it), `=1` on for both backends, `=coarse` on with
/// per-local flags only (round 5's form), for A/B runs. Returns (on, fine).
fn static_drop_flags(p: &Program) -> (bool, bool) {
    static ENV: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let llvm = ll::on(p);
    match ENV.get_or_init(|| std::env::var("LUST_DROPFLAGS").ok()).as_deref() {
        Some("0") => (false, false),
        Some("1") => (true, !llvm),
        Some("coarse") => (true, false),
        _ => (!llvm, !llvm),
    }
}

impl<'b, 'p> FnGen<'b, 'p> {
    /// A generator for `body` with nothing emitted yet (`gen_fn`; an
    /// `ItemShim` builtin method's one-call body, `prim_shim`).
    fn new(p: &'p Program, body: &'b Body<'p>, map: &'b SourceMap, base_line: u32, slots: &'b Slots<'b>) -> Self {
        let local_cty: Vec<CTy> = body.locals.iter().map(|l| cty(&body.tys, l.ty)).collect();
        let byte_blobs = crate::ir::byte_blob_locals(body);
        let kstatic: crate::intern::FxMap<Local, crate::ty::consteval::ConstValue> = if names::release() {
            kconst::eval_promoted(p, body)
                .into_iter()
                .filter(|(l, v)| {
                    !byte_blobs.get(*l as usize).is_some_and(|b| b.is_some())
                        && kconst::entry_ok(v)
                        && !kconst::moves_drop_value(p, body, &local_cty, *l)
                })
                .collect()
        } else {
            Default::default()
        };
        let local_drop: Vec<bool> = local_cty.iter().map(|t| needs_drop_c(p, t)).collect();
        let n_locals = local_cty.len();
        let (on, fine) = static_drop_flags(p);
        let dflags = if on {
            crate::ir::dropflags::analyze(body, &local_drop, fine)
        } else {
            crate::ir::dropflags::DropFlags::all_runtime(n_locals)
        };
        FnGen {
            p,
            body,
            out: String::new(),
            glue: HashSet::new(),
            local_cty,
            local_drop,
            dflags,
            at: (u32::MAX, u32::MAX),
            move_paths: vec![Vec::new(); n_locals],
            bad_move: false,
            bad_callee: None,
            bad_callable: std::cell::Cell::new(None),
            const_index: crate::borrowck::const_index_locals(body),
            index_spans: index_spans(body),
            map,
            sig_types: HashSet::new(),
            sig_named: HashSet::new(),
            base_line,
            slots,
            tmp: 0,
            ret_large: ret_is_large(p, body.fn_id),
            r1: false,
            borrowed: Vec::new(),
            r3_value: false,
            vtables: HashMap::new(),
            prelude: String::new(),
            adapters: 0,
            shims: HashMap::new(),
            cleanup: if p.unwind { unwind::cleanup_blocks(body) } else { Vec::new() },
            byte_blobs,
            kstatic,
            kcx: kconst::StaticCx::default(),
            kentry: HashMap::new(),
            kdata: false,
            knames: HashMap::new(),
            stmt_unw: body.stmt_unwind.iter().map(|&(b, i, u)| ((b.0, i), u.0)).collect(),
            unw: None,
            unw_call: false,
            zc_frame: false,
            zc_st: None,
            zc_in_cleanup: false,
            flags_at_term: Vec::new(),
            cur_bb: 0,
            call_out: None,
            kdecl_at: None,
            kstrs: HashMap::new(),
            addr_only: false,
        }
    }
}

/// The line of `ty`'s `int_impl!` or `uint_impl!` invocation in
/// core/src/num/mod.rs (rustc 1.99, 64-bit targets): where a panic in
/// one of its methods called through a fn pointer is reported.
fn int_impl_line(ty: IntTy) -> u32 {
    match ty {
        IntTy::I8 => 379,
        IntTy::I16 => 404,
        IntTy::I32 => 429,
        IntTy::I64 => 454,
        IntTy::I128 => 479,
        IntTy::Isize => 559,
        IntTy::U8 => 586,
        IntTy::U16 => 1234,
        IntTy::U32 => 1290,
        IntTy::U64 => 1322,
        IntTy::U128 => 1354,
        IntTy::Usize => 1452,
    }
}

/// The driver-facing message for `FnGen::bad_callable`.
fn bad_callable_error(p: &Program, body: &Body, t: Ty) -> String {
    format!(
        "code generation for `{}`: a builtin call (`catch_unwind`, a thread start, `OnceLock::get_or_init`, `sort_by`, `retain`, ...) whose callable has type `{}` is not supported yet; wrap the call in a closure",
        p.display_path(p.fn_info(body.fn_id).name),
        crate::check::collect::ty_name(p, &body.tys, t)
    )
}

/// The driver-facing message for `FnGen::bad_move`.
fn bad_move_error(p: &Program, body: &Body) -> String {
    format!(
        "internal: code generation for `{}`: a move out of part of a value reached code generation in a form drop elaboration cannot track (through a reference or a non-constant index)",
        p.name(p.fn_info(body.fn_id).name)
    )
}

/// The span of each local's last plain assignment, where a self-copy
/// `l = copy l` wins: the panic location of an index local
/// (`Proj::Index`, lowering's `mark_index_loc`).
fn index_spans(body: &Body) -> Vec<Option<Span>> {
    let mut out: Vec<Option<Span>> = vec![None; body.locals.len()];
    let mut fixed = vec![false; body.locals.len()];
    for b in &body.blocks {
        for st in &b.stmts {
            if let StmtKind::Assign(p, rv) = &st.kind
                && p.proj.is_empty()
                && let Some(slot) = out.get_mut(p.local as usize)
            {
                let l = p.local as usize;
                let self_copy = matches!(rv, Rvalue::Use(Operand::Copy(q)) if q.local == p.local && q.proj.is_empty());
                if self_copy || !fixed[l] {
                    *slot = Some(st.span);
                }
                fixed[l] |= self_copy;
            }
        }
    }
    out
}

impl FnGen<'_, '_> {
    /// The packed panic location of index local `l`, else `loc`.
    fn index_loc(&self, l: Local, loc: &str) -> String {
        match self.index_spans.get(l as usize).copied().flatten() {
            Some(sp) => self.loc(sp),
            None => loc.to_string(),
        }
    }
    /// A packed source location, relative to the function's first line. See `lust_loc`.
    /// The runtime prints one file path for the whole program (`lust_file`), so the packed
    /// value carries line and column only; an expanded span reports at its call site.
    fn loc(&self, span: Span) -> String {
        // A panic rustc reports inside std keeps std's line, also in a
        // `#[track_caller]` fn.
        if span.file == crate::diag::FileId::STD_SITE {
            return std_loc(span.lo as u64, (span.hi >> 12) as u64, (span.hi & 0xFFF) as u64);
        }
        // In a `#[track_caller]` fn every panic reports the caller's
        // location, as rustc does (check/caller.rs).
        if crate::check::caller::is_track_caller(self.p, self.body.fn_id) {
            return names::LTC_WORD.to_string();
        }
        let span = self.map.call_site(span);
        // A panic site in shipped std source reports std's own file and
        // line (its `//@` marker, src/stdloc.rs), as rustc does.
        if let Some((f, l, c)) = crate::stdloc::site(self.p, self.map, span) {
            return std_loc(f as u64, l as u64, c as u64);
        }
        let (l, c) = self.map.line_display_col(span);
        let rel = l.saturating_sub(self.base_line).min(0xFFFFF) as u64;
        self.slots.loc(self.body.fn_id, rel, c.min(0xFFFFF) as u64)
    }
    fn tmp(&mut self) -> String {
        self.tmp += 1;
        format!("t{}", self.tmp)
    }
    fn want(&mut self, g: Glue, t: &CTy) {
        self.glue.insert((g, t.clone()));
    }

    fn function(&mut self) {
        let p = self.p;
        let fid = self.body.fn_id;
        let slot = self.slots.of(fid);
        let n = self.body.blocks.len();
        let mut reachable = vec![false; n];
        let mut stack = vec![0usize];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut reachable[b], true) {
                continue;
            }
            stack.extend(succ(&self.body.blocks[b].term).into_iter().map(|s| s.0 as usize));
            stack.extend(self.body.stmt_unwind.iter().filter(|e| e.0.0 as usize == b).map(|e| e.2.0 as usize));
        }
        let order: Vec<usize> = (0..n).filter(|&b| reachable[b]).collect();
        // Unwind tables: the cleanup blocks go to their own fn (`cleanup_fn`), and the frame
        // struct its cleanup variable points at holds the flags of the locals they read and
        // a pointer to each.
        let zc = p.unwind && p.unwind_tables;
        let cl_order: Vec<usize> = if zc { order.iter().copied().filter(|&b| self.cleanup[b]).collect() } else { Vec::new() };
        let order: Vec<usize> = if zc { order.into_iter().filter(|&b| !self.cleanup[b]).collect() } else { order };
        let mut cl_text = String::new();
        let mut members: Vec<Vec<String>> = Vec::new();
        if !cl_order.is_empty() {
            let saved = std::mem::take(&mut self.out);
            self.zc_in_cleanup = true;
            self.blocks(&cl_order);
            self.zc_in_cleanup = false;
            cl_text = std::mem::replace(&mut self.out, saved);
        }
        // A ladder with no call (only jumps and returns) drops nothing: no frame.
        let mut cl_inline = false;
        if cl_text.contains('(') {
            let kept: Vec<bool> = (0..self.local_cty.len()).map(|l| self.local_drop[l] && self.dflags.keeps(l as Local)).collect();
            members = unwind::frame_members(&cl_text, self.local_cty.len(), &self.move_paths, &kept, &self.body.promoted);
            self.zc_frame = true;
            let flags = members.iter().flatten().filter(|nm| !nm.starts_with('l')).count();
            let calls = self.body.blocks.iter().filter(|b| matches!(b.term, Terminator::Call { unwind: Some(_), .. })).count();
            cl_inline = unwind::frame_inline(flags, self.stmt_unw.len() + calls);
            let decls = self.frame_struct(&names::fn_tag(slot), &members, cl_inline);
            self.out.push_str(&decls);
        }
        // Release C bodies are extern: other units call them directly (`names`).
        let linkage = if names::release() { "" } else { "static " };
        // The fn's own text starts here: the in-place rename below stays inside it (not the
        // frame struct before it, nor the cleanup fn after it).
        let body_start = self.out.len();
        let _ = writeln!(self.out, "/* {} */\n{linkage}{} {{", p.display_path(p.fn_info(fid).name), fn_sig(p, fid, slot));
        // Release C: a by-pointer parameter whose local the unwind frame holds lives in memory
        // anyway (the cleanup's drop takes its address, so the C compiler keeps it there), and
        // its copy-in was a real copy. The body uses the caller's fresh copy (`spill_by_ptr`)
        // in place, `(*p{i})` (the rename below): the callee owns it until it returns.
        let in_place: Vec<usize> = (1..=self.body.arg_count)
            .filter(|&i| {
                let t = &self.local_cty[i];
                members.get(i).is_some_and(|m| !m.is_empty()) && param_by_ptr(p, t) && !param_dropped(p, t) && names::release() && !ll::on(p)
            })
            .collect();
        // R1: the return value is built in the caller's storage, `(*out)` (the rename below),
        // and the return copies nothing. Lowering never drops local 0 on unwind, so no
        // cleanup reads it; a frame that did would keep `l0`.
        self.r1 = inplace(p).r1 && self.ret_large && members.first().is_none_or(|m| m.is_empty());
        self.borrowed = vec![false; self.local_cty.len()];
        for s in self.body.blocks.iter().flat_map(|b| &b.stmts) {
            if let StmtKind::Assign(_, Rvalue::Ref(_, pl) | Rvalue::SliceOf(pl) | Rvalue::Subslice { base: pl, .. }) = &s.kind {
                self.borrowed[pl.local as usize] = true;
            }
        }
        // Locals grouped by C type. No initializers: the borrow checker proves every read is
        // after a write. Drop flags start at 0, except for parameters, which own their values.
        let mut by_type: Vec<(String, Vec<String>)> = Vec::new();
        let mut flags = Vec::new();
        // Dev C's locals with alignment over 16 (see `overaligned_local`).
        let mut high: Vec<(usize, String, String)> = Vec::new();
        let mut frame_init: Vec<String> = Vec::new();
        // A `kdata` fn's constants are named data with no local (`kdata_local`); else the
        // compile-time promoted values' decls (`kstatic_decl`; both need `self` mutably,
        // so ahead of the loop).
        self.kdata = self.kdata_ok();
        if self.kdata {
            let ks: Vec<usize> = (0..self.local_cty.len()).filter(|&i| self.kconst_local(i)).collect();
            for i in ks {
                let name = self.kdata_local(i);
                self.knames.insert(i as Local, name);
            }
        }
        let kdecls: Vec<Option<String>> = (0..self.local_cty.len())
            .map(|i| if self.body.promoted.contains(&(i as Local)) && !self.knames.contains_key(&(i as Local)) { self.kstatic_decl(i) } else { None })
            .collect();
        for (i, t) in self.local_cty.iter().enumerate() {
            // A byte string temp gets static storage below, not a frame local.
            if self.byte_blobs.get(i).is_some_and(|b| b.is_some()) {
                continue;
            }
            let is_param = i >= 1 && i <= self.body.arg_count;
            // A local the cleanup ladder reads stays a local; the frame struct holds a pointer
            // to it and its flags, set right after `L` is declared.
            let member = members.get(i).is_some_and(|m| !m.is_empty());
            if member {
                frame_init.push(format!("L.pl{i} = &l{i};"));
                if self.local_drop[i] && self.dflags.entry(i as Local) {
                    frame_init.push(format!("L.d{i} = {};", is_param as u8));
                }
                for k in 0..self.move_paths[i].len() {
                    frame_init.push(format!("L.m{i}_{k} = 1;"));
                }
            }
            if in_place.contains(&i) || (i == 0 && self.r1) {
                // No local: it is the pointee, `(*p{i})` (or `(*out)`).
                continue;
            }
            // A dropped parameter (see `param_dropped`) has no `p{i}`; its
            // local is the one possible value of a zero-sized type.
            let decl = if is_param && param_dropped(p, t) {
                format!("l{i} = {}", zero_lit(p, t))
            } else if is_param && param_by_ptr(p, t) {
                format!("l{i} = *p{i}")
            } else if is_param {
                format!("l{i} = p{i}")
            } else {
                format!("l{i}")
            };
            let ct = ctype(t);
            if self.knames.contains_key(&(i as Local)) {
                // A `kdata` constant: named data, no local (`kdata_local`).
            } else if self.body.promoted.contains(&(i as Local)) {
                // A promoted constant (`&5` borrowed for `'static`): static
                // storage, written with the same value each time it runs.
                // In release builds a value codegen computed at compile time
                // is static data instead (its assignment is skipped in `stmt`).
                match &kdecls[i] {
                    Some(d) => self.out.push_str(d),
                    None => {
                        let _ = writeln!(self.out, "  static {ct} {decl};");
                    }
                }
                if self.kconst_local(i) {
                    let d = self.kconst_decls(i);
                    self.out.push_str(&d);
                }
            } else if c_size_align(p, t).1 > 16 && !names::release() {
                high.push((i, ct, decl));
            } else {
                match by_type.iter_mut().find(|(c, _)| *c == ct) {
                    Some((_, v)) => v.push(decl),
                    None => by_type.push((ct, vec![decl])),
                }
            }
            if member {
                continue;
            }
            if self.local_drop[i] && self.dflags.entry(i as Local) {
                flags.push(format!("d{i} = {}", is_param as u8));
            } else if self.local_drop[i] && self.dflags.keeps(i as Local) {
                // No test reads the entry value (`ir::dropflags` liveness).
                flags.push(format!("d{i}"));
            }
            for k in 0..self.move_paths[i].len() {
                flags.push(format!("m{i}_{k} = 1"));
            }
        }
        for (ct, names) in &by_type {
            // In C, `T* a, b` makes only `a` a pointer, so every declarator gets its own stars.
            let base = ct.trim_end_matches('*');
            let stars = &ct[base.len()..];
            let decls: Vec<String> = names.iter().map(|n| format!("{stars}{n}")).collect();
            let _ = writeln!(self.out, "  {base} {};", decls.join(", "));
        }
        for (i, ct, decl) in &high {
            overaligned_local(&mut self.out, *i, ct, decl);
        }
        // Byte string temps: static storage, initialized once, never
        // assigned (the matching assignments are skipped in `stmt`).
        for (i, b) in self.byte_blobs.iter().enumerate() {
            if let Some(b) = b
                && !self.knames.contains_key(&(i as Local))
            {
                let ct = ctype(&self.local_cty[i]);
                let init = if b.is_empty() { "{0}".to_string() } else { format!("{{ .v = {} }}", c_bytes_lit(b.as_slice())) };
                let _ = writeln!(self.out, "  static {ct} l{i} = {init};");
                if self.kconst_local(i) {
                    let d = self.kconst_decls(i);
                    self.out.push_str(&d);
                }
            }
        }
        if !flags.is_empty() {
            let _ = writeln!(self.out, "  uint8_t {};", flags.join(", "));
        }
        if self.zc_frame {
            let tag = names::fn_tag(slot);
            let _ = writeln!(self.out, "  struct fr{tag} L __attribute__((cleanup(clw{tag})));\n  L.st = 0;");
            for s in &frame_init {
                let _ = writeln!(self.out, "  {s}");
            }
            // The body reads its member locals directly; only their flags are in the frame.
            for nm in members.iter().flatten().filter(|nm| !nm.starts_with('l')) {
                let _ = writeln!(self.out, "#define {nm} (L.{nm})");
            }
        }
        if zc {
            // A panic never returns with unwind tables: no entry check.
            self.out.push_str("  lust_exc ex;\n");
        } else if p.unwind {
            // A call made while its thread has a pending exception comes
            // from code that runs on after a panic (glue, a runtime
            // callback): it returns at once, as if never called.
            let _ = writeln!(self.out, "  lust_exc ex;
  if (lust_unw_pending && lust_unw_mine()) {}", self.unwind_return());
        }
        self.kdecl_at = Some(self.out.len());
        if zc {
            self.flags_at_term = self.flags_maybe_set();
        }
        self.blocks(&order);
        self.kstr_finish();
        self.out.push_str("}\n");
        if !in_place.is_empty() || self.r1 {
            let mut map: Vec<(String, String)> = in_place.iter().map(|i| (format!("l{i}"), format!("(*p{i})"))).collect();
            if self.r1 {
                map.push(("l0".into(), "(*out)".into()));
            }
            let text = rename_idents(&self.out[body_start..], &map);
            self.out.truncate(body_start);
            self.out.push_str(&text);
        }
        for (i, ..) in &high {
            let _ = writeln!(self.out, "#undef l{i}");
        }
        if self.zc_frame {
            unwind::cleanup_fn(&mut self.out, &names::fn_tag(slot), &members, &cl_order, &cl_text, cl_inline);
            self.zc_frame = false;
        }
        self.out.push('\n');
    }

    /// Emits the blocks `order` (reachable, in this order): their labels, statements with
    /// their unwind actions, and terminators.
    fn blocks(&mut self, order: &[usize]) {
        let zc = self.p.unwind && self.p.unwind_tables;
        let entry = if zc && self.zc_frame && !self.zc_in_cleanup { self.zc_entry_states(order) } else { Vec::new() };
        for (k, &bi) in order.iter().enumerate() {
            self.zc_st = entry.get(bi).copied().flatten();
            self.cur_bb = bi;
            let _ = writeln!(self.out, "bb{bi}:;");
            let block = self.body.block(Bb(bi as u32));
            for (si, s) in block.stmts.iter().enumerate() {
                self.at = (bi as u32, si as u32);
                self.unw = self.stmt_action(bi, si).filter(|_| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)));
                // Unwind tables: the statement's ladder entry is in `L.st` before it runs;
                // a panic inside never returns, so nothing follows it.
                if zc && let Some(Unw::Goto(b)) = self.unw {
                    self.zc_store(b);
                }
                let mark = self.out.len();
                self.stmt(&s.kind, s.span);
                if let Some(u) = self.unw.take()
                    && !zc
                {
                    let check = u.check();
                    let text = unwind::wrap_calls(&self.out[mark..], &check);
                    self.out.truncate(mark);
                    self.out.push_str(&text);
                    let _ = writeln!(self.out, "  {check}");
                }
            }
            self.at = (bi as u32, block.stmts.len() as u32);
            self.unw = self.stmt_action(bi, block.stmts.len());
            if zc && let Some(Unw::Goto(b)) = self.unw {
                self.zc_store(b);
            }
            let next = order.get(k + 1).copied();
            if let Terminator::Goto(t) = &block.term
                && Some(t.0 as usize) == next
            {
                continue;
            }
            self.term(&block.term, block.term_span, next);
        }
    }

    /// Unwind tables: the ladder entry `L.st` holds when each of `order`'s blocks starts,
    /// where every path to the block agrees (`function` stores 0 at entry, and `blocks`
    /// stores each statement's and call's entry before it runs), so a block stores only
    /// where the entry changes. None where the paths disagree.
    fn zc_entry_states(&self, order: &[usize]) -> Vec<Option<u32>> {
        let n = self.body.blocks.len();
        let mut normal = vec![false; n];
        order.iter().for_each(|&b| normal[b] = true);
        // None: no path seen yet; Some(None): the paths disagree.
        let mut entry: Vec<Option<Option<u32>>> = vec![None; n];
        let Some(&first) = order.first() else { return Vec::new() };
        entry[first] = Some(Some(0));
        let mut work = vec![first];
        while let Some(b) = work.pop() {
            let block = self.body.block(Bb(b as u32));
            let mut st = entry[b].flatten();
            for si in 0..=block.stmts.len() {
                let skip = block.stmts.get(si).is_some_and(|s| matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)));
                if !skip && let Some(Unw::Goto(e)) = self.stmt_action(b, si) {
                    st = Some(e);
                }
            }
            if let Terminator::Call { unwind: Some(u), .. } = &block.term {
                st = Some(u.0);
            }
            for s in succ(&block.term).into_iter().map(|s| s.0 as usize).filter(|&s| normal[s]) {
                let new = match entry[s] {
                    None => Some(st),
                    Some(old) if old == st => Some(old),
                    Some(_) => Some(None),
                };
                if entry[s] != new {
                    entry[s] = new;
                    work.push(s);
                }
            }
        }
        entry.into_iter().map(Option::flatten).collect()
    }

    /// Unwind tables: stores ladder entry `b` in the frame's `L.st` (once per run of
    /// statements with the same entry). No frame (no cleanup to run) or a cleanup
    /// block's own code stores nothing.
    fn zc_store(&mut self, b: u32) {
        if self.zc_frame && !self.zc_in_cleanup && self.zc_st != Some(b) {
            let _ = writeln!(self.out, "  L.st = {b};");
            self.zc_st = Some(b);
        }
    }

    /// The unwind action of statement `si` of block `bi` (`si` equal to
    /// the statement count is the terminator): abort in a cleanup
    /// block, else its cleanup entry, if lowering gave it one.
    fn stmt_action(&self, bi: usize, si: usize) -> Option<Unw> {
        if !self.p.unwind {
            return None;
        }
        if self.cleanup[bi] {
            return Some(Unw::Abort);
        }
        self.stmt_unw.get(&(bi as u32, si as u32)).map(|&u| Unw::Goto(u))
    }

    /// R1's caller rule, for a call whose result goes straight into whole local `l` of type
    /// `t` (the `direct` path). Under R1 a callee that returns through the out pointer writes
    /// its result there as it runs, not only at its return, so no reference may reach the
    /// storage during the call. A local with no value on any path here has no live reference
    /// into it (borrowck): a type with drop glue shows that by its clear flag (`direct` asks
    /// for it), a type with none by `flags_maybe_set`, which tracks every local. Else a local
    /// the body never borrows will do. Promoted locals are static storage: never.
    fn r1_out_ok(&self, l: Local, t: &CTy) -> bool {
        if !inplace(self.p).r1 || !ret_by_out(self.p, t) {
            return true;
        }
        let clear = self.flags_at_term.get(self.cur_bb).is_some_and(|f| !f[l as usize]);
        !self.body.promoted.contains(&l) && (needs_drop_c(self.p, t) || clear || !self.borrowed[l as usize])
    }

    /// `return <placeholder>;` for a frame that leaves by unwinding: the
    /// caller never reads the value.
    fn unwind_return(&self) -> String {
        if self.ret_large {
            return "return;".into();
        }
        let rt = cty(&self.p.tys, self.p.fn_info(self.body.fn_id).ret);
        format!("return {};", zero_lit(self.p, &rt))
    }

    /// For an assignment to `dest` of a type that needs drop: the C
    /// statements that drop the old value first, and the ones that
    /// mark the place owned again after the write. Each starts with
    /// a space. A whole local drops through its flag and elaboration;
    /// a part drops through elaboration when moves went through it
    /// (Rust lets a moved field be assigned again), else always.
    fn drop_old_value(&mut self, dest: &Place, d: &str, dt: &CTy) -> (String, String) {
        let l = dest.local;
        if dest.proj.is_empty() {
            // A flag store no test reads is left out (`ir::dropflags` liveness).
            let set = if self.dflags.store(self.at, l, Store::Set) { format!(" d{l} = 1;") } else { String::new() };
            let old = self.elab_drop(l, &[]);
            return match self.dflags.test(self.at, l) {
                // The old value drops here on every path, or on none. The drop is made either
                // way, so the glue it names stays wanted (other C names it too).
                Some(true) => {
                    let clear = if self.dflags.store(self.at, l, Store::DropClear) { format!(" d{l} = 0;") } else { String::new() };
                    (format!("{clear}{old}"), format!("{set}{}", self.reset_move_flags(l, &[])))
                }
                Some(false) => (String::new(), format!("{set}{}", self.reset_move_flags(l, &[]))),
                None => (format!(" if (d{l}) {{{old} }}"), format!("{set}{}", self.reset_move_flags(l, &[]))),
            };
        }
        if let Some(path) = self.steps_of(dest)
            && self.move_paths[l as usize].iter().any(|p| p.starts_with(&path))
        {
            return (self.elab_drop(l, &path), self.reset_move_flags(l, &path));
        }
        self.want(Glue::Drop, dt);
        (format!(" drop_{}(&{d});", mangle(dt)), String::new())
    }

    /// Unwind tables: a cleanup variable that drops `v` (of type `t`, which a builtin owns)
    /// when a panic unwinds before the disarm statement runs: the declaration, to emit before
    /// the call or check that can panic, and the disarm, to emit after it. Empty when `t`
    /// needs no drop.
    pub(super) fn zc_guard(&mut self, v: &str, t: &CTy) -> (String, String) {
        if !needs_drop_c(self.p, t) {
            return (String::new(), String::new());
        }
        self.want(Glue::Drop, t);
        let g = self.tmp();
        (
            format!(" struct lust_dguard {g} __attribute__((cleanup(lust_dguard_end))) = {{ (void (*)(void *))drop_{}, (void *)&{v}, 1 }};", mangle(t)),
            format!(" {g}.armed = 0;"),
        )
    }

    /// panic=unwind: C text that drops `v` (of type `t`), which a
    /// builtin owns, when this thread has a pending exception: the
    /// exception is held while the drop runs as cleanup, a second panic
    /// aborts (`lust_unw_dstep`), then it is pending again. The drop
    /// call is in expression form, so `wrap_calls` leaves it alone.
    pub(super) fn unw_cleanup_drop(&mut self, v: &str, t: &CTy) -> String {
        if !needs_drop_c(self.p, t) {
            return String::new();
        }
        self.want(Glue::Drop, t);
        format!(
            " if (lust_unw_pending && lust_unw_mine()) {{ lust_exc e_; int32_t u_ = 0; lust_unw_dstep(&e_, &u_); (void)(drop_{}(&{v}), 0); lust_unw_dstep(&e_, &u_); lust_unw_resume(&e_); }}",
            mangle(t)
        )
    }

    // ---------- Drop elaboration ----------

    /// The move path of a place: its projections as `Step`s, or None
    /// when it goes through a reference or a non-constant index.
    /// A deref through a `Box` is a step (moving out of a box is
    /// legal); a deref through a reference is not.
    fn steps_of(&self, pl: &Place) -> Option<Vec<Step>> {
        let mut steps: Vec<Step> = Vec::new();
        for pr in &pl.proj {
            let step = match pr {
                Proj::Field(i) => Step::Field(*i),
                Proj::Downcast(v) => Step::Downcast(*v),
                Proj::Index(l) => Step::Elem(*self.const_index.get(l)?),
                Proj::Deref => {
                    let (_, t) = self.path_place(pl.local, &steps)?;
                    if !matches!(t, CTy::Boxed(_)) {
                        return None;
                    }
                    Step::Deref
                }
            };
            steps.push(step);
        }
        Some(steps)
    }

    /// Fills `move_paths` from every `Move` of a part of a local.
    /// The statement and terminator matches are exhaustive, like
    /// the rvalue scan, so a new IR variant cannot hide a move from
    /// drop elaboration. A part move with no trackable path sets
    /// `bad_move` instead of being skipped.
    fn collect_move_paths(&mut self) {
        let body = self.body;
        let mut moved: Vec<&Place> = Vec::new();
        for b in &body.blocks {
            for s in &b.stmts {
                match &s.kind {
                    StmtKind::Assign(_, rv) => rvalue_moves(rv, &mut moved),
                    StmtKind::Print { parts, .. } => parts_moves(parts, &mut moved),
                    StmtKind::Drop(_) | StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {}
                }
            }
            match &b.term {
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => operand_moves(o, &mut moved),
                // `dest` is a write and an `Indirect` target reads a
                // Copy fn pointer local: neither moves a place.
                Terminator::Call { args, .. } => args.iter().for_each(|o| operand_moves(o, &mut moved)),
                Terminator::Panic(parts) => parts_moves(parts, &mut moved),
                Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable | Terminator::MatchExhausted => {}
            }
        }
        for pl in moved {
            if pl.proj.is_empty() {
                continue;
            }
            let l = pl.local as usize;
            if !self.local_drop[l] {
                continue;
            }
            let Some(path) = self.steps_of(pl) else {
                self.bad_move = true;
                continue;
            };
            match self.path_place(pl.local, &path) {
                Some((_, t)) if needs_drop_c(self.p, &t) => {
                    // Drop elaboration reads the fields of each container on the path
                    // (`elab_parts`): they need their definitions (`nested_block`).
                    for k in 1..path.len() {
                        if let Some((_, ct)) = self.path_place(pl.local, &path[..k]) {
                            self.note_held(&ct);
                        }
                    }
                    if !self.move_paths[l].contains(&path) {
                        self.move_paths[l].push(path);
                    }
                }
                Some(_) => {}
                None => self.bad_move = true,
            }
        }
    }

    /// The C expression and type of one move path of local `l`
    /// (`place` for the projections a path can hold), or None when
    /// a step does not fit the type it steps into. Callers turn
    /// None into `bad_move`: a move path that does not fit its
    /// local's type must not reach drop elaboration.
    fn path_place(&self, l: Local, path: &[Step]) -> Option<(String, CTy)> {
        let mut e = format!("l{l}");
        let mut t = self.local_cty[l as usize].clone();
        let mut variant: Option<u32> = None;
        for step in path {
            match (*step, t.clone()) {
                (Step::Downcast(v), _) => variant = Some(v),
                (Step::Field(i), CTy::Adt(a)) => {
                    let v = variant.take();
                    e = match v {
                        Some(v) => format!("{e}.u.v{v}.f{i}"),
                        None => format!("{e}.f{i}"),
                    };
                    let f = self.p.adt(a).variants.get(v.unwrap_or(0) as usize)?.fields.get(i as usize)?;
                    t = cty(&self.p.tys, f.ty);
                }
                (Step::Field(i), CTy::Tuple(es)) => {
                    e = format!("{e}.f{i}");
                    t = es.get(i as usize)?.clone();
                }
                (Step::Field(0), CTy::OptIter(_, el)) => {
                    e = format!("{e}.f0");
                    t = CTy::Option(el);
                }
                (Step::Field(i), CTy::ArrayIter(el, n)) => {
                    e = format!("{e}.f{i}");
                    t = match i {
                        0 => CTy::Array(el, n),
                        1 | 2 => CTy::Int(IntTy::Usize),
                        _ => return None,
                    };
                }
                (Step::Field(_), CTy::Option(inner)) => {
                    variant = None;
                    e = variant_field(self.p, &t, &e, 1, 0);
                    t = *inner;
                }
                (Step::Field(_), CTy::Result(a, b)) => {
                    let v = variant.take().unwrap_or(0);
                    e = variant_field(self.p, &t, &e, v as usize, 0);
                    t = if v == 0 { *a } else { *b };
                }
                (Step::Elem(c), CTy::Array(el, n)) => {
                    if c >= n {
                        return None;
                    }
                    e = format!("{e}.v[{c}]");
                    t = *el;
                }
                (Step::Deref, CTy::Boxed(inner)) => {
                    e = format!("(*{e})");
                    t = *inner;
                }
                _ => return None,
            }
        }
        Some((e, t))
    }

    /// The flag index of one moved path of local `l`.
    fn move_flag(&self, l: Local, path: &[Step]) -> Option<usize> {
        self.move_paths[l as usize].iter().position(|p| p == path)
    }

    /// C statements that set every move flag of `l` at or below
    /// `prefix` (the part an assignment just filled again).
    fn reset_move_flags(&self, l: Local, prefix: &[Step]) -> String {
        let mut s = String::new();
        for (k, path) in self.move_paths[l as usize].iter().enumerate() {
            if path.starts_with(prefix) {
                let _ = write!(s, " m{l}_{k} = 1;");
            }
        }
        s
    }

    /// C statements that drop the part of local `l` at `prefix` that
    /// the function still owns: a moved path drops only while its
    /// flag is set, a place above moved paths drops part by part in
    /// Rust's order (an enum only in the variant the paths go
    /// through), and any other place drops whole. Rust forbids moving
    /// out of a type with a `Drop` impl (E0509, borrowck), so no place
    /// split here has one.
    fn elab_drop(&mut self, l: Local, prefix: &[Step]) -> String {
        let paths = &self.move_paths[l as usize];
        let own = paths.iter().position(|p| p == prefix);
        let deeper = paths.iter().any(|p| p.len() > prefix.len() && p.starts_with(prefix));
        // Every prefix here is a prefix of a path `collect_move_paths`
        // verified, or one step below such a prefix taken from the
        // type at that prefix (`elab_parts`), so None cannot happen
        // for a body the scan accepted. Flag it anyway: the driver
        // reports `bad_move` and discards this function's code.
        let Some((e, t)) = self.path_place(l, prefix) else {
            self.bad_move = true;
            return String::new();
        };
        let inner = if deeper {
            self.elab_parts(l, prefix, &e, &t)
        } else if needs_drop_c(self.p, &t) {
            self.want(Glue::Drop, &t);
            format!(" drop_{}(&{e});", mangle(&t))
        } else {
            String::new()
        };
        match own {
            Some(k) => format!(" if (m{l}_{k}) {{{inner} }}"),
            None => inner,
        }
    }

    /// `elab_drop` one level down: the fields of a struct, tuple, or
    /// (after a `Downcast`) enum variant in order, the elements of an
    /// array in order, or a switch over the enum variants the moved
    /// paths go through.
    fn elab_parts(&mut self, l: Local, prefix: &[Step], e: &str, t: &CTy) -> String {
        let next_steps: Vec<Step> = {
            let mut v: Vec<Step> = Vec::new();
            for p in &self.move_paths[l as usize] {
                if p.len() > prefix.len() && p.starts_with(prefix) && !v.contains(&p[prefix.len()]) {
                    v.push(p[prefix.len()]);
                }
            }
            v
        };
        let sub = |s: Step| {
            let mut p = prefix.to_vec();
            p.push(s);
            p
        };
        let mut out = String::new();
        let variant = match prefix.last() {
            Some(Step::Downcast(v)) => Some(*v as usize),
            _ => None,
        };
        let is_enum = match t {
            CTy::Adt(a) => self.p.adt(*a).is_enum,
            CTy::Option(_) | CTy::Result(..) => true,
            _ => false,
        };
        match t {
            CTy::Array(el, n) if variant.is_none() => {
                // rustc's open drop of an array (`open_drop_for_array`):
                // a run of elements with no move path drops as one
                // subslice (in index order), an element with one drops
                // on its own, and the runs and elements go in reverse.
                let kept: Vec<u64> = next_steps.iter().filter_map(|s| if let Step::Elem(c) = s { Some(*c) } else { None }).collect();
                let mut parts: Vec<Result<(u64, u64), u64>> = Vec::new();
                let (mut dropping, mut start) = (true, 0);
                for i in 0..*n {
                    let keep = kept.contains(&i);
                    if dropping && keep {
                        parts.push(Ok((start, i)));
                        dropping = false;
                    } else if !dropping && !keep {
                        dropping = true;
                        start = i;
                    }
                    if keep {
                        parts.push(Err(i));
                    }
                }
                if dropping {
                    parts.push(Ok((start, *n)));
                }
                for part in parts.into_iter().rev() {
                    match part {
                        Ok((a, b)) if b > a => {
                            let i = self.tmp();
                            self.want(Glue::Drop, el);
                            let _ = write!(out, " for (uint64_t {i} = {a}; {i} < {b}; {i}++) drop_{}(&{e}.v[{i}]);", mangle(el));
                        }
                        Ok(_) => {}
                        Err(c) => out += &self.elab_drop(l, &sub(Step::Elem(c))),
                    }
                }
            }
            // An `array::IntoIter`'s still-owned part is a range, not
            // a set of move paths: its glue drops exactly that range.
            CTy::ArrayIter(..) => {
                if needs_drop_c(self.p, t) {
                    self.want(Glue::Drop, t);
                    let _ = write!(out, " drop_{}(&{e});", mangle(t));
                }
            }
            CTy::Boxed(inner) => {
                // Drop the still-owned part behind the pointer,
                // then free the allocation itself (its `sizeof` needs the type defined).
                out += &self.elab_drop(l, &sub(Step::Deref));
                self.note_held(inner);
                let et = ctype(inner);
                let _ = write!(out, " lust_dealloc((void*){e}, sizeof({et}), _Alignof({et}));");
            }
            _ if is_enum && variant.is_none() => {
                let d = self.disc(t, &format!("(&{e})"));
                let _ = write!(out, " switch ({d}) {{");
                for s in next_steps {
                    if let Step::Downcast(v) = s {
                        let body = self.elab_drop(l, &sub(s));
                        let _ = write!(out, " case {v}: {{{body} }} break;");
                    }
                }
                self.want(Glue::Drop, t);
                let _ = write!(out, " default: drop_{}(&{e}); break; }}", mangle(t));
            }
            _ => {
                let n = match t {
                    CTy::Tuple(es) => es.len(),
                    CTy::OptIter(..) => 1,
                    CTy::Adt(a) => self.p.adt(*a).variants.get(variant.unwrap_or(0)).map_or(0, |v| v.fields.len()),
                    CTy::Option(_) => usize::from(variant == Some(1)),
                    CTy::Result(..) => usize::from(variant.is_some()),
                    _ => 0,
                };
                for f in 0..n {
                    out += &self.elab_drop(l, &sub(Step::Field(f as u32)));
                }
            }
        }
        out
    }

    // ---------- Places and operands ----------

    /// Release C: a deref that starts an offset place (`OffsetPlace`): a `&`, `Box` or
    /// raw pointer to a struct or tuple with a known layout, or an `Rc`/`Arc` value
    /// (its offset in the count block). Returns the place, the plain C form of the
    /// deref (for a place that ends there) and the pointee type.
    fn offset_start(&self, pr: &Proj, t: &CTy, via: &mut Option<OffsetPlace>, e: &str) -> Option<(OffsetPlace, String, CTy)> {
        let (inner, off) = match (pr, t) {
            (Proj::Deref, CTy::Ref(inner) | CTy::Boxed(inner) | CTy::Ptr(inner)) if offset_layout(self.p, inner).is_some() => ((**inner).clone(), 0),
            (Proj::Deref, CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner)) => {
                let l = c_layout(self.p, inner).filter(|l| l.align > 0)?;
                ((**inner).clone(), 16u64.div_ceil(l.align) * l.align)
            }
            _ => return None,
        };
        // The pointer itself may sit at an offset (a field of an offset place).
        let ptr = match via.take() {
            Some(v) => v.render(t),
            None => e.to_string(),
        };
        let plain = if off == 0 { format!("(*{ptr})") } else { format!("(*({}*)((uint8_t*)({ptr}) + {off}))", ctype(&inner)) };
        Some((OffsetPlace { ptr, off, fields: off != 0, plain: plain.clone() }, plain, inner))
    }

    fn place(&mut self, pl: &Place, loc: &str) -> (String, CTy) {
        let mut e = match self.knames.get(&pl.local) {
            Some(n) => format!("(*({} *)&{n})", ctype(&self.local_cty[pl.local as usize])),
            None => format!("l{}", pl.local),
        };
        let mut t = self.local_cty[pl.local as usize].clone();
        let mut variant: Option<u32> = None;
        let release = names::release();
        // Release C reads fields through a pointer by offset (`OffsetPlace`): the unit
        // then depends on the offsets it reads and the field types, not on the whole
        // container, so a field added to a struct changes only units whose offsets move.
        let mut via: Option<OffsetPlace> = None;
        for pr in &pl.proj {
            if release {
                // An offset place casts to a pointer to its current type (`render`): the
                // unit needs what a `&T` local would.
                if let Some(start) = self.offset_start(pr, &t, &mut via, &e) {
                    (via, e, t) = (Some(start.0), start.1, start.2);
                    self.note_held(&CTy::Ref(Box::new(t.clone())));
                    continue;
                }
                if let Some(v) = via.as_mut() {
                    match (pr, &t) {
                        (Proj::Downcast(k), CTy::Adt(_) | CTy::Tuple(_)) => {
                            variant = Some(*k);
                            continue;
                        }
                        (Proj::Field(i), _) if let Some((off, ft)) = field_offset(self.p, &t, variant, *i) => {
                            variant = None;
                            v.off += off;
                            v.fields = true;
                            t = ft;
                            self.note_held(&CTy::Ref(Box::new(t.clone())));
                            continue;
                        }
                        _ => {}
                    }
                }
                if let Some(v) = via.take() {
                    e = v.render(&t);
                }
            }
            // Release C defines only what a unit holds by value (`type_decls`): a field
            // or element read needs its container defined (behind a pointer too), an
            // index the element type, a deref of an `Rc` or a guard the block it reads.
            // A bare reborrow (`&*p`) takes only an address.
            if names::release() {
                match (pr, &t) {
                    (Proj::Deref, CTy::Ref(_) | CTy::Boxed(_) | CTy::Ptr(_)) | (Proj::Downcast(_), _) => {}
                    // (`offset_start` reads an `Rc` value with a layout by offset.)
                    (Proj::Deref, CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner)) if c_layout(self.p, inner).is_some_and(|l| l.align > 0) => {}
                    (Proj::Index(_), CTy::Vec(el) | CTy::Slice(el) | CTy::BoxSlice(el)) => {
                        let el = (**el).clone();
                        self.note_held(&el)
                    }
                    // A guard's deref reads the value in its cell (a RefCell's `f1`, a lock's
                    // `v`): the cell's definition, not what the value points at.
                    (Proj::Deref, CTy::Guard(inner, _)) => {
                        let cell = CTy::RefCell(inner.clone());
                        self.note_held(&cell)
                    }
                    (Proj::Deref, CTy::Sync(k, inner)) if let Some((lock, _)) = k.guard() => {
                        let cell = CTy::Sync(lock, inner.clone());
                        self.note_held(&cell)
                    }
                    // A field of a value (`l1.u.v1.f0`) needs the container's definition, not
                    // what its fields point at. A kind with no struct of its own keeps the
                    // whole closure.
                    (Proj::Field(_), _) => {
                        let t = t.clone();
                        let mut held = Vec::new();
                        by_value_deps(&t, &mut held);
                        if held.is_empty() { collect_types(&t, &mut self.sig_types) } else { self.note_held(&t) }
                    }
                    _ => collect_types(&t, &mut self.sig_types),
                }
            }
            match (pr, t.clone()) {
                (Proj::Deref, CTy::Ref(inner)) => {
                    if *inner == CTy::Str {
                        // A `str` place is represented by its fat `&str` value.
                        t = CTy::Str;
                    } else {
                        e = format!("(*{e})");
                        t = *inner;
                    }
                }
                // The dyn place behind an owning fat pointer is its fat
                // value, as behind `&dyn` (the data points at the value).
                (Proj::Deref, CTy::BoxDyn | CTy::RcDyn) => {
                    t = CTy::Dyn;
                }
                (Proj::Deref, CTy::Boxed(inner)) => {
                    e = format!("(*{e})");
                    t = *inner;
                }
                (Proj::Deref, CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner)) => {
                    // Release C reaches the value by its offset in the count block
                    // (two words, then the value at its alignment), so a unit that
                    // only borrows through an `Rc` needs no definition of the block.
                    e = match c_layout(self.p, &inner) {
                        Some(l) if names::release() && l.align > 0 => {
                            let off = 16u64.div_ceil(l.align) * l.align;
                            format!("(*({}*)((uint8_t*)({e}) + {off}))", ctype(&inner))
                        }
                        _ => format!("{e}->v"),
                    };
                    t = *inner;
                }
                (Proj::Deref, CTy::Guard(inner, _)) => {
                    e = format!("{e}->f1");
                    t = *inner;
                }
                // A lock guard points at its lock (W-THREADS).
                (Proj::Deref, CTy::Sync(k, inner)) if k.guard().is_some() => {
                    e = format!("{e}->v");
                    t = *inner;
                }
                (Proj::Field(i), CTy::Adt(a)) => {
                    let v = variant.take();
                    e = match v {
                        Some(v) => format!("{e}.u.v{v}.f{i}"),
                        None => format!("{e}.f{i}"),
                    };
                    let fty = self.p.adt(a).variants[v.unwrap_or(0) as usize].fields[*i as usize].ty;
                    t = cty(&self.p.tys, fty);
                }
                (Proj::Downcast(_), CTy::Option(_)) => {}
                (Proj::Field(_), CTy::Option(inner)) => {
                    e = variant_field(self.p, &t, &e, 1, 0);
                    t = *inner;
                }
                (Proj::Downcast(v), CTy::Result(..)) => variant = Some(*v),
                (Proj::Field(_), CTy::Result(ok_t, err_t)) => {
                    let v = variant.take().unwrap_or(0);
                    e = variant_field(self.p, &t, &e, v as usize, 0);
                    t = if v == 0 { *ok_t } else { *err_t };
                }
                (Proj::Downcast(v), _) => variant = Some(*v),
                (Proj::Index(l), CTy::Vec(el)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&format!("{e}.len"), &format!("(({}*){e}.ptr)", ctype(&el)), *l, &loc, b),
                        _ => format!("(({}*){e}.ptr)[lust_bounds(l{l}, {e}.len, {loc})]", ctype(&el)),
                    };
                    t = *el;
                }
                (Proj::Field(i), CTy::Tuple(es)) => {
                    e = format!("{e}.f{i}");
                    t = es[*i as usize].clone();
                }
                (Proj::Field(0), CTy::OptIter(_, el)) => {
                    e = format!("{e}.f0");
                    t = CTy::Option(el);
                }
                (Proj::Field(i), CTy::ArrayIter(el, n)) => {
                    e = format!("{e}.f{i}");
                    t = match *i {
                        0 => CTy::Array(el, n),
                        _ => CTy::Int(IntTy::Usize),
                    };
                }
                (Proj::Index(l), CTy::Array(el, n)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&n.to_string(), &format!("{e}.v"), *l, &loc, b),
                        _ => format!("{e}.v[lust_bounds(l{l}, {n}, {loc})]"),
                    };
                    t = *el;
                }
                (Proj::Deref, CTy::Slice(_)) | (Proj::Deref, CTy::Dyn) => {
                    // A slice or dyn place is represented by its fat value, like `str`.
                }
                (Proj::Deref, CTy::Unsized(..)) => {}
                // A `&RefCell<dyn Tr>` (`&Mutex<dyn Tr>`) is the fat place too.
                (Proj::Deref, CTy::DynCell | CTy::DynLock(false)) => {}
                (Proj::Field(0), CTy::Unsized(_, inner)) => {
                    // The field of an unsized newtype (W-SHIM): the same fat value.
                    t = *inner;
                }
                (Proj::Deref, CTy::BoxSlice(el)) => {
                    // The boxed slice's fat value is its slice place too.
                    t = CTy::Slice(el);
                }
                // So is an owning fat pointer's (cgen/own.rs).
                (Proj::Deref, CTy::Own(_, x)) => {
                    t = *x;
                }
                // A `Ref<dyn Tr>`'s value sits after the cell's flag.
                (Proj::Deref, CTy::DynGuard(_)) => {
                    e = own::dyn_cell_value(&e);
                    t = CTy::Dyn;
                }
                (Proj::Deref, CTy::DynLock(true)) => {
                    e = own::dyn_lock_value(&e);
                    t = CTy::Dyn;
                }
                // A boxed slice indexes as its fat slice value (a `for` over
                // `&Box<[T]>` walks it as `&Vec<T>` is walked).
                (Proj::Index(l), CTy::Slice(el) | CTy::BoxSlice(el)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&format!("{e}.len"), &format!("{e}.ptr"), *l, &loc, b),
                        _ => format!("{e}.ptr[lust_bounds(l{l}, {e}.len, {loc})]"),
                    };
                    t = *el;
                }
                (pr, t) => panic!("bad projection in codegen: {pr:?} on {t:?}"),
            }
        }
        if let Some(v) = via.take() {
            e = v.render(&t);
        }
        // A place read by value or by discriminant needs its type defined.
        if names::release() && !self.addr_only {
            self.note_held(&t);
        }
        (e, t)
    }

    /// An indexed element place under panic=unwind: a GNU statement
    /// expression whose failed bounds check panics and leaves for the
    /// cleanup at block `b` before any element is read. The `(void)`
    /// keeps `wrap_calls` from adding its own check in front of `b`.
    fn index_unw(&self, len: &str, base: &str, l: Local, loc: &str, b: u32) -> String {
        if self.p.unwind_tables {
            // The bounds panic never returns: the frame's cleanup runs from `L.st`.
            return format!(
                "(*({{ if (__builtin_expect(l{l} >= {len}, 0)) {{ (void)lust_bounds(l{l}, {len}, {loc}); __builtin_unreachable(); }} &{base}[l{l}]; }}))"
            );
        }
        format!("(*({{ if (l{l} >= {len}) {{ (void)lust_bounds(l{l}, {len}, {loc}); lust_unw_take(&ex); goto bb{b}; }} &{base}[l{l}]; }}))")
    }

    fn operand(&mut self, o: &Operand, loc: &str, post: &mut Vec<String>) -> (String, CTy) {
        match o {
            Operand::Copy(pl) => self.place(pl, loc),
            Operand::Move(pl) => {
                let (e, t) = self.place(pl, loc);
                if self.local_drop[pl.local as usize] {
                    if pl.proj.is_empty() {
                        // Moving the whole local: it owns nothing now (a static flag has
                        // nothing to clear).
                        if self.dflags.store(self.at, pl.local, Store::Clear) {
                            post.push(format!("d{} = 0;", pl.local));
                        }
                    } else if let Some(path) = self.steps_of(pl)
                        && let Some(k) = self.move_flag(pl.local, &path)
                    {
                        // Moving one field out (a partial move, or an enum payload): the
                        // local's later drops skip this path (see `elab_drop`).
                        post.push(format!("m{}_{k} = 0;", pl.local));
                    }
                }
                (e, t)
            }
            Operand::Const(c) => match c {
                Const::Int(v, it) => {
                    let lit = if is128(*it) {
                        format!("(({}){{{}ULL, {}ULL}})", int_c(*it), *v as u64, (*v >> 64) as u64)
                    } else if *v < (1 << 31) {
                        v.to_string()
                    } else {
                        format!("(({}){}ULL)", int_c(*it), *v as u64)
                    };
                    (lit, CTy::Int(*it))
                }
                Const::Float(bits, f) => {
                    let lit = match f {
                        FloatTy::F64 => format!("(((union {{ uint64_t b; double d; }}){{ .b = {}ull }}).d)", bits),
                        FloatTy::F32 => format!("(((union {{ uint32_t b; float f; }}){{ .b = {}u }}).f)", *bits as u32),
                    };
                    (lit, CTy::Float(*f))
                }
                Const::Bool(b) => ((*b as u8).to_string(), CTy::Bool),
                Const::Char(c) => (format!("((uint32_t){})", *c as u32), CTy::Char),
                Const::Str(i) => {
                    let s = &self.p.ast.strings[*i as usize];
                    (self.kstr(s.as_bytes()), CTy::Ref(Box::new(CTy::Str)))
                }
                Const::StrBytes(b) => (self.kstr(b.as_slice()), CTy::Ref(Box::new(CTy::Str))),
                Const::Bytes(b) => {
                    let t = CTy::Array(Box::new(CTy::Int(IntTy::U8)), b.len() as u64);
                    (bytes_array_lit(self.p, &t, b.as_slice()), t)
                }
                Const::Unit => ("((lust_Unit){})".into(), CTy::Unit),
            },
        }
    }

    // ---------- Statements ----------

    /// Stores a computed value into `dest`, dropping the old value first when
    /// the local owns one. Shared by `Assign` statements and `Call`
    /// terminators: `make_value` produces the value text (and may emit helper
    /// statements into the block this opens), and `mentions` says whether
    /// producing the value reads `dest` itself.
    fn emit_assign(
        &mut self,
        dest: &Place,
        mentions: bool,
        loc: &str,
        make_value: impl FnOnce(&mut Self, &str, &mut Vec<String>) -> String,
    ) {
        // Value generation may emit helper statements with temporaries, so open a C block lazily.
        let mark = self.out.len();
        self.out.push_str("  {\n");
        let body_start = self.out.len();
        let mut post = Vec::new();
        let value = make_value(self, loc, &mut post);
        let (d, dt) = self.place(dest, loc);
        let drop = needs_drop_c(self.p, &dt);
        // A statement whose destination is a whole local with nothing to
        // drop writes it directly: a value left there by a panic is never
        // read, and the statement's own check follows (`function`).
        let unw = self.unw.filter(|_| self.unw_call || drop || !dest.proj.is_empty());
        // R3: a value that cannot unwind at any point, into a whole local that holds no value
        // on any path here (its flag is statically clear): there is no old value to drop and
        // no panic can come between the write and the flag set, so the local is written
        // directly, with no temporary and no check.
        if unw.is_some()
            && self.r3_value
            && !self.unw_call
            && dest.proj.is_empty()
            && !mentions
            && drop
            && self.dflags.test(self.at, dest.local) == Some(false)
        {
            let (_, refill) = self.drop_old_value(dest, &d, &dt);
            let _ = writeln!(self.out, "    {d} = {value};");
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            if !refill.is_empty() {
                let _ = writeln!(self.out, "   {refill}");
            }
            self.out.push_str("  }\n");
            return;
        }
        if let Some(u) = unw {
            // panic=unwind: the value goes to a temporary first and the
            // check runs before the old value drops or the place is
            // written, so a panic leaves the destination as it was.
            // A call owns its moved arguments from the start, so their
            // flags clear before it runs: a panic inside it must not drop
            // them again here. A statement moves only at its end.
            if self.unw_call {
                let flags: String = post.iter().map(|p| format!("    {p}\n")).collect();
                self.out.insert_str(body_start, &flags);
                post.clear();
            }
            let t = self.tmp();
            let _ = writeln!(self.out, "    {} {t} = {value};", ctype(&dt));
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            let zc = self.p.unwind_tables;
            if !zc {
                let _ = writeln!(self.out, "    {}", u.check());
            }
            if zc && drop && dest.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
                // An index out of bounds panics before the value moves into the
                // place: a guard drops the value as the panic unwinds.
                let (gd, gdis) = self.zc_guard(&t, &dt);
                let (pd, _) = self.place(dest, loc);
                let _ = writeln!(self.out, "   {gd}\n    (void)&{pd};\n   {gdis}");
            }
            if drop
                && !zc
                && let Unw::Goto(cb) = u
                && dest.proj.iter().any(|p| matches!(p, Proj::Index(_)))
            {
                // An index out of bounds panics before the value moves
                // into the place (rustc checks bounds first), so the
                // value drops as cleanup: the place's bounds checks run
                // once here with a local cleanup label that drops it.
                self.tmp += 1;
                let lab = 1_000_000_000 + self.tmp;
                self.unw = Some(Unw::Goto(lab));
                let (pd, _) = self.place(dest, loc);
                self.unw = Some(u);
                self.want(Glue::Drop, &dt);
                let _ = writeln!(self.out, "    (void)&{pd};");
                let _ = writeln!(self.out, "    if (0) {{ bb{lab}:; (void)(drop_{}(&{t}), 0); LUST_UNW_ABORT(); goto bb{cb}; }}", mangle(&dt));
            }
            if drop {
                let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
                // A drop that panics leaves the local unowned, so its
                // cleanup does not drop it again.
                let drop_old = if dest.proj.is_empty() && self.dflags.keeps(dest.local) && self.dflags.test(self.at, dest.local).is_none() {
                    drop_old.replacen(" {", &format!(" {{ d{} = 0;", dest.local), 1)
                } else {
                    drop_old
                };
                let _ = writeln!(self.out, "   {drop_old}\n    {d} = {t};\n   {refill}");
            } else {
                let _ = writeln!(self.out, "    {d} = {t};");
            }
            self.out.push_str("  }\n");
            return;
        }
        if drop && dest.proj.is_empty() && !mentions {
            // The old value is dropped before the new one is written. Safe because the
            // rvalue does not read the destination.
            let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
            if self.out.len() == body_start {
                self.out.truncate(mark);
                let _ = write!(self.out, " {drop_old} {d} = {value};{refill}");
                for p in &post {
                    let _ = write!(self.out, " {p}");
                }
                self.out.push('\n');
                return;
            }
            let _ = writeln!(self.out, "   {drop_old}\n    {d} = {value};\n   {refill}");
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            self.out.push_str("  }\n");
            return;
        }
        if drop {
            let t = self.tmp();
            let _ = writeln!(self.out, "    {} {t} = {value};", ctype(&dt));
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
            let _ = writeln!(self.out, "   {drop_old}\n    {d} = {t};\n   {refill}");
        } else {
            // A plain local of str type is a compiler place temporary
            // holding the fat value itself; assigning it is a fat copy.
            // A projected str place would be an unsized byte copy.
            if dt == CTy::Str && !dest.proj.is_empty() {
                panic!("unsized assignment");
            }
            if self.out.len() == body_start && post.is_empty() {
                // No helper statements: a plain assignment needs no block.
                self.out.truncate(mark);
                let _ = writeln!(self.out, "  {d} = {value};");
                return;
            }
            let _ = writeln!(self.out, "    {d} = {value};");
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
        }
        self.out.push_str("  }\n");
    }

    fn stmt(&mut self, s: &StmtKind, span: Span) {
        let loc = self.loc(span);
        match s {
            // A byte string temp is a static initialized at its
            // declaration: its one blob assignment never runs.
            StmtKind::Assign(dest, Rvalue::Use(Operand::Const(Const::Bytes(b))))
                if dest.proj.is_empty()
                    && self.byte_blobs.get(dest.local as usize).is_some_and(|x| x.as_ref().is_some_and(|x| x.as_slice() == b.as_slice())) =>
            {
            }
            // A compile-time promoted local's value is its static
            // initializer (`kstatic`): its defining assignment never runs.
            StmtKind::Assign(dest, _) if dest.proj.is_empty() && self.kstatic.contains_key(&dest.local) => {}
            StmtKind::Assign(dest, rv) => {
                // A promoted constant is the same value on every run: once its site has
                // interned it (`lk{i}` set), the write is skipped, so threads do not all
                // write the one static again.
                let kguard = self.body.promoted.contains(&dest.local) && self.kconst_local(dest.local as usize);
                if kguard {
                    let _ = writeln!(self.out, "  if (!lk{}) {{", dest.local);
                }
                let mentions = rvalue_mentions(rv, dest.local);
                let dest_cty = self.place(dest, &loc).1;
                self.r3_value = inplace(self.p).r3 && !crate::ir::dropflags::may_panic_before_moves(dest, rv);
                self.emit_assign(dest, mentions, &loc, |s, loc, post| match rv {
                    // A never value (which shares the unit C form) used
                    // where another type is expected never actually
                    // arrives: give the dead assignment a zero of the
                    // destination type.
                    Rvalue::Use(o) => {
                        let (v, vt) = s.operand(o, loc, post);
                        if vt == CTy::Unit && dest_cty != CTy::Unit { format!("({v}, {})", zero_lit(s.p, &dest_cty)) } else { v }
                    }
                    _ => s.rvalue(rv, loc, post),
                });
                self.r3_value = false;
                if kguard {
                    self.out.push_str("  }\n");
                }
            }
            StmtKind::Drop(l) => {
                if self.local_drop[*l as usize] {
                    let what = self.elab_drop(*l, &[]);
                    match self.dflags.test(self.at, *l) {
                        None => {
                            let _ = writeln!(self.out, "  if (d{l}) {{ d{l} = 0;{what} }}");
                        }
                        // Set on every path here: the drop is unconditional; a runtime flag is
                        // cleared first when a test can read it. (Clear on every path: no
                        // drop, but its glue stays wanted, as other C names it.)
                        Some(true) => {
                            let clear = if self.dflags.store(self.at, *l, Store::DropClear) { format!(" d{l} = 0;") } else { String::new() };
                            let _ = writeln!(self.out, " {clear}{what}");
                        }
                        Some(false) => {}
                    }
                }
            }
            StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {}
            StmtKind::Print { stderr, newline, parts } => {
                self.out.push_str("  {\n");
                let mut post = Vec::new();
                self.print(parts, *newline, *stderr, &loc, &mut post);
                self.out.push_str("  }\n");
            }
        }
    }

    fn term(&mut self, t: &Terminator, span: Span, next_block: Option<usize>) {
        let loc = self.loc(span);
        let mut post = Vec::new();
        match t {
            Terminator::Goto(b) => {
                let _ = writeln!(self.out, "  goto bb{};", b.0);
            }
            Terminator::If(o, a, b) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = writeln!(self.out, "  if ({c}) goto bb{}; else goto bb{};", a.0, b.0);
            }
            Terminator::Switch(o, cases, other) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = write!(self.out, "  switch ({c}) {{");
                for (v, b) in cases {
                    let _ = write!(self.out, " case {v}: goto bb{};", b.0);
                }
                let _ = writeln!(self.out, " default: goto bb{}; }}", other.0);
            }
            Terminator::Call { target, args, dest, next, unwind } => {
                // Calls carry a cleanup (unwind) successor since
                // W-CORELANG. Under panic=abort the C form has no edge to
                // it: a panic in the callee aborts first. Under
                // panic=unwind the call is checked and the edge taken
                // (cgen/unwind.rs); a call without one (a catch
                // boundary) is not checked.
                if self.unw != Some(Unw::Abort) {
                    self.unw = unwind.filter(|_| self.p.unwind).map(|u| Unw::Goto(u.0));
                }
                let zc = self.p.unwind && self.p.unwind_tables;
                if zc && let Some(Unw::Goto(b)) = self.unw {
                    self.zc_store(b);
                }
                let mark = self.out.len();
                self.unw_call = true;
                let mentions =
                    args.iter().any(|o| operand_mentions(o, dest.local)) || matches!(target, CallTarget::Indirect(c) if *c == dest.local);
                // A call to a never fn (unit C form) whose destination
                // has another type: the call never returns, so give the
                // dead assignment a zero of the destination type.
                let dest_cty = self.place(dest, &loc).1;
                let ret_unit = match target {
                    CallTarget::Fn(f) => cty(&self.p.tys, self.p.fn_info(*f).ret) == CTy::Unit,
                    CallTarget::Intrinsic(id) => lang::intrinsic(*id).ret == SigTy::Never,
                    CallTarget::Indirect(c) => matches!(&self.local_cty[*c as usize], CTy::FnPtr(_, r) if **r == CTy::Unit),
                    // `resume_unwind` and `panic_any` return `!` (W-UNWIND).
                    CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::ResumeUnwind | crate::check::sync::SyncOp::PanicAny)) => true,
                    // Lowering gives a dyn call a destination of the
                    // method's own return type.
                    CallTarget::Builtin(_) | CallTarget::Dyn(_) => false,
                };
                // Unwind tables: a call into a whole local that its arguments do not read, with no
                // old value to drop (a type without drop glue, a flag `flags_maybe_set` proves
                // clear, or a static flag clear here), writes the local itself, and a large return
                // gets it as the out-pointer: a panic inside never returns here, and the cleanup
                // sees the clear flag.
                let direct = zc
                    && !self.zc_in_cleanup
                    && dest.proj.is_empty()
                    && !mentions
                    && !ret_unit
                    && matches!(target, CallTarget::Fn(_) | CallTarget::Dyn(_) | CallTarget::Indirect(_))
                    && (!needs_drop_c(self.p, &dest_cty)
                        || self.flags_at_term.get(self.cur_bb).is_some_and(|f| !f[dest.local as usize])
                        || self.dflags.test(self.at, dest.local) == Some(false))
                    && self.r1_out_ok(dest.local, &dest_cty);
                if direct {
                    let d = self.place(dest, &loc).0;
                    self.out.push_str("  {\n");
                    let body_start = self.out.len();
                    let mut post = Vec::new();
                    self.call_out = Some(d.clone());
                    let v = self.call_value(*target, args, &dest_cty, &loc, &mut post);
                    self.call_out = None;
                    // A call owns its moved arguments from the start (as in `emit_assign`).
                    let flags: String = post.iter().map(|p| format!("    {p}\n")).collect();
                    self.out.insert_str(body_start, &flags);
                    if v != d {
                        let _ = writeln!(self.out, "    {d} = {v};");
                    }
                    if needs_drop_c(self.p, &dest_cty) {
                        let l = dest.local;
                        let set = if self.dflags.store(self.at, l, Store::Set) { format!(" d{l} = 1;") } else { String::new() };
                        let _ = writeln!(self.out, "   {set}{}", self.reset_move_flags(l, &[]));
                    }
                    self.out.push_str("  }\n");
                } else if *target == CallTarget::Builtin(Builtin::DefaultGlue) {
                    // The default glue of the destination's type.
                    let v = match &dest_cty {
                        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(self.p, &dest_cty),
                        t => {
                            self.want(Glue::Default, t);
                            format!("default_{}()", mangle(t))
                        }
                    };
                    self.emit_assign(dest, mentions, &loc, |_, _, _| v);
                } else {
                    self.emit_assign(dest, mentions, &loc, |s, loc, post| {
                        let v = s.call_value(*target, args, &dest_cty, loc, post);
                        if ret_unit && dest_cty != CTy::Unit { format!("({v}, {})", zero_lit(s.p, &dest_cty)) } else { v }
                    });
                }
                self.unw_call = false;
                if let Some(u) = self.unw.take()
                    && !zc
                {
                    let text = unwind::wrap_calls(&self.out[mark..], &u.check());
                    self.out.truncate(mark);
                    self.out.push_str(&text);
                }
                if Some(next.0 as usize) != next_block {
                    let _ = writeln!(self.out, "  goto bb{};", next.0);
                }
            }
            Terminator::Return => {
                // Unwind tables: a normal return leaves no ladder to run (the frame's
                // cleanup variable runs at scope exit too).
                if self.zc_frame && !self.zc_in_cleanup {
                    self.out.push_str("  L.st = 0;\n");
                }
                if self.r1 {
                    // R1: the value is already in the caller's storage.
                    self.out.push_str("  return;\n")
                } else if self.ret_large {
                    self.out.push_str("  *out = l0; return;\n")
                } else {
                    self.out.push_str("  return l0;\n")
                }
            }
            // The last block of a cleanup ladder: the frame gives its
            // exception back and leaves (panic=unwind). With unwind tables
            // the cleanup fn returns and the unwinder goes on.
            Terminator::Unreachable if self.unw == Some(Unw::Abort) && self.zc_in_cleanup => self.out.push_str("  return;\n"),
            Terminator::Unreachable if self.unw == Some(Unw::Abort) => {
                let _ = writeln!(self.out, "  lust_unw_resume(&ex);\n  {}", self.unwind_return());
            }
            Terminator::Unreachable => self.out.push_str("  abort();\n"),
            // An exhaustive match's otherwise edge: as rustc, release C lets the C compiler
            // assume it never runs, so a tag test that only guarded it folds away. Dev C and
            // any build with debug assertions or overflow checks abort, as `Unreachable` does.
            Terminator::MatchExhausted if self.unw != Some(Unw::Abort) && assume_unreachable(self.p) => {
                self.out.push_str("  __builtin_unreachable();\n")
            }
            Terminator::MatchExhausted => self.term(&Terminator::Unreachable, span, next_block),
            Terminator::Panic(parts)
                if self.p.unwind
                    && self.p.unwind_tables
                    && parts.iter().any(|p| matches!(p, FmtPart::Arg { .. }))
                    && let Some(call) = self.panic_outlined(parts, &loc) =>
            {
                let _ = writeln!(self.out, "  {call}\n  __builtin_unreachable();");
            }
            Terminator::Panic(parts) => {
                self.out.push_str("  {\n");
                // A message with arguments formats inside the panic (std's
                // lazy payload): a panic while it formats aborts as a
                // nested panic, and a fmt error just ends the text.
                if parts.iter().any(|p| matches!(p, FmtPart::Arg { .. })) {
                    let _ = writeln!(self.out, "    lust_panic_begin({loc});");
                    let s = self.format(parts, &loc, &mut post, 4);
                    let _ = writeln!(self.out, "    lust_panic_fmt(&{s}, {loc});\n  }}");
                } else {
                    // No runtime argument: Rust's `&'static str` payload
                    // (W-STD-B's `fmt_parts` inlines literal arguments).
                    let s = self.format(parts, &loc, &mut post, 0);
                    let _ = writeln!(self.out, "    lust_panic_lit(&{s}, {loc});\n  }}");
                }
                if let Some(Unw::Goto(b)) = self.unw
                    && !(self.p.unwind && self.p.unwind_tables)
                {
                    let _ = writeln!(self.out, "  lust_unw_take(&ex);\n  goto bb{b};");
                }
                // Unwind tables: the panic never returns.
                if self.p.unwind && self.p.unwind_tables {
                    self.out.push_str("  __builtin_unreachable();\n");
                }
            }
        }
    }

    // ---------- Rvalues ----------

    /// Unwind tables: a panic whose message has arguments formats in a cold, never inlined,
    /// noreturn fn of its own (in the unit before this fn), as rustc's panic paths do, so
    /// the fn that panics stays small; the site passes its location and pointers to the
    /// locals the message reads. None (format inline) when the text reads more than plain
    /// locals, such as an interned constant's slot or the frame struct.
    fn panic_outlined(&mut self, parts: &[FmtPart], loc: &str) -> Option<String> {
        // The location is a parameter too: a #[track_caller] fn's is its caller's.
        let saved = std::mem::take(&mut self.out);
        let mut post = Vec::new();
        self.out.push_str("  lust_panic_begin(qloc);\n");
        let s = self.format(parts, "qloc", &mut post, 4);
        let _ = writeln!(self.out, "  lust_panic_fmt(&{s}, qloc);");
        let body = std::mem::replace(&mut self.out, saved);
        // The identifiers the text reads: `l<N>` locals move to parameters; `lk..`
        // slots, `L.` frame fields and `ex` belong to this fn and cannot move.
        let bytes = body.as_bytes();
        let mut used = std::collections::BTreeSet::new();
        let mut i = 0;
        while i < bytes.len() {
            let c = bytes[i];
            if c.is_ascii_alphabetic() || c == b'_' {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let word = &body[start..i];
                if word.starts_with("lk") || (word == "L" && bytes.get(i) == Some(&b'.')) || word == "ex" {
                    return None;
                }
                if let Some(n) = word.strip_prefix('l')
                    && !n.is_empty()
                    && n.bytes().all(|b| b.is_ascii_digit())
                {
                    let n: usize = n.parse().ok()?;
                    if n >= self.local_cty.len() || c_size_align(self.p, &self.local_cty[n]).1 > 16 {
                        return None;
                    }
                    used.insert(n);
                }
            } else if c.is_ascii_digit() {
                while i < bytes.len() && bytes[i].is_ascii_alphanumeric() {
                    i += 1;
                }
            } else if c == b'"' {
                // A C string literal.
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                i += 1;
            } else {
                i += 1;
            }
        }
        // Named by the fn's tag (its stable id in release C), not its slot, which moves.
        let name = format!("pk{}_{}", names::fn_tag(self.slots.of(self.body.fn_id)), self.tmp());
        let params: Vec<String> =
            std::iter::once("lust_loc qloc".to_string()).chain(used.iter().map(|n| format!("{} *q{n}", ctype(&self.local_cty[*n])))).collect();
        let defs: String = used.iter().map(|n| format!("#define l{n} (*q{n})\n")).collect();
        let undefs: String = used.iter().map(|n| format!("#undef l{n}\n")).collect();
        // Release C: external, so another unit's inline copy of this fn calls it
        // (`plain_fn_def`); the tag makes the name unique in the program.
        let linkage = if names::release() { "" } else { "static " };
        let _ = writeln!(self.prelude, "{linkage}{PK_ATTRS}{name}({}) {{\n{defs}{body}{undefs}}}", params.join(", "));
        let args: Vec<String> = std::iter::once(loc.to_string()).chain(used.iter().map(|n| format!("&l{n}"))).collect();
        Some(format!("{name}({});", args.join(", ")))
    }

    /// Records a type the code uses by value (a call's parameter or result, a place it
    /// reads, an element it indexes). Release C defines only what `t` holds by value and
    /// names what it points at, so a unit does not change when a struct behind an `Rc` or
    /// a `&` does. Dev C defines all of it.
    fn note_held(&mut self, t: &CTy) {
        if names::release() {
            let mut held = Vec::new();
            by_value_deps(t, &mut held);
            self.sig_types.extend(held);
            collect_types(t, &mut self.sig_named);
        } else {
            collect_types(t, &mut self.sig_types);
        }
    }

    /// A fn pointer type whose parameters and result a shim this fn emits takes and
    /// returns by value (a definition needs them complete), and the type itself.
    fn note_fn_sig(&mut self, t: &CTy) {
        self.note_held(t);
        if let CTy::FnPtr(ps, r) = t {
            for x in ps.iter().chain(std::iter::once(&**r)) {
                self.note_held(x);
            }
        }
    }

    /// Release C: a builtin's operand or result type. Inline builtin code may open what
    /// the value points at, one step down: a reference's pointee, an `Rc`'s count block,
    /// a container's elements (also of a referenced container); `opens` is false for a
    /// builtin that opens nothing (`opens_nothing`).
    /// Kinds this does not model keep the whole closure.
    fn note_builtin(&mut self, t: &CTy, opens: bool) {
        self.note_held(t);
        match t {
            CTy::Ref(inner) | CTy::Boxed(inner) | CTy::Ptr(inner) => {
                self.note_held(inner);
                if opens {
                    self.note_opened(inner);
                }
            }
            _ if opens => self.note_opened(t),
            _ => {}
        }
    }

    /// The blocks and elements behind a value of `t` that builtin code reads (`note_builtin`).
    fn note_opened(&mut self, t: &CTy) {
        use crate::ty::sync::SyncTy;
        match t {
            // An `Arc` and the weak handles share the `Rc` count block (`RcI_<T>`).
            CTy::Rc(e) | CTy::Weak(e) | CTy::Sync(SyncTy::Arc | SyncTy::ArcWeak, e) => {
                self.sig_types.insert(CTy::Rc(e.clone()));
                collect_types(t, &mut self.sig_named);
            }
            CTy::Vec(e) | CTy::Slice(e) | CTy::BoxSlice(e) | CTy::VecIter(e) | CTy::VecDrain(e) | CTy::Array(e, _) => self.note_held(e),
            CTy::Option(e) => match &**e {
                CTy::Ref(x) | CTy::Boxed(x) => self.note_held(x),
                x => self.note_opened(x),
            },
            CTy::Hash(k, _) if hash::is_table(*k) => self.note_held(&hash::elem_cty(t)),
            // A cell or lock holds its value by value (`note_held` defines it); what the
            // value points at is opened as for the value itself.
            CTy::RefCell(e) | CTy::Cell(e) => self.note_opened(e),
            CTy::Sync(k, e) if k.is_cell_struct() => self.note_opened(e),
            // A `RefCell` guard points at the cell's block.
            CTy::Guard(e, _) => {
                self.sig_types.insert(CTy::RefCell(e.clone()));
                collect_types(t, &mut self.sig_named);
            }
            CTy::Int(_) | CTy::Float(_) | CTy::Bool | CTy::Char | CTy::Unit | CTy::Str | CTy::String | CTy::Adt(_) | CTy::Tuple(_) | CTy::Result(..) | CTy::FnPtr(..) => {}
            _ => collect_types(t, &mut self.sig_types),
        }
    }

    /// Records `f` as `bad_callee` when its slot will have no C: every
    /// reference to another fn's slot goes through here first.
    fn note_callee(&mut self, f: LocalDefId) {
        if self.bad_callee.is_none() && !has_generated_body(self.p, f) {
            self.bad_callee = Some(f);
        }
    }

    /// The C text of one call's result value. Every user fn call goes through
    /// `lust_fns`, so a changed function can be swapped in without relinking
    /// its callers.
    /// The out-pointer target of a large-return call: the destination the caller set in
    /// `call_out` (no declaration), else a new temporary of C type `ct` and its declaration.
    fn out_target(&mut self, ct: &str) -> (String, String) {
        match self.call_out.take() {
            Some(d) => (String::new(), d),
            None => {
                let t = self.tmp();
                (format!("{ct} {t}; "), t)
            }
        }
    }

    fn call_value(&mut self, target: CallTarget, args: &[Operand], dest_cty: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        // Release C defines only what a unit holds by value or projects from
        // (`type_decls_with`): a builtin may size or open what its operands and result
        // point at (an `Rc`'s count block, a `Vec`'s elements), one step down
        // (`note_builtin`).
        if names::release() && matches!(target, CallTarget::Builtin(_) | CallTarget::Intrinsic(_)) {
            let opens = !matches!(target, CallTarget::Builtin(b) if opens_nothing(b));
            self.note_builtin(dest_cty, opens);
            for o in args.iter().filter(|o| matches!(o, Operand::Move(_) | Operand::Copy(_))) {
                let t = cty(&self.body.tys, self.callable_place_ty(o));
                self.note_builtin(&t, opens);
            }
        }
        match target {
            CallTarget::Fn(f) => {
                self.note_callee(f);
                let info = self.p.fn_info(f);
                for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
                    let ct = cty(&self.p.tys, t);
                    self.note_held(&ct);
                }
                let ops = args;
                let mut args: Vec<String> = args.iter().map(|o| self.operand(o, loc, post).0).collect();
                // The LLVM backend calls the fn's internal ABI entry (cgen/ll.rs).
                if ll::on(self.p) {
                    return self.ll_fn_call(f, &args, loc);
                }
                let pts: Vec<CTy> = info.params.iter().map(|&t| cty(&self.p.tys, t)).collect();
                let mut pre = String::new();
                self.spill_by_ptr(&mut pre, &pts, &mut args);
                self.out.push_str(&pre);
                let dropped: Vec<bool> = info.params.iter().map(|&t| param_dropped(self.p, &cty(&self.p.tys, t))).collect();
                let mut i = 0;
                args.retain(|_| {
                    let keep = !dropped.get(i).copied().unwrap_or(false);
                    i += 1;
                    keep
                });
                // `#[track_caller]`: this call's location, or the one this
                // fn received when it is itself `#[track_caller]` (`loc`), with a
                // plain read of the location slot (`names::hot_loc`).
                if crate::check::caller::is_track_caller(self.p, f) {
                    args.push(names::hot_loc(loc));
                }
                if let Some(v) = self.unwrap_inline(f, ops, &args) {
                    return v;
                }
                if ret_is_large(self.p, f) {
                    let (decl, t) = self.out_target(&ctype(&cty(&self.p.tys, info.ret)));
                    let pre = if args.is_empty() { String::new() } else { format!(", {}", args.join(", ")) };
                    let _ = writeln!(self.out, "    {decl}{}(&{t}{pre});", self.slots.callee(self.p, f));
                    t
                } else {
                    format!("{}({})", self.slots.callee(self.p, f), args.join(", "))
                }
            }
            // `mpsc::channel()`: the element type comes from the pair.
            CallTarget::Builtin(Builtin::Sync(op @ (crate::check::sync::SyncOp::Channel | crate::check::sync::SyncOp::SyncChannel))) => {
                let cap = if op == crate::check::sync::SyncOp::SyncChannel { format!("(int64_t){}", self.operand(&args[0], loc, post).0) } else { "-1".into() };
                self.channel_new(dest_cty, &cap)
            }
            // `Mutex::default()`: the lock's Default glue (W-THREADS).
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::LockDefault(_) | crate::check::sync::SyncOp::SyncNew(crate::ty::sync::SyncTy::OnceLock))) => {
                self.want(Glue::Default, dest_cty);
                format!("default_{}()", mangle(dest_cty))
            }
            // A slice-to-array `TryFrom` (tf-slice): the destination
            // `Result` type tells the array length and whether the
            // Ok form is the array or a reference to it.
            CallTarget::Builtin(Builtin::SliceTryInto) => {
                let (sv, sct) = self.operand(&args[0], loc, post);
                let CTy::Result(ok, err) = dest_cty.clone() else { unreachable!() };
                let (arr, by_ref) = match &*ok {
                    CTy::Array(..) => ((*ok).clone(), false),
                    CTy::Ref(a) => ((**a).clone(), true),
                    _ => unreachable!(),
                };
                let CTy::Array(_, n) = &arr else { unreachable!() };
                let n = *n;
                let (ptr, len) = match &sct {
                    CTy::Slice(_) => (format!("{sv}.ptr"), format!("{sv}.len")),
                    CTy::Ref(inner) if matches!(&**inner, CTy::Slice(_)) => (format!("{sv}->ptr"), format!("{sv}->len")),
                    _ => unreachable!(),
                };
                let (ok_ct, err_ct) = (ctype(&ok), ctype(&err));
                let res = CTy::Result(ok, err);
                self.note_held(&res);
                let t = self.tmp();
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                // By value the elements are Copy (core's impl): one memcpy, which the C
                // compiler makes a single load and store for a small array (byte by byte,
                // a following 8-byte read of the array stalled on store forwarding).
                let ok_assign = if by_ref {
                    format!("{ok_f} = ({ok_ct}){ptr};")
                } else {
                    format!("lust_memcpy({ok_f}.v, {ptr}, {n} * sizeof({ok_f}.v[0]));")
                };
                let te = self.tmp();
                let _ = writeln!(self.out, "    {} {t}; {err_ct} {te}; {te}.f0 = ((lust_Unit){{}});", ctype(&res));
                let _ = writeln!(self.out, "    if ({len} == {n}) {{ {ok_assign} {ok_d} }} else {{ {err_f} = {te}; {err_d} }}");
                t
            }
            // Core's `TryFrom<Vec<T>> for [T; N]`: on a length match the
            // elements move into the array and the emptied Vec drops
            // (its buffer frees); else the Vec moves into `Err`.
            // Alloc's boxed-array pairs: on a length match the buffer
            // becomes the box (a Vec's shrunk to its length first, as
            // `into_boxed_slice` does); else the source moves into `Err`.
            CallTarget::Builtin(Builtin::VecTryInto) if matches!(dest_cty, CTy::Result(ok, _) if matches!(**ok, CTy::Boxed(_))) => {
                let (sv, sct) = self.operand(&args[0], loc, post);
                let CTy::Result(ok, err) = dest_cty.clone() else { unreachable!() };
                let CTy::Boxed(arr) = &*ok else { unreachable!() };
                let CTy::Array(el, n) = &**arr else { unreachable!("a boxed array") };
                let n = *n;
                let res = CTy::Result(ok.clone(), err);
                self.note_held(&res);
                let (t, v) = (self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                let (elc, arrc) = (ctype(el), ctype(arr));
                let _ = writeln!(self.out, "    {} {t}; {} {v} = {sv};", ctype(&res), ctype(&sct));
                let buf = if matches!(sct, CTy::Vec(_)) {
                    format!(
                        "(({v}.cap != {n} && sizeof({elc}) != 0) ? lust_realloc({v}.ptr, {v}.cap * sizeof({elc}), _Alignof({elc}), {n} * sizeof({elc})) : {v}.ptr)"
                    )
                } else {
                    format!("((void*){v}.ptr)")
                };
                let _ = writeln!(self.out, "    if ({v}.len == {n}) {{ {ok_f} = ({arrc}*){buf}; {ok_d} }} else {{ {err_f} = {v}; {err_d} }}");
                t
            }
            CallTarget::Builtin(Builtin::VecTryInto) => {
                let (sv, sct) = self.operand(&args[0], loc, post);
                let CTy::Result(ok, err) = dest_cty.clone() else { unreachable!() };
                let CTy::Array(el, n) = &*ok else { unreachable!() };
                let n = *n;
                let res = CTy::Result(ok.clone(), err);
                self.note_held(&res);
                self.want(Glue::Drop, &sct);
                let (t, v, i) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                let elc = ctype(el);
                let _ = writeln!(self.out, "    {} {t}; lust_Vec {v} = {sv};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if ({v}.len == {n}) {{ for (uint64_t {i} = 0; {i} < {n}; {i}++) {ok_f}.v[{i}] = (({elc}*){v}.ptr)[{i}]; {v}.len = 0; drop_{}(&{v}); {ok_d} }} else {{ {err_f} = {v}; {err_d} }}",
                    mangle(&sct)
                );
                t
            }
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::ChanTrySend)) => self.chan_try_send(args, dest_cty, loc, post),
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::TryLock(write))) => self.try_lock(write, args, dest_cty, loc, post),
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::AvailPar)) => self.avail_par(dest_cty, loc, post),
            // `MaybeUninit::uninit` and `zeroed` (TRIAGE T5): a
            // zero compound literal of the destination type (an
            // uninitialized value may hold any bytes; zero is one).
            // `env::args()`: the `IterKind::Args` state (front, back)
            // over every process argument.
            CallTarget::Builtin(Builtin::EnvArgs) => format!("(({}){{ 0, (uint64_t)lust_argc }})", ctype(dest_cty)),
            // A zeroed temporary, not `(T){0}`: a zero-sized `T` is an
            // empty C struct, which takes no initializer.
            CallTarget::Builtin(Builtin::MaybeUninitUninit | Builtin::MaybeUninitZeroed) => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t}; memset(&{t}, 0, sizeof({t}));", ctype(dest_cty));
                t
            }
            // `Box::new_uninit` and `new_zeroed`: a heap slot of the
            // `MaybeUninit<T>` the destination box points to. The bytes
            // are zero for both (any bytes are valid for uninit).
            CallTarget::Builtin(Builtin::BoxNewUninit | Builtin::BoxNewZeroed) => {
                let CTy::Boxed(mu) = dest_cty else { unreachable!("Box::new_uninit makes a Box") };
                let mt = ctype(mu);
                format!("(({mt}*)lust_alloc_zeroed(sizeof({mt}), _Alignof({mt})))")
            }
            // `Box::new_uninit_slice(n)`: RawVec's allocation for `n`
            // slots (its capacity overflow panic), zeroed by calloc (no
            // page is touched, as for Rust's uninit memory), as a boxed
            // slice of exactly `n`. Under panic=unwind the overflow
            // returns with cap 0 (an empty box, never written).
            CallTarget::Builtin(Builtin::BoxNewUninitSlice) => {
                let CTy::BoxSlice(mu) = dest_cty else { unreachable!("Box::new_uninit_slice makes a Box<[T]>") };
                let mt = ctype(mu);
                let (n, _) = self.operand(&args[0], loc, post);
                let (k, v, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {k} = {n}; lust_Vec {v} = lust_vec_with_capacity_zeroed({k}, sizeof({mt}), _Alignof({mt})); {} {t}; {t}.ptr = ({mt}*){v}.ptr; {t}.len = {} >= {k} ? {k} : 0;",
                    ctype(dest_cty),
                    vec_cap(&mt, &format!("&{v}"))
                );
                t
            }
            // `Box::write`: the slot's field 0 is the `T` at offset 0,
            // so the same pointer, cast, is the `Box<T>` to store into.
            CallTarget::Builtin(Builtin::BoxWrite) => {
                let (b, _) = self.operand(&args[0], loc, post);
                let (v, _) = self.operand(&args[1], loc, post);
                let t = self.tmp();
                let bt = ctype(dest_cty);
                let _ = writeln!(self.out, "    {bt} {t} = ({bt})({b}); *{t} = {v};");
                t
            }
            CallTarget::Builtin(Builtin::MaybeUninitNew) => {
                let (v, _) = self.operand(&args[0], loc, post);
                format!("(({}){{ {v} }})", ctype(dest_cty))
            }
            // alloc's `spare_capacity_mut`: `ptr.add(len)` for `capacity -
            // len` elements of `MaybeUninit<T>` (`T`'s C layout). A
            // zero-sized `T` keeps the dangling pointer.
            CallTarget::Builtin(Builtin::VecSpareCapacityMut) => {
                let (v, vt) = self.operand(&args[0], loc, post);
                let CTy::Ref(inner) = &vt else { unreachable!("spare_capacity_mut takes &mut Vec") };
                let CTy::Vec(e) = &**inner else { unreachable!("spare_capacity_mut takes &mut Vec") };
                let et = ctype(e);
                let zst = c_layout(self.p, e).is_some_and(|l| l.size == 0);
                let ptr = if zst { format!("({v})->ptr") } else { format!("(void*)((({et}*)({v})->ptr) + ({v})->len)") };
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t}; {t}.ptr = {ptr}; {t}.len = {} - ({v})->len;", ctype(dest_cty), vec_cap(&et, &v));
                t
            }
            CallTarget::Builtin(b) => match self.hash_builtin(b, args, dest_cty, loc, post) {
                Some(v) => v,
                None => match self.split_builtin(b, args, dest_cty, loc, post) {
                    Some(v) => v,
                    None => match self.bytes_builtin(b, args, dest_cty, loc, post) {
                        Some(v) => v,
                        None => match self.slice_split_builtin(b, args, dest_cty, loc, post) {
                            Some(v) => v,
                            None => self.builtin(b, args, loc, post),
                        },
                    },
                },
            },
            CallTarget::Intrinsic(id) => self.intrinsic(id, args, loc, post),
            CallTarget::Dyn(k) => {
                // Through the vtable: entry `k` is a shim whose receiver
                // is the erased data pointer (see `vtable_shim`). The
                // return type is the destination's, which lowering made
                // the method's own.
                let (r, _) = self.operand(&args[0], loc, post);
                let rt = self.tmp();
                let _ = writeln!(self.out, "    lust_dyn {rt} = {r};");
                let mut vals: Vec<String> = Vec::new();
                let mut pts: Vec<CTy> = Vec::new();
                for o in &args[1..] {
                    let (v, t) = self.operand(o, loc, post);
                    self.note_held(&t);
                    if !param_dropped(self.p, &t) {
                        pts.push(t);
                        vals.push(v);
                    }
                }
                let mut pre = String::new();
                self.spill_by_ptr(&mut pre, &pts, &mut vals);
                self.out.push_str(&pre);
                let mut tys: Vec<String> = vec!["void *".into()];
                tys.extend(pts.iter().map(|t| param_ctype(self.p, t)));
                let ret = dest_cty.clone();
                self.note_held(&ret);
                let rc = ctype(&ret);
                let pre: String = vals.iter().map(|v| format!(", {v}")).collect();
                if ret_by_out(self.p, &ret) {
                    let (decl, t) = self.out_target(&rc);
                    let _ = writeln!(self.out, "    {decl}((void (*)({rc} *, {}))({rt}.vt[{k}]))(&{t}, {rt}.data{pre});", tys.join(", "));
                    t
                } else {
                    format!("(({rc} (*)({}))({rt}.vt[{k}]))({rt}.data{pre})", tys.join(", "))
                }
            }
            CallTarget::Indirect(callee) => {
                let ct = self.local_cty[callee as usize].clone();
                let CTy::FnPtr(ps, ret) = &ct else { panic!("indirect call through a non-fn-pointer local") };
                // The call passes and returns by value what the pointer's type names.
                for t in ps.iter().chain(std::iter::once(&**ret)).chain(std::iter::once(&ct)) {
                    self.note_held(t);
                }
                let mut args: Vec<String> = args.iter().map(|o| self.operand(o, loc, post).0).collect();
                let mut pre = String::new();
                self.spill_by_ptr(&mut pre, ps, &mut args);
                self.out.push_str(&pre);
                let dropped: Vec<bool> = ps.iter().map(|t| param_dropped(self.p, t)).collect();
                let mut i = 0;
                args.retain(|_| {
                    let keep = !dropped.get(i).copied().unwrap_or(false);
                    i += 1;
                    keep
                });
                if ret_by_out(self.p, ret) {
                    let (decl, t) = self.out_target(&ctype(ret));
                    let pre = if args.is_empty() { String::new() } else { format!(", {}", args.join(", ")) };
                    let _ = writeln!(self.out, "    {decl}l{callee}(&{t}{pre});");
                    t
                } else {
                    format!("l{callee}({})", args.join(", "))
                }
            }
        }
    }

    /// Builds one enum or Option value as one compound literal that
    /// designates a single union member: the variant struct, which
    /// carries the explicit tag or the niche scalar as a member of
    /// its own, so tag and fields are set by the same designator.
    /// The same forms serve as constant initializers in `const_init`.
    /// A variant literal of `t`: it names `t`'s fields (`nested_block`).
    fn make_variant(&mut self, t: &CTy, variant: usize, vals: &[String]) -> String {
        self.note_held(t);
        variant_lit(self.p, t, variant, vals)
    }

    /// `disc_call`: the read needs `t`'s definition (`nested_block`).
    fn disc(&mut self, t: &CTy, ptr: &str) -> String {
        self.note_held(t);
        disc_call(self.p, t, ptr)
    }

    /// Release C: std's `unwrap` or `expect` of an Option or Result that the x86-64 ABI passes
    /// in two eightbytes cutting through its fields (9 to 16 bytes, aligned under 8, such as
    /// the `Result<[u8; 8], _>` of a slice `try_into`). Passed by value, the value stays in
    /// memory even when clang inlines the call (SROA cannot split it), and the loads that
    /// rebuild the eightbytes cannot take their data from its stores. So the payload is read
    /// here, and only the panic path calls the fn, with a copy. `args` are the call's C
    /// arguments (with the caller location); None for any other call.
    fn unwrap_inline(&mut self, f: LocalDefId, ops: &[Operand], args: &[String]) -> Option<String> {
        if !names::release() || (self.p.unwind && !self.p.unwind_tables) {
            return None;
        }
        let def = self.p.fn_info(f).def(&self.p.ast);
        if !matches!(self.p.name(def.name), "unwrap" | "expect") || !self.p.std_source_span(def.name_span) {
            return None;
        }
        let op = ops.first().filter(|o| matches!(o, Operand::Move(_) | Operand::Copy(_)))?;
        let t = cty(&self.body.tys, self.callable_place_ty(op));
        let ok = match t {
            CTy::Result(..) => 0,
            CTy::Option(_) => 1,
            _ => return None,
        };
        let (size, align) = c_size_align(self.p, &t);
        // A receiver that goes by pointer (`param_by_ptr`) is already the address of a spill
        // here: the call takes the normal path.
        if !(9..=16).contains(&size) || align >= 8 || ret_is_large(self.p, f) || param_by_ptr(self.p, &t) {
            return None;
        }
        let recv = &args[0];
        let disc = self.disc(&t, &format!("(&{recv})"));
        let payload = variant_field(self.p, &t, recv, ok, 0);
        let rest: String = args[1..].iter().map(|a| format!(", {a}")).collect();
        let callee = self.slots.callee(self.p, f);
        Some(format!("(__builtin_expect({disc} == {ok}, 1) ? {payload} : ({{ {} lust_uw = {recv}; {callee}(lust_uw{rest}); }}))", ctype(&t)))
    }

    fn rvalue(&mut self, rv: &Rvalue, loc: &str, post: &mut Vec<String>) -> String {
        match rv {
            Rvalue::Use(o) => self.operand(o, loc, post).0,
            Rvalue::Ref(_, pl) => {
                if let Some(a) = self.const_zst_addr(pl) {
                    let (e, t) = self.place(pl, loc);
                    return format!("({}(({} *){a}))", zst_checks(pl, &e), ctype(&t));
                }
                // Release C: taking an address needs no definition of the place's type.
                self.addr_only = true;
                let (e, t) = self.kplace(pl, loc);
                self.addr_only = false;
                // A slice place (a deref of a fat value, or a bare-slice
                // temporary from a range index) is already the fat value;
                // a place holding a slice reference takes an address as usual.
                // The C form cannot tell a `&[T]`/`&dyn` value from the
                // unsized place behind it, so ask the place's own type:
                // `&*r` for `r: &&dyn Tr` borrows the `&dyn` value.
                // An unsized newtype (`OsStr`, `Path`; W-SHIM) is laid out as
                // its slice field, so its place is a slice place too.
                let tys = &self.body.tys;
                let slice_like = |k: TyKind| match k {
                    TyKind::Slice(_) => true,
                    TyKind::Adt(d, _) => tys.unsized_field(d).is_some(),
                    _ => false,
                };
                let sem = self.place_sem_ty(pl).map(|ty| tys.kind(ty));
                let slice_place = matches!(t, CTy::Slice(_) | CTy::Unsized(..))
                    && match sem {
                        Some(k) => slice_like(k),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)) || slice_like(tys.kind(self.body.locals[pl.local as usize].ty)),
                    };
                let dyn_place = t == CTy::Dyn
                    && match sem {
                        Some(k) => matches!(k, TyKind::Dyn(..)),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)),
                    };
                // So is a `RefCell<dyn Tr>` place (cgen/own.rs).
                let cell_place = matches!(t, CTy::DynCell | CTy::DynLock(false))
                    && match self.place_sem_ty(pl) {
                        Some(ty) => crate::check::own::dyn_wrapped_elem(tys, ty).is_some(),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)),
                    };
                if t == CTy::Str || slice_place || dyn_place || cell_place { e } else { format!("(&{e})") }
            }
            Rvalue::SliceOf(pl) => {
                let (e, t) = self.kplace(pl, loc);
                if let (Some(a), CTy::Array(el, n)) = (self.const_zst_addr(pl), &t) {
                    return format!("({}(({}){{ ({} *){a}, {n} }}))", zst_checks(pl, &e), ctype(&CTy::Slice(el.clone())), ctype(el));
                }
                self.slice_of(&e, &t)
            }
            Rvalue::Subslice { base, lo, hi, inclusive, .. } => {
                let (e, t) = self.kplace(base, loc);
                // `ptr + lo` steps over elements: the element type by value.
                if let CTy::Array(el, _) | CTy::Slice(el) | CTy::Vec(el) = &t {
                    let el = (**el).clone();
                    self.note_held(&el);
                }
                let (ptr, len) = self.slice_ptr_len(&e, &t);
                let (lo_v, _) = self.operand(lo, loc, post);
                let ct = match &t {
                    CTy::Array(el, _) | CTy::Slice(el) | CTy::Vec(el) => ctype(&CTy::Slice(el.clone())),
                    _ => "lust_str".into(),
                };
                let (tmp, end) = (self.tmp(), self.tmp());
                let hi_v = match hi {
                    Some(h) => self.operand(h, loc, post).0,
                    None => len.clone(),
                };
                let incl = if *inclusive { 1 } else { 0 };
                // A str or String base slices to a str: the runtime
                // check also validates the char boundaries.
                let range_fn = if matches!(t, CTy::Str | CTy::String) { "lust_str_range" } else { "lust_slice_range" };
                let range_args = if range_fn == "lust_str_range" {
                    format!("{ptr}, {lo_v}, {hi_v}, {incl}, {len}, {loc}")
                } else {
                    format!("{lo_v}, {hi_v}, {incl}, {len}, {loc}")
                };
                let _ = writeln!(self.out, "    uint64_t {end} = {range_fn}({range_args});");
                let _ = writeln!(self.out, "    {ct} {tmp} = {{ {ptr} + {lo_v}, {end} - {lo_v} }};");
                tmp
            }
            Rvalue::Bin(op, a, b) => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                self.bin(*op, &a, &at, &b, &bt, loc)
            }
            Rvalue::Un(op, a) => {
                let (a, at) = self.operand(a, loc, post);
                match (op, &at) {
                    (UnOp::Neg, CTy::Float(_)) => format!("(-{a})"),
                    (UnOp::Neg, CTy::Int(i)) if !self.p.overflow_checks => {
                        if is128(*i) {
                            format!("lust_{}_sub((({}){{0, 0}}), {a})", int_fn(*i), int_c(*i))
                        } else {
                            format!("(({})(0ull - (uint64_t)({a})))", int_c(*i))
                        }
                    }
                    (UnOp::Neg, CTy::Int(i)) => format!("lust_neg_{}({a}, {loc})", int_fn(*i)),
                    (UnOp::Not, CTy::Bool) => format!("(!{a})"),
                    (UnOp::Not, CTy::Int(i)) if is128(*i) => format!("lust_{}_not({a})", int_fn(*i)),
                    (UnOp::Not, CTy::Int(i)) => format!("(({})~{a})", int_c(*i)),
                    _ => panic!("bad unary op"),
                }
            }
            Rvalue::Cast(o, to) => {
                let (a, from) = self.operand(o, loc, post);
                let to = cty(&self.body.tys, *to);
                // A fat raw pointer (tf-fatptr): to a fat one of the same
                // pointee it is a copy, to a thin one its address.
                if let CTy::FatPtr(_) = from {
                    return if matches!(to, CTy::FatPtr(_)) { a } else { format!("(({}){})", ctype(&to), ptr_addr(&a, &from)) };
                }
                // Casts to or from a 128-bit struct value are not C casts.
                match (&from, &to) {
                    // Float casts go through the runtime helpers so rounding
                    // and saturation match Rust exactly (src/runtime/float.h).
                    (CTy::Float(f), CTy::Float(g)) => {
                        if f == g {
                            a
                        } else if *f == FloatTy::F64 {
                            format!("lust_f64_to_f32({a})")
                        } else {
                            format!("lust_f32_to_f64({a})")
                        }
                    }
                    (CTy::Float(f), CTy::Int(ti)) if is128(*ti) => {
                        let t = self.tmp();
                        let _ = writeln!(self.out, "    {} {t}; lust_{}_to_{}({a}, &{t}.lo, &{t}.hi);", int_c(*ti), f.name(), int_fn(*ti));
                        t
                    }
                    (CTy::Float(f), CTy::Int(ti)) => format!("lust_{}_to_{}({a})", f.name(), int_fn(*ti)),
                    (CTy::Float(f), CTy::Char) => format!("((uint32_t)lust_{}_to_u32({a}))", f.name()),
                    (CTy::Int(fi), CTy::Float(g)) if is128(*fi) => {
                        format!("lust_{}_to_{}(({a}).lo, ({a}).hi)", int_fn(*fi), g.name())
                    }
                    (CTy::Int(fi), CTy::Float(g)) => {
                        if fi.signed() {
                            format!("lust_i64_to_{}((int64_t)({a}))", g.name())
                        } else {
                            format!("lust_u64_to_{}((uint64_t)({a}))", g.name())
                        }
                    }
                    (CTy::Bool | CTy::Char, CTy::Float(g)) => {
                        format!("lust_u64_to_{}((uint64_t)({a}))", g.name())
                    }
                    (CTy::Int(fi), CTy::Int(ti)) if is128(*fi) && is128(*ti) => {
                        if fi == ti {
                            a
                        } else {
                            format!("lust_{}_from_{}({a})", int_fn(*ti), int_fn(*fi))
                        }
                    }
                    (CTy::Int(fi), _) if is128(*fi) => format!("(({})(({a}).lo))", ctype(&to)),
                    (CTy::Adt(aid), CTy::Int(ti)) => {
                        // A fieldless enum cast to an integer gives its
                        // discriminant value. Layout types store the value
                        // in the tag, so read it back; legacy types store
                        // the variant index, so map index to value.
                        let adt = self.p.adt(*aid);
                        let ct = ctype(&to);
                        // A 16-byte tag is a two-word struct: a cast to a
                        // 128-bit int copies both words (the bit pattern
                        // is the discriminant), and a cast to a smaller
                        // int reads the low word.
                        let wide = match c_layout(self.p, &from) {
                            Some(l) if matches!(l.enum_tag, Some(EnumTag::Explicit { size, .. }) if size >= 16) => Some(if is128(*ti) {
                                format!("(({}){{({a}).u._tag.lo, ({a}).u._tag.hi}})", int_c(*ti))
                            } else {
                                format!("(({ct})(({a}).u._tag.lo))")
                            }),
                            _ => None,
                        };
                        let raw = match c_layout(self.p, &from) {
                            Some(l) => match l.enum_tag {
                                Some(EnumTag::Explicit { signed, .. }) => Some((format!("(({a}).u._tag)"), signed)),
                                _ => {
                                    let d = adt.variants.first().map_or(0, |v| v.disc);
                                    Some((disc_lit(d, 8, d < 0), d < 0))
                                }
                            },
                            None => None,
                        };
                        match (wide, raw) {
                            (Some(w), _) => w,
                            (None, Some((raw, raw_signed))) => {
                                if is128(*ti) {
                                    if raw_signed {
                                        format!("(({}){{(uint64_t)(int64_t)({raw}), (uint64_t)((int64_t)({raw}) >> 63)}})", int_c(*ti))
                                    } else {
                                        format!("(({}){{(uint64_t)({raw}), 0}})", int_c(*ti))
                                    }
                                } else {
                                    format!("(({ct})({raw}))")
                                }
                            }
                            (None, None) => {
                                let t = self.tmp();
                                let zero = if is128(*ti) { "{0, 0}" } else { "0" };
                                let _ = write!(self.out, "    {ct} {t} = {zero};\n    switch ({a}.tag) {{");
                                for (vi, v) in adt.variants.iter().enumerate() {
                                    let lit = if is128(*ti) {
                                        let bits = v.disc as u128;
                                        format!("(({ct}){{{}ULL, {}ULL}})", bits as u64, (bits >> 64) as u64)
                                    } else if v.disc < 0 {
                                        format!("(({ct})((int64_t){}))", v.disc)
                                    } else {
                                        format!("(({ct})((uint64_t){}ull))", v.disc as u128)
                                    };
                                    let _ = write!(self.out, " case {vi}: {t} = {lit}; break;");
                                }
                                let _ = writeln!(self.out, " }}");
                                t
                            }
                        }
                    }
                    (_, CTy::Int(ti)) if is128(*ti) => {
                        let signed = matches!(&from, CTy::Int(si) if si.signed());
                        if signed {
                            format!("(({}){{(uint64_t)(int64_t)({a}), (uint64_t)((int64_t)({a}) >> 63)}})", int_c(*ti))
                        } else {
                            format!("(({}){{(uint64_t)({a}), 0}})", int_c(*ti))
                        }
                    }
                    _ => format!("(({}){a})", ctype(&to)),
                }
            }
            Rvalue::Res(ty, is_ok, op) => {
                let t = cty(&self.body.tys, *ty);
                let (v, _) = self.operand(op, loc, post);
                self.make_variant(&t, (!*is_ok) as usize, &[v])
            }
            Rvalue::Opt(ty, op) => {
                let t = cty(&self.body.tys, *ty);
                match op {
                    Some(o) => {
                        let (v, _) = self.operand(o, loc, post);
                        // Release C: the payload of `Some(r)` with `r` a thin reference is never
                        // null, so a later niche check of this Option folds (`lust_ref_nn`). This
                        // runs only where the program builds the Some, and only for a plain local,
                        // which reading twice cannot change.
                        if names::release()
                            && let CTy::Option(inner) = &t
                            && matches!(**inner, CTy::Ref(_))
                            && ctype(inner).ends_with('*')
                            && v.starts_with('l')
                            && v[1..].bytes().all(|b| b.is_ascii_digit())
                            && v.len() > 1
                        {
                            let _ = writeln!(self.out, "    lust_ref_nn({v});");
                        }
                        self.make_variant(&t, 1, &[v])
                    }
                    None => self.make_variant(&t, 0, &[]),
                }
            }
            Rvalue::Aggregate(a, v, ops) => {
                let a = &self.p.tys.c_adt(*a);
                // A literal names the fields (`nested_block`).
                self.note_held(&CTy::Adt(*a));
                let adt = self.p.adt(*a);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if adt.is_enum {
                    self.make_variant(&CTy::Adt(*a), *v as usize, &vals)
                } else if vals.is_empty() {
                    zero_lit(self.p, &CTy::Adt(*a))
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("(({}){{ {} }})", names::adt(*a), fields.join(", "))
                }
            }
            Rvalue::VecLit(elem, ops) => {
                // `sizeof` and the element stores need the element type by value.
                let ec = cty(&self.body.tys, *elem);
                self.note_held(&ec);
                let et = ctype(&ec);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({}, sizeof({et}), _Alignof({et}));", ops.len());
                for (i, o) in ops.iter().enumerate() {
                    let (v, _) = self.operand(o, loc, post);
                    let _ = writeln!(self.out, "    (({et}*){t}.ptr)[{i}] = {v};");
                }
                let _ = writeln!(self.out, "    {t}.len = {};", ops.len());
                t
            }
            Rvalue::VecRepeat(elem, x, n) => {
                let ec = cty(&self.body.tys, *elem);
                let et = ctype(&ec);
                let (xv, _) = self.operand(x, loc, post);
                let (nv, _) = self.operand(n, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {xv};\n    uint64_t {i}_n = {nv};");
                // std's from_elem fast paths. A value that zeroed memory
                // reproduces (IsZero) takes calloc'd memory and no clones; a
                // zero-sized Copy value (`()`) only sets the length. Both
                // return at once for any n, as in Rust.
                let copy = is_copy_c(self.p, &ec);
                let zt = self.tmp();
                let zero = zero_test(self.p, &ec, &xt, &zt);
                if let Some(z) = &zero {
                    if z.contains(&zt) {
                        let _ = writeln!(self.out, "    static {et} {zt};");
                    }
                    let _ = writeln!(self.out, "    int32_t {zt}_z = {z};");
                    let _ = writeln!(
                        self.out,
                        "    lust_Vec {t} = {zt}_z ? lust_vec_with_capacity_zeroed({i}_n, sizeof({et}), _Alignof({et})) : lust_vec_with_capacity({i}_n, sizeof({et}), _Alignof({et}));"
                    );
                } else {
                    let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({i}_n, sizeof({et}), _Alignof({et}));");
                }
                // Unwind tables: a capacity overflow panic never returns. The frame still owns
                // the moved value (its drop flag clears at the end of the statement), so the
                // frame's cleanup drops it.
                if self.p.unwind && !self.p.unwind_tables {
                    // A capacity overflow panic returns here under panic=unwind:
                    // fill nothing, drop the value, and unwind.
                    let _ = writeln!(self.out, "    if ({} < {i}_n) {i}_n = 0;", vec_cap(&et, &format!("&{t}")));
                }
                let drop_x = if needs_drop_c(self.p, &ec) {
                    self.want(Glue::Drop, &ec);
                    format!(" drop_{}(&{xt});", mangle(&ec))
                } else {
                    String::new()
                };
                let fast = match (&zero, copy) {
                    (Some(_), true) => format!("{zt}_z || sizeof({et}) == 0"),
                    (Some(_), false) => format!("{zt}_z"),
                    (None, true) => format!("sizeof({et}) == 0"),
                    (None, false) => String::new(),
                };
                if !fast.is_empty() {
                    let _ = writeln!(self.out, "    if ({fast}) {{{drop_x} }} else");
                }
                if copy {
                    // u8 and i8 fill with memset in std; any one-byte Copy
                    // value gives the same bytes.
                    let _ = writeln!(
                        self.out,
                        "    if (sizeof({et}) == 1) memset({t}.ptr, *(uint8_t *)&{xt}, {i}_n);\n    else for (uint64_t {i} = 0; {i} < {i}_n; {i}++) (({et}*){t}.ptr)[{i}] = {xt};"
                    );
                } else {
                    self.want(Glue::Clone, &ec);
                    // Clone n-1 times, then move the original into the last slot (as Rust does).
                    let _ = writeln!(
                        self.out,
                        "    {{ for (uint64_t {i} = 0; {i} + 1 < {i}_n; {i}++) (({et}*){t}.ptr)[{i}] = clone_{}(&{xt});",
                        mangle(&ec)
                    );
                    let _ = writeln!(self.out, "    if ({i}_n) (({et}*){t}.ptr)[{i}_n - 1] = {xt}; else{} }}", if drop_x.is_empty() { " {}" } else { &drop_x });
                }
                let _ = writeln!(self.out, "    {t}.len = {i}_n;");
                t
            }
            Rvalue::Eq { a, b, ty, ne } => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                // A slice operand is already the fat value (not a pointer to
                // it), so take its address for the glue call.
                let a = if matches!(at, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{a})") } else { a };
                let b = if matches!(bt, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{b})") } else { b };
                let t = cty(&self.body.tys, *ty);
                let e = self.eq_expr(&t, &a, &b);
                if *ne { format!("(!{e})") } else { e }
            }
            Rvalue::Cmp { op, a, b, ty } => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                let a = if matches!(at, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{a})") } else { a };
                let b = if matches!(bt, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{b})") } else { b };
                let t = cty(&self.body.tys, *ty);
                self.want(Glue::Cmp, &t);
                let c = format!("cmp_{}({a}, {b})", mangle(&t));
                // The code is -1, 0, 1, or 2 (unordered): every
                // operator is false on 2, as in `PartialOrd`.
                match op {
                    BinOp::Lt => format!("({c} == -1)"),
                    BinOp::Gt => format!("({c} == 1)"),
                    BinOp::Le => format!("((uint8_t)({c} + 1) <= 1)"),
                    _ => format!("((uint8_t){c} <= 1)"),
                }
            }
            Rvalue::StrCmp(op, a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                match op {
                    BinOp::Eq => format!("lust_str_eq({a}, {b})"),
                    BinOp::Ne => format!("(!lust_str_eq({a}, {b}))"),
                    _ => format!("(lust_str_cmp({a}, {b}) {} 0)", op.symbol()),
                }
            }
            Rvalue::StringAdd(a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_String {t} = {a};\n    lust_string_push_str(&{t}, {b});");
                t
            }
            Rvalue::TupleAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() {
                    zero_lit(self.p, &t)
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("(({ct}){{ {} }})", fields.join(", "))
                }
            }
            Rvalue::ArrayAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() { zero_lit(self.p, &t) } else { format!("(({ct}){{ .v = {{ {} }} }})", vals.join(", ")) }
            }
            Rvalue::ArrayRepeat(ty, o, n) => {
                let at = cty(&self.body.tys, *ty);
                let ct = ctype(&at);
                let et = match &at {
                    CTy::Array(e, _) => ctype(e),
                    _ => "uint8_t".into(),
                };
                let (v, _) = self.operand(o, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {v};\n    {ct} {t};");
                // A zero-sized element has nothing to copy (`[(); usize::MAX]`).
                let _ = writeln!(self.out, "    if (sizeof({et})) for (uint64_t {i} = 0; {i} < {n}; {i}++) {t}.v[{i}] = {xt};");
                t
            }
            Rvalue::Format(parts) => self.format(parts, loc, post, 0),
            Rvalue::WriteFmt(dst, parts, stream) => self.write_fmt(dst, parts, *stream, loc, post),
            Rvalue::FormatArgs(env, parts) => self.format_args_value(env.as_ref(), parts, loc, post),
            Rvalue::Discriminant(pl) => {
                let (e, t) = self.place(pl, loc);
                self.disc(&t, &format!("(&{e})"))
            }
            Rvalue::StaticLoad(idx) => static_sym(self.p, *idx),
            Rvalue::StaticRef(idx) => format!("(&{})", static_sym(self.p, *idx)),
            Rvalue::LenOf(pl) => {
                let (e, t) = self.place(pl, loc);
                match &t {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) | CTy::Vec(_) | CTy::String | CTy::Str => format!("{e}.len"),
                    CTy::Ref(inner) if **inner == CTy::Str => format!("{e}.len"),
                    _ => format!("({e})->len"),
                }
            }
            Rvalue::FnValue(f, ty) => {
                let t = cty(&self.body.tys, *ty);
                match t {
                    CTy::FnPtr(..) => {
                        self.note_callee(*f);
                        self.note_held(&t);
                        format!("(({}){})", ctype(&t), self.slots.fn_value(self.p, *f))
                    }
                    // A bare fn item value is a zero-sized type.
                    CTy::Unit => "((lust_Unit){})".into(),
                    _ => "0".into(),
                }
            }
            Rvalue::ItemShim(item, ty) => {
                let t = cty(&self.body.tys, *ty);
                self.note_fn_sig(&t);
                let name = match self.body.tys.kind(*item) {
                    TyKind::FnDef(def, _) if def == crate::ty::prim_fn_def() => self.prim_shim(*item, *ty, &t),
                    _ => self.item_shim(*item, &t),
                };
                format!("(({}){name})", ctype(&t))
            }
            Rvalue::MakeDyn { ptr, src, dyn_ty } => {
                let (v, ct) = self.operand(ptr, loc, post);
                // An Rc or Arc points the fat value at its value, after the counts.
                let at_value = matches!(ct, CTy::Rc(_) | CTy::Sync(crate::ty::sync::SyncTy::Arc, _));
                // That (and a Weak's) `->v` needs the count block defined.
                if at_value || matches!(ct, CTy::Weak(_) | CTy::Sync(crate::ty::sync::SyncTy::ArcWeak, _)) {
                    collect_types(&ct, &mut self.sig_types);
                }
                // `Box<[T; N]>`, `Rc<[T; N]>`, or `Arc<[T; N]>` to the
                // `[T]` form: the element pointer and the constant length.
                if let TyKind::Slice(e) = self.body.tys.kind(*dyn_ty) {
                    let n = match cty(&self.body.tys, *src) {
                        CTy::Array(_, n) => n,
                        other => unreachable!("an owning slice from {other:?}"),
                    };
                    let sl = CTy::Slice(Box::new(cty(&self.body.tys, e)));
                    self.note_held(&sl);
                    let (st, et) = (ctype(&sl), ctype(&cty(&self.body.tys, e)));
                    let data = if at_value { format!("&({v})->v") } else { format!("({v})") };
                    return format!("(({st}){{ ({et}*)({data}), {n} }})");
                }
                let vid = crate::check::generics::vtable_for(self.p, &self.body.tys, *src, *dyn_ty)
                    .expect("mono builds a vtable for every unsizing coercion in a concrete body");
                let vt = self.vtable_sym(vid);
                // An `Rc<T>` source points the data at the value in its
                // allocation (`Rc<dyn Tr>` finds the counts before it);
                // a `Weak<T>` too, unless it dangles (`Weak::new()`).
                let data = match ct {
                    _ if at_value => format!("&({v})->v"),
                    CTy::Weak(_) | CTy::Sync(crate::ty::sync::SyncTy::ArcWeak, _) => {
                        format!("(({v}) == (void *)~(uintptr_t)0 ? (void *)~(uintptr_t)0 : (void *)&({v})->v)")
                    }
                    _ => format!("({v})"),
                };
                format!("((lust_dyn){{ (void *){data}, {vt} }})")
            }
            Rvalue::DynUpcast { ptr, path } => {
                let (v, _) = self.operand(ptr, loc, post);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_dyn {t} = {v};");
                for k in path {
                    let _ = writeln!(self.out, "    {t}.vt = (const void *const *){t}.vt[{k}];");
                }
                t
            }
            Rvalue::DynMeta { ptr, word } => {
                let (v, _) = self.operand(ptr, loc, post);
                format!("((uint64_t)(uintptr_t)({v}).vt[{word}])")
            }
            Rvalue::DynData { ptr, ty } => {
                let (v, _) = self.operand(ptr, loc, post);
                let ct = cty(&self.body.tys, *ty);
                match &ct {
                    // An `Rc<T>` or `Arc<T>` points at its allocation, the
                    // counts first.
                    CTy::Rc(e) | CTy::Sync(crate::ty::sync::SyncTy::Arc, e) => {
                        collect_types(&ct, &mut self.sig_types);
                        let rc = format!("RcI_{}", mangle(e));
                        format!("(({rc} *)((char *)({v}).data - __builtin_offsetof({rc}, v)))")
                    }
                    _ => format!("(({})({v}).data)", ctype(&ct)),
                }
            }
        }
    }

    /// The semantic type of a place, through derefs, fields, variants,
    /// and indexes. None for a projection this walk does not follow.
    fn place_sem_ty(&self, pl: &Place) -> Option<Ty> {
        let tys = &self.body.tys;
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant = 0usize;
        for pr in &pl.proj {
            t = match (tys.kind(t), pr) {
                (TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner), Proj::Deref) => inner,
                (TyKind::Adt(..), Proj::Deref) => tys.boxed_elem(t)?,
                // A closure env is the tuple of its captures (`cty`).
                (TyKind::Closure(_, a), Proj::Field(i)) => tys.args(a).iter().filter_map(|g| g.as_ty()).nth(*i as usize)?,
                (_, Proj::Downcast(v)) => {
                    variant = *v as usize;
                    continue;
                }
                (TyKind::Tuple(ts), Proj::Field(i)) => *tys.tys_of(ts).get(*i as usize)?,
                (TyKind::Adt(..), Proj::Field(i)) => match tys.local_adt(t) {
                    Some(a) => self.p.adt(a).variants.get(variant)?.fields.get(*i as usize)?.ty,
                    None => tys.option_elem(t)?,
                },
                (TyKind::Array(e, _) | TyKind::Slice(e), Proj::Index(_)) => e,
                (_, Proj::Index(_)) => tys.vec_elem(t)?,
                _ => return None,
            };
            variant = 0;
        }
        Some(t)
    }

    /// The C name of vtable `vid` in this function, emitting it (and the
    /// super vtables it points at) into the prelude on first use. See
    /// `check::object` for the word layout.
    fn vtable_sym(&mut self, vid: u32) -> String {
        if let Some(s) = self.vtables.get(&vid) {
            return s.clone();
        }
        let p = self.p;
        let vt = p.gx.vtables[vid as usize].clone();
        let supers: Vec<String> = vt.supers.iter().map(|&s| self.vtable_sym(s)).collect();
        let fslot = self.slots.of(self.body.fn_id);
        // Release C counts this fn's vtables: `vid` is a program-wide counter.
        let name = if names::release() { format!("vt{}_{}", names::fn_tag(fslot), self.vtables.len()) } else { format!("vt{fslot}_{vid}") };
        let ct = cty(&p.tys, vt.self_ty);
        let drop = if needs_drop_c(p, &ct) {
            self.want(Glue::Drop, &ct);
            format!("(void *)drop_{}", mangle(&ct))
        } else {
            "0".to_string()
        };
        let (size, align) = match layout::layout_of_ty(&p.tys, p, vt.self_ty) {
            Ok(l) => (l.size, l.align),
            Err(()) => c_size_align(p, &ct),
        };
        let mut words = vec![drop, format!("(void *)(uintptr_t){size}"), format!("(void *)(uintptr_t){align}")];
        // The fmt header shims (`VT_FMT_DEBUG`, `VT_FMT_DISPLAY` in
        // check/object.rs): the concrete type's fmt glue behind a
        // principal with that supertrait, else 0.
        let info = p.gx.dyn_infos.get(&vt.principal.def);
        for (has, kind) in
            [(info.is_some_and(|i| i.fmt_debug), FmtKind::Debug), (info.is_some_and(|i| i.fmt_display), FmtKind::Display)]
        {
            if has {
                let shim = self.vt_fmt_shim(&name, &ct, kind);
                words.push(format!("(void *){shim}"));
            } else {
                words.push("0".to_string());
            }
        }
        words.extend(supers.iter().map(|s| format!("(void *){s}")));
        // A `dyn Any` vtable holds the value's type id (`object::VT_ANY_ID`).
        if vt.principal.def == p.gx.lang.any {
            let (lo, hi) = crate::check::any::type_id_words(p, &p.tys, vt.self_ty);
            words.extend([format!("(void *)(uintptr_t){lo}ull"), format!("(void *)(uintptr_t){hi}ull")]);
        }
        // A `dyn FnOnce` vtable's call entry consumes the value and
        // frees the box it lives in (ARCH 2.9): the only call is
        // through `Box<dyn FnOnce>` by value.
        let consume = (vt.principal.def == p.gx.lang.fn_once).then_some(vt.self_ty);
        if matches!(p.tys.kind(vt.self_ty), TyKind::FnDef(..) | TyKind::FnPtr(_)) {
            // A fn item or fn pointer as a `dyn Fn` value: no env.
            let shim = self.fn_value_shim(&name, &vt, consume.is_some());
            words.push(format!("(void *){shim}"));
        } else if let TyKind::Ref(_, _, inner) = p.tys.kind(vt.self_ty)
            && p.gx.lang.is_fn_family(vt.principal.def)
            && matches!(p.tys.kind(inner), TyKind::Dyn(..))
        {
            let shim = self.dyn_ref_shim(&name, inner);
            words.push(format!("(void *){shim}"));
        } else {
            // `&C` / `&mut C` of a closure: the data pointer points at
            // the reference, so the entry loads it first.
            let through_ref = p.gx.lang.is_fn_family(vt.principal.def)
                && matches!(p.tys.kind(vt.self_ty), TyKind::Ref(_, _, inner) if matches!(p.tys.kind(inner), TyKind::Closure(..)));
            for (j, &f) in vt.methods.iter().enumerate() {
                let shim = self.vtable_shim(&name, j, f, consume, through_ref);
                words.push(format!("(void *){shim}"));
            }
        }
        let tn = crate::check::object::trait_name(p, vt.principal.def);
        let _ = writeln!(self.prelude, "/* vtable: {} as {tn} */", ty_name(p, &p.tys, vt.self_ty));
        let _ = writeln!(self.prelude, "static const void *const {name}[] = {{ {} }};", words.join(", "));
        self.vtables.insert(vid, name.clone());
        name
    }

    /// One fmt header shim: formats the erased value with the concrete
    /// type's own Debug or Display glue (`fmt_expr` on its C type), in
    /// the `int (void *self, lust_Formatter *f)` shape the fmt glue
    /// calls through `VT_FMT_DEBUG` / `VT_FMT_DISPLAY`.
    fn vt_fmt_shim(&mut self, vt_name: &str, ct: &CTy, kind: FmtKind) -> String {
        let name = format!("{vt_name}_fmt{}", if kind == FmtKind::Debug { "D" } else { "S" });
        self.note_held(ct);
        self.note_fmt_opens(ct, kind);
        let v = format!("(({ }*)self)", ctype(ct));
        let e = fmt::fmt_expr(ct, kind, "f", &v, &mut |g, t| self.want(g, t));
        let _ = writeln!(self.prelude, "static int {name}(void *self, lust_Formatter *f) {{ return {e}; }}");
        name
    }

    /// The call entry of a `dyn Fn` vtable whose value is a fn item (a
    /// zero-sized value: the shim calls the fn through `lust_fns[slot]`,
    /// ignoring the data pointer) or a fn pointer (the shim calls the
    /// pointer stored at the data pointer). With `consume` (a `dyn
    /// FnOnce`) the shim then frees the box.
    fn fn_value_shim(&mut self, vt_name: &str, vt: &crate::check::object::VtableData, consume: bool) -> String {
        let p = self.p;
        let name = format!("{vt_name}_m0");
        let ct = cty(&p.tys, vt.self_ty);
        let cts = ctype(&ct);
        let (params, ret, call) = match (p.tys.kind(vt.self_ty), &ct) {
            (TyKind::FnPtr(_), CTy::FnPtr(ps, r)) => {
                self.note_fn_sig(&ct);
                (ps.clone(), (**r).clone(), format!("(*({cts}*)self)"))
            }
            _ => {
                let Some(&f) = vt.methods.first() else { return "0".to_string() };
                self.note_callee(f);
                let info = p.fn_info(f);
                let params: Vec<CTy> = info.params.iter().map(|&t| cty(&p.tys, t)).collect();
                for t in &params {
                    self.note_held(t);
                }
                let call = self.slots.callee(p, f);
                (params, cty(&p.tys, info.ret), call)
            }
        };
        self.note_held(&ret);
        let rt = ctype(&ret);
        let decls: String = params.iter().enumerate().map(|(i, t)| format!(", {} a{i}", param_ctype(p, t))).collect();
        let names: Vec<String> = (0..params.len()).map(|i| format!("a{i}")).collect();
        let free = if consume { format!(" lust_dealloc(self, sizeof({cts}), _Alignof({cts}));") } else { String::new() };
        if ret_by_out(p, &ret) {
            let args: String = std::iter::once("out".to_string()).chain(names).collect::<Vec<_>>().join(", ");
            let _ = writeln!(self.prelude, "static void {name}({rt} *out, void *self{decls}) {{ {call}({args});{free} }}");
        } else {
            let args = names.join(", ");
            let _ = writeln!(self.prelude, "static {rt} {name}(void *self{decls}) {{ {rt} r = {call}({args});{free} (void)self; return r; }}");
        }
        name
    }

    /// The call entry of a `dyn Fn` vtable whose value is a reference to
    /// another `dyn Fn`/`FnMut` object (`&mut dyn FnMut(A) -> R`): the data
    /// pointer points at that fat reference, so the shim loads it and
    /// calls the inner object's call entry (`VT_HEADER`, as every dyn Fn
    /// call does) with the same arguments.
    fn dyn_ref_shim(&mut self, vt_name: &str, inner: Ty) -> String {
        let p = self.p;
        let name = format!("{vt_name}_m0");
        let lang = p.gx.lang;
        let Some(pr) = crate::check::object::principal_of(&p.tys, inner) else { return "0".to_string() };
        let ins: Vec<Ty> = match p.tys.args(pr.args).get(1).and_then(|g| g.as_ty()).map(|t| p.tys.kind(t)) {
            Some(TyKind::Tuple(ts)) => p.tys.tys_of(ts).to_vec(),
            _ => Vec::new(),
        };
        let out_def = lang.output_of(lang.fn_once);
        let out = p.tys.bindings(pr.bindings).iter().find(|(d, _)| Some(*d) == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
        let ret = cty(&p.tys, out);
        self.note_held(&ret);
        let params: Vec<CTy> = ins.iter().map(|&t| cty(&p.tys, t)).filter(|t| !param_dropped(p, t)).collect();
        for t in &params {
            self.note_held(t);
        }
        let rt = ctype(&ret);
        let decls: String = params.iter().enumerate().map(|(i, t)| format!(", {} a{i}", param_ctype(p, t))).collect();
        let tys: String = params.iter().map(|t| format!(", {}", param_ctype(p, t))).collect();
        let args: String = (0..params.len()).map(|i| format!(", a{i}")).collect();
        let k = crate::check::object::VT_HEADER;
        let load = "lust_dyn d = *(lust_dyn *)self;";
        if ret_by_out(p, &ret) {
            let _ = writeln!(
                self.prelude,
                "static void {name}({rt} *out, void *self{decls}) {{ {load} ((void (*)({rt} *, void *{tys}))(d.vt[{k}]))(out, d.data{args}); }}"
            );
        } else {
            let _ = writeln!(
                self.prelude,
                "static {rt} {name}(void *self{decls}) {{ {load} return (({rt} (*)(void *{tys}))(d.vt[{k}]))(d.data{args}); }}"
            );
        }
        name
    }

    /// One vtable method entry: a shim that takes the erased receiver and
    /// forwards through `lust_fns[slot]`, so the entry never names a body
    /// an overlay could replace (ARCH 4.5). Its C signature is the
    /// method's with `void *` for the receiver; dyn call sites cast the
    /// entry to that shape. With `consume` (the concrete type of a `dyn
    /// FnOnce` vtable) the shim takes the value out of the box (an
    /// `FnOnce` closure's by-value env) or drops it after the call (an
    /// `Fn`/`FnMut` closure's), then frees the box. With `through_ref`
    /// (the concrete type is a reference to the closure) the receiver
    /// is the pointer stored at the data pointer.
    fn vtable_shim(&mut self, vt_name: &str, j: usize, f: LocalDefId, consume: Option<Ty>, through_ref: bool) -> String {
        self.note_callee(f);
        let p = self.p;
        let info = p.fn_info(f);
        for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
            self.note_held(&cty(&p.tys, t));
        }
        let name = format!("{vt_name}_m{j}");
        let ret = ctype(&cty(&p.tys, info.ret));
        // `(CAST lust_fns[slot])`, or `(CAST f_<id>)` in release C (`names::callee`).
        let target = self.slots.callee(p, f);
        let recv = ctype(&cty(&p.tys, info.params[0]));
        let recv_dropped = param_dropped(p, &cty(&p.tys, info.params[0]));
        let mut decls: Vec<String> = Vec::new();
        let mut rest: Vec<String> = Vec::new();
        for (i, &t) in info.params.iter().enumerate().skip(1) {
            if param_dropped(p, &cty(&p.tys, t)) {
                continue;
            }
            decls.push(format!("{} a{i}", param_ctype(p, &cty(&p.tys, t))));
            rest.push(format!("a{i}"));
        }
        let decls = decls.iter().map(|d| format!(", {d}")).collect::<String>();
        if let Some(self_ty) = consume {
            let ct = cty(&p.tys, self_ty);
            let cts = ctype(&ct);
            let by_value = !matches!(p.tys.kind(info.params[0]), TyKind::Ref(..));
            // An over-aligned env goes by pointer (`param_by_ptr`): the body
            // copies it out of the box before the shim frees the box.
            let env = if by_value && param_by_ptr(p, &cty(&p.tys, info.params[0])) {
                format!("({cts}*)self")
            } else if by_value {
                format!("*({cts}*)self")
            } else {
                format!("({recv})self")
            };
            let drop = if !by_value && needs_drop_c(p, &ct) {
                self.want(Glue::Drop, &ct);
                format!("drop_{}(({cts}*)self); ", mangle(&ct))
            } else {
                String::new()
            };
            let free = format!("lust_dealloc(self, sizeof({cts}), _Alignof({cts}));");
            let mut call: Vec<String> = Vec::new();
            if !recv_dropped {
                call.push(env);
            }
            call.extend(rest.iter().cloned());
            let call = call.join(", ");
            if ret_is_large(p, f) {
                let rest = if call.is_empty() { String::new() } else { format!(", {call}") };
                let _ = writeln!(
                    self.prelude,
                    "static void {name}({ret} *out, void *self{decls}) {{ {target}(out{rest}); {drop}{free} }}"
                );
            } else {
                let _ = writeln!(
                    self.prelude,
                    "static {ret} {name}(void *self{decls}) {{ {ret} r = {target}({call}); {drop}{free} return r; }}"
                );
            }
            return name;
        }
        let mut names: Vec<String> = Vec::new();
        if !recv_dropped {
            names.push(if through_ref { format!("({recv})*(void **)self") } else { format!("({recv})self") });
        }
        names.extend(rest);
        let names = names.join(", ");
        if ret_is_large(p, f) {
            let rest = if names.is_empty() { String::new() } else { format!(", {names}") };
            let _ = writeln!(
                self.prelude,
                "static void {name}({ret} *out, void *self{decls}) {{ {target}(out{rest}); }}"
            );
        } else {
            let _ = writeln!(
                self.prelude,
                "static {ret} {name}(void *self{decls}) {{ return {target}({names}); }}"
            );
        }
        name
    }

    fn bin(&mut self, op: BinOp, a: &str, at: &CTy, b: &str, bt: &CTy, loc: &str) -> String {
        use BinOp::*;
        // 128-bit values are C structs: no C operators apply, so every
        // operation is a runtime helper call.
        if let CTy::Int(i) = at
            && is128(*i)
        {
            let f = int_fn(*i);
            if op.is_cmp() {
                return format!("(lust_{f}_cmp({a}, {b}) {} 0)", op.symbol());
            }
            let checks = self.p.overflow_checks;
            return match op {
                // Overflow checks off: + - * wrap and shift amounts are masked,
                // as rustc's release builds do (`Program::overflow_checks`).
                Add | Sub | Mul if !checks => {
                    let how = match op {
                        Add => "add",
                        Sub => "sub",
                        _ => "mul",
                    };
                    format!("lust_{f}_{how}({a}, {b})")
                }
                Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                BitAnd => format!("lust_{f}_and({a}, {b})"),
                BitOr => format!("lust_{f}_or({a}, {b})"),
                BitXor => format!("lust_{f}_xor({a}, {b})"),
                Shl | Shr => {
                    let amount = match bt {
                        CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
                        CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                        _ => format!("(uint64_t)({b})"),
                    };
                    let dir = if op == Shl { "left" } else { "right" };
                    let sh = if checks { format!("lust_shift_amount({amount}, 128, \"{dir}\", {loc})") } else { format!("((uint32_t)({amount} & 127u))") };
                    let how = if op == Shl { "shl" } else { "shr" };
                    format!("lust_{f}_{how}({a}, {sh})")
                }
                _ => unreachable!(),
            };
        }
        if op.is_cmp() {
            return format!("({a} {} {b})", op.symbol());
        }
        match at {
            CTy::Float(f) => {
                if op == Rem {
                    format!("lust_fmod_{}({a}, {b})", f.name())
                } else {
                    format!("(({})({a} {} {b}))", ctype(&CTy::Float(*f)), op.symbol())
                }
            }
            CTy::Bool => format!("((uint8_t)({a} {} {b}))", op.symbol()),
            CTy::Int(i) => {
                let (c, f) = (int_c(*i), int_fn(*i));
                let checks = self.p.overflow_checks;
                match op {
                    // Overflow checks off: wrapping math in uint64_t (no C signed
                    // overflow), truncated to the type by the cast.
                    Add | Sub | Mul if !checks => format!("(({c})((uint64_t)({a}) {} (uint64_t)({b})))", op.symbol()),
                    Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                    Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                    Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                    Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                    Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                    BitAnd | BitOr | BitXor => format!("(({c})({a} {} {b}))", op.symbol()),
                    Shl | Shr => {
                        let amount = match bt {
                            CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
                            CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                            _ => format!("(uint64_t)({b})"),
                        };
                        let dir = if op == Shl { "left" } else { "right" };
                        let sh = if checks {
                            format!("lust_shift_amount({amount}, {}, \"{dir}\", {loc})", i.bits())
                        } else {
                            format!("((uint32_t)({amount} & {}u))", i.bits() - 1)
                        };
                        if op == Shl { format!("(({c})((uint64_t)({a}) << {sh}))") } else { format!("(({c})({a} >> {sh}))") }
                    }
                    _ => unreachable!(),
                }
            }
            _ => panic!("bad binary operand type"),
        }
    }

    /// `a` and `b` are pointers to values of type `t`.
    /// The data pointer and length C expressions of an array, Vec, or slice place.
    fn slice_ptr_len(&self, e: &str, t: &CTy) -> (String, String) {
        match t {
            CTy::Array(_, n) => (format!("{e}.v"), n.to_string()),
            CTy::Vec(el) => (format!("(({}*){e}.ptr)", ctype(el)), format!("{e}.len")),
            CTy::Slice(_) | CTy::Str | CTy::String => (format!("{e}.ptr"), format!("{e}.len")),
            _ => (format!("(({e}))"), "0".into()),
        }
    }

    /// A fat slice value over the whole of an array, Vec, or slice place.
    /// The address of a zero-sized constant (a promoted temp or a byte
    /// string temp, or a place inside one): rustc gives it no storage, so
    /// its address is its alignment (`{:p}` of `&()` prints 0x1, of
    /// `&[0u64; 0]` 0x8). None for any other place.
    fn const_zst_addr(&self, pl: &Place) -> Option<String> {
        let i = pl.local as usize;
        let is_const = self.body.promoted.contains(&pl.local) || self.byte_blobs.get(i).is_some_and(|b| b.is_some());
        if !is_const || pl.proj.iter().any(|pr| matches!(pr, Proj::Deref)) {
            return None;
        }
        let (size, align) = c_size_align(self.p, &self.local_cty[i]);
        (size == 0).then(|| format!("(void *)(uintptr_t){}", align.max(1)))
    }

    fn slice_of(&mut self, e: &str, t: &CTy) -> String {
        match t {
            CTy::Slice(_) => e.to_string(),
            CTy::Array(el, _) | CTy::Vec(el) => {
                let ct = ctype(&CTy::Slice(el.clone()));
                let (ptr, len) = self.slice_ptr_len(e, t);
                format!("(({ct}){{ {ptr}, {len} }})")
            }
            _ => e.to_string(),
        }
    }

    /// The callable argument of a builtin whose C adapter calls it (a sort
    /// comparator or key, a `binary_search_by` probe, a `retain`
    /// predicate, a `bool::then` fn): a closure, a fn item or a fn
    /// pointer, or a reference to a `dyn Fn`/`FnMut` (`sync::Callee`), behind
    /// `.1` references or boxes. Its value's C type is `.2`.
    fn adapter_callee(&self, o: &Operand) -> (sync::Callee, u8, CTy) {
        let mut t = self.callable_place_ty(o);
        let mut derefs = 0;
        loop {
            t = match self.body.tys.kind(t) {
                // A reference to a `dyn Fn*` is the callee (`Callee::DynRef`).
                TyKind::Ref(_, _, i) if matches!(self.body.tys.kind(i), TyKind::Dyn(..)) => break,
                TyKind::Ref(_, _, i) => i,
                _ if let Some(i) = self.body.tys.boxed_elem(t) => i,
                _ => break,
            };
            derefs += 1;
        }
        (self.callee_of_ty(t), derefs, cty(&self.body.tys, t))
    }

    /// The C return type of an `adapter_callee`.
    fn adapter_callee_ret(&self, c: &(sync::Callee, u8, CTy)) -> CTy {
        self.callee_ret(&c.0)
    }

    /// A call of an `adapter_callee` whose value (or the first of its
    /// references) is at pointer expression `at`, into a fresh variable
    /// of its return type (written to `out`).
    fn adapter_call_c(&mut self, out: &mut String, c: &(sync::Callee, u8, CTy), at: &str, args: &[String]) -> (String, CTy) {
        let mut at = at.to_string();
        for _ in 0..c.1 {
            at = format!("(*(void**){at})");
        }
        self.note_held(&c.2);
        let value = format!("(*({}*){at})", ctype(&c.2));
        (self.callee_call_c(out, &c.0, &value, args), self.adapter_callee_ret(c))
    }

    /// A call of closure body `f` on the env pointer `env` and the
    /// argument expressions, into a fresh variable of its return type
    /// (written to `out`): the large-return form takes `&var` first.
    fn closure_call_c(&mut self, out: &mut String, f: LocalDefId, env: &str, args: &[String]) -> (String, CTy) {
        let mut all: Vec<String> = vec![env.to_string()];
        all.extend(args.iter().cloned());
        self.fn_call_c(out, f, &all)
    }

    /// Replaces each argument in `args` whose parameter type in `params`
    /// goes by pointer (`param_by_ptr`) with the address of a fresh copy
    /// declared in `out`. The callee copies the value again on entry, so
    /// the copy only has to live until the call returns.
    fn spill_by_ptr(&mut self, out: &mut String, params: &[CTy], args: &mut [String]) {
        for (t, a) in params.iter().zip(args.iter_mut()) {
            if param_by_ptr(self.p, t) && !param_dropped(self.p, t) {
                let v = self.tmp();
                let _ = writeln!(out, "    {} {v} = {a};", ctype(t));
                *a = format!("&{v}");
            }
        }
    }

    /// C statements (into `out`) calling fn `f` through its slot with
    /// C argument values `args` (all of its params, in order); returns
    /// the result temp and its C type. `closure_call_c` passes a closure
    /// body's env first.
    fn fn_call_c(&mut self, out: &mut String, f: LocalDefId, args: &[String]) -> (String, CTy) {
        let rt = cty(&self.p.tys, self.p.fn_info(f).ret);
        self.note_held(&rt);
        for &t in &self.p.fn_info(f).params {
            self.note_held(&cty(&self.p.tys, t));
        }
        let v = self.tmp();
        // The LLVM backend calls the fn's internal ABI entry (cgen/ll.rs).
        if ll::on(self.p) {
            let saved = std::mem::take(&mut self.out);
            let e = self.ll_fn_call(f, args, "0");
            let pre = std::mem::replace(&mut self.out, saved);
            out.push_str(&pre);
            let _ = writeln!(out, "  {} {v} = {e};", ctype(&rt));
            return (v, rt);
        }
        let call = self.slots.callee(self.p, f);
        // A dropped parameter (a zero-sized env taken by value, or a
        // zero-sized argument) is not in the C signature, so it is
        // not passed here either (see `param_dropped`).
        let mut all: Vec<String> = args.to_vec();
        let pts: Vec<CTy> = self.p.fn_info(f).params.iter().map(|&t| cty(&self.p.tys, t)).collect();
        self.spill_by_ptr(out, &pts, &mut all);
        let dropped: Vec<bool> = self.p.fn_info(f).params.iter().map(|&t| param_dropped(self.p, &cty(&self.p.tys, t))).collect();
        let mut i = 0;
        all.retain(|_| {
            let keep = !dropped.get(i).copied().unwrap_or(false);
            i += 1;
            keep
        });
        if ret_is_large(self.p, f) {
            let rest: String = all.iter().map(|a| format!(", {a}")).collect();
            let _ = writeln!(out, "  {} {v}; {call}(&{v}{rest});", ctype(&rt));
        } else {
            let _ = writeln!(out, "  {} {v} = {call}({});", ctype(&rt), all.join(", "));
        }
        (v, rt)
    }

    /// C statements (into `out`) comparing the values at pointer
    /// expressions `a` and `b` of an Ord type lust compares
    /// (check/collect.rs `has_total_ord`); returns the name of an int32_t
    /// that is negative, zero, or positive like `Ord::cmp`. With
    /// `partial`, the comparison is `PartialOrd::partial_cmp` (the
    /// sort adapters: std's sort compares with `lt`); the code 2
    /// (unordered) can then also reach the caller, whose `< 0` test
    /// is `lt`.
    fn cmp3_c(&mut self, out: &mut String, t: &CTy, a: &str, b: &str, partial: bool) -> String {
        if let CTy::Ref(inner) = t
            && **inner != CTy::Str
        {
            return self.cmp3_c(out, inner, &format!("(*{a})"), &format!("(*{b})"), partial);
        }
        let v = self.tmp();
        match t {
            CTy::Unit => {
                let _ = writeln!(out, "  int32_t {v} = 0;");
            }
            CTy::Int(i) if is128(*i) => {
                let f = if i.signed() { "lust_i128_cmp" } else { "lust_u128_cmp" };
                let _ = writeln!(out, "  int32_t {v} = {f}(*{a}, *{b});");
            }
            CTy::Int(_) | CTy::Bool | CTy::Char => {
                let _ = writeln!(out, "  int32_t {v} = (*{a} > *{b}) - (*{a} < *{b});");
            }
            CTy::String => {
                let _ = writeln!(out, "  int32_t {v} = lust_str_cmp(lust_string_as_str({a}), lust_string_as_str({b}));");
            }
            CTy::Ref(_) => {
                let _ = writeln!(out, "  int32_t {v} = lust_str_cmp(*{a}, *{b});");
            }
            CTy::Tuple(es) => {
                let _ = writeln!(out, "  int32_t {v} = 0;");
                for (i, e) in es.iter().enumerate() {
                    let _ = writeln!(out, "  if (!{v}) {{");
                    let c = self.cmp3_c(out, e, &format!("(&({a})->f{i})"), &format!("(&({b})->f{i})"), partial);
                    let _ = writeln!(out, "  {v} = {c}; }}");
                }
            }
            // A derived `Ord` (check/collect.rs `has_total_ord`), or,
            // for `partial`, its `PartialOrd` (check/collect.rs
            // `has_partial_cmp`).
            _ => {
                let (g, pre) = if partial { (Glue::PCmp, "pcmp") } else { (Glue::Cmp, "cmp") };
                self.want(g, t);
                let _ = writeln!(out, "  int32_t {v} = {pre}_{}({a}, {b});", mangle(t));
            }
        }
        v
    }

    /// The `is_less` adapter of one sort call (runtime/sort.h): `a.lt(b)`
    /// for `sort`, `compare(a, b) == Less` for `sort_by`, and
    /// `f(a).lt(&f(b))` for `sort_by_key` (the keys drop after, in
    /// reverse order of creation, as Rust's temporaries do).
    fn sort_adapter(&mut self, b: Builtin, elem: &CTy, clo: Option<(sync::Callee, u8, CTy)>) -> String {
        use Builtin as B;
        let name = format!("lust_less_{}_{}", names::fn_tag(self.slots.of(self.body.fn_id)), self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let (a, bb) = (format!("(({pt})a)"), format!("(({pt})b)"));
        let mut body = String::new();
        match (b, clo) {
            (B::SliceSortBy | B::SliceSortUnstableBy, Some(f)) => {
                let (r, rt) = self.adapter_call_c(&mut body, &f, "ctx", &[a, bb]);
                let d = self.disc(&rt, &format!("(&{r})"));
                let _ = writeln!(body, "  return {d} == 0;");
            }
            (B::SliceSortByKey | B::SliceSortUnstableByKey, Some(f)) => {
                let (ka, kt) = self.adapter_call_c(&mut body, &f, "ctx", &[a]);
                let (kb, _) = self.adapter_call_c(&mut body, &f, "ctx", &[bb]);
                let c = self.cmp3_c(&mut body, &kt, &format!("(&{ka})"), &format!("(&{kb})"), true);
                if needs_drop_c(self.p, &kt) {
                    self.want(Glue::Drop, &kt);
                    let _ = writeln!(body, "  drop_{0}(&{kb}); drop_{0}(&{ka});", mangle(&kt));
                }
                let _ = writeln!(body, "  return {c} < 0;");
            }
            _ => {
                let c = self.cmp3_c(&mut body, elem, &a, &bb, true);
                let _ = writeln!(body, "  return {c} < 0;");
            }
        }
        let _ = writeln!(self.prelude, "static uint8_t {name}(void *ctx, const void *a, const void *b) {{
{body}}}");
        name
    }

    /// The C fn behind a constructor item coerced to fn pointer type
    /// `fp` (`Rvalue::ItemShim`): it takes the pointer's C params (a
    /// zero-sized one is dropped, as in every fn pointer call) and
    /// builds the variant from them. Emitted once per function and
    /// item (named by this function's slot), ahead of the function.
    fn item_shim(&mut self, item: Ty, fp: &CTy) -> String {
        let CTy::FnPtr(ps, ret) = fp else { unreachable!("ItemShim to a non fn pointer type") };
        let variant = match self.body.tys.kind(item) {
            TyKind::FnDef(_, args) => match self.body.tys.args(args).first() {
                Some(GenericArg::Const(c)) => match self.body.tys.const_kind(*c) {
                    ConstKind::Int(v) => v as usize,
                    _ => 0,
                },
                _ => 0,
            },
            _ => unreachable!("ItemShim of a non item type"),
        };
        let key = format!("{variant}_{}", mangle(fp));
        if let Some(n) = self.shims.get(&key) {
            return n.clone();
        }
        let name = format!("lust_ctor_{}_{}", names::fn_tag(self.slots.of(self.body.fn_id)), self.shims.len());
        self.shims.insert(key, name.clone());
        let mut decls: Vec<String> = Vec::new();
        let mut vals: Vec<String> = Vec::new();
        for (i, t) in ps.iter().enumerate() {
            if param_dropped(self.p, t) {
                vals.push(zero_lit(self.p, t));
            } else if param_by_ptr(self.p, t) {
                decls.push(format!("{} p{i}", param_ctype(self.p, t)));
                vals.push(format!("(*p{i})"));
            } else {
                decls.push(format!("{} p{i}", ctype(t)));
                vals.push(format!("p{i}"));
            }
        }
        let value = match &**ret {
            CTy::Adt(a) if !self.p.adt(*a).is_enum => {
                if vals.is_empty() {
                    zero_lit(self.p, ret)
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("(({}){{ {} }})", names::adt(*a), fields.join(", "))
                }
            }
            _ => self.make_variant(ret, variant, &vals),
        };
        let rt = ctype(ret);
        if ret_by_out(self.p, ret) {
            decls.insert(0, format!("{rt} *out"));
            let _ = writeln!(self.prelude, "static void {name}({}) {{ *out = {value}; }}", decls.join(", "));
        } else {
            let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
            let _ = writeln!(self.prelude, "static {rt} {name}({params}) {{ return {value}; }}");
        }
        name
    }

    /// The C fn behind an integer type's primitive builtin method item
    /// coerced to fn pointer type `fp_ty` (`Rvalue::ItemShim`): it calls
    /// the builtin on its params. The call is emitted by a generator over
    /// a one-call body (locals: the return value, then the params). A
    /// panic reports the type's `int_impl!` / `uint_impl!` line in core,
    /// where rustc's fn pointer shim locates a `#[track_caller]` method.
    fn prim_shim(&mut self, item: Ty, fp_ty: Ty, fp: &CTy) -> String {
        let p = self.p;
        let CTy::FnPtr(ps, ret) = fp else { unreachable!("ItemShim to a non fn pointer type") };
        let tys = &self.body.tys;
        let TyKind::FnDef(_, args) = tys.kind(item) else { unreachable!("ItemShim of a non item type") };
        let gs = tys.args(args).to_vec();
        let self_ty = gs.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
        let code = match gs.get(2) {
            Some(GenericArg::Const(c)) => match tys.const_kind(*c) {
                ConstKind::Int(v) => v as u32,
                _ => u32::MAX,
            },
            _ => u32::MAX,
        };
        let b = crate::check::prim_builtin_of_code(code).expect("internal: an ItemShim of an unknown builtin");
        let key = format!("p{code}_{}_{}", mangle(&cty(tys, self_ty)), mangle(fp));
        if let Some(n) = self.shims.get(&key) {
            return n.clone();
        }
        let name = format!("lust_prim_{}_{}", names::fn_tag(self.slots.of(self.body.fn_id)), self.shims.len());
        self.shims.insert(key, name.clone());
        let TyKind::FnPtr(sig) = tys.kind(fp_ty) else { unreachable!("ItemShim to a non fn pointer type") };
        let sig = tys.sig(sig).value;
        let ins: Vec<Ty> = tys.tys_of(sig.inputs).to_vec();
        let decl = |ty: Ty| crate::ir::LocalDecl { ty, mutable: false, name: None };
        let mut locals = vec![decl(sig.output)];
        locals.extend(ins.iter().map(|&t| decl(t)));
        let body = Body {
            fn_id: self.body.fn_id,
            tys: self.body.tys.clone(),
            locals,
            blocks: Vec::new(),
            arg_count: ins.len(),
            reads: Default::default(),
            lower_errs: Vec::new(),
            annotations: Vec::new(),
            promoted: Vec::new(),
            index_exprs: Vec::new(),
            pat_back_index: Vec::new(),
            pat_front_index: Vec::new(),
            pat_subslice: Vec::new(),
        dyn_coerce: Vec::new(),
            false_edges: Vec::new(),
            opaque_locals: Vec::new(),
            opaque_nodrop: Vec::new(),
            stmt_unwind: Vec::new(),
        };
        let line = match tys.kind(self_ty) {
            TyKind::Int(it) => int_impl_line(it),
            _ => 0,
        };
        let loc = std_loc(0, line as u64, 5);
        // The shim's params have no drop flags: the builtin takes each by
        // a plain read (a by-value one, `drop`'s, is consumed there).
        let ops: Vec<Operand> = (1..=ins.len()).map(|i| Operand::Copy(Place::local(i as Local))).collect();
        let mut g = FnGen::new(p, &body, self.map, self.base_line, self.slots);
        let mut post: Vec<String> = Vec::new();
        let value = if b == Builtin::PrimFromCast {
            g.rvalue(&Rvalue::Cast(ops[0].clone(), sig.output), &loc, &mut post)
        } else {
            g.call_value(CallTarget::Builtin(b), &ops, ret, &loc, &mut post)
        };
        let mut decls: Vec<String> = Vec::new();
        let mut inits = String::new();
        for (i, t) in ps.iter().enumerate() {
            if param_dropped(p, t) {
                let _ = write!(inits, "  {} l{} = {};", ctype(t), i + 1, zero_lit(p, t));
            } else if param_by_ptr(p, t) {
                // The fn pointer type passes it by pointer (`param_ctype`): copy it in.
                decls.push(format!("{} p{}", param_ctype(p, t), i + 1));
                let _ = write!(inits, "  {} l{} = *p{};", ctype(t), i + 1, i + 1);
            } else {
                decls.push(format!("{} l{}", ctype(t), i + 1));
            }
        }
        let rt = ctype(ret);
        let (head, tail) = if ret_by_out(p, ret) {
            decls.insert(0, format!("{rt} *out"));
            (format!("static void {name}({})", decls.join(", ")), format!("*out = r;"))
        } else {
            let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
            (format!("static {rt} {name}({params})"), "return r;".to_string())
        };
        let exc = if p.unwind { "  lust_exc ex; (void)ex;" } else { "" };
        let _ = writeln!(
            self.prelude,
            "{}{head} {{{exc}{inits}\n{}  {rt} r = {value};\n{}  {tail}\n}}",
            std::mem::take(&mut g.prelude),
            g.out,
            post.iter().map(|x| format!("  {x}\n")).collect::<String>()
        );
        self.glue.extend(g.glue);
        self.sig_types.extend(g.sig_types);
        self.vtables.extend(g.vtables);
        if self.bad_callee.is_none() {
            self.bad_callee = g.bad_callee;
        }
        name
    }

    /// The `cmp(ctx, p)` adapter of one binary search call: `p.cmp(x)`,
    /// `f(p)` as an Ordering, or `f(p).cmp(b)` with ctx `{&f, b}`.
    fn search_adapter(&mut self, b: Builtin, elem: &CTy, clo: Option<(sync::Callee, u8, CTy)>) -> String {
        use Builtin as B;
        let name = format!("lust_bcmp_{}_{}", names::fn_tag(self.slots.of(self.body.fn_id)), self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let p = format!("(({pt})p)");
        let mut body = String::new();
        match (b, clo) {
            (B::SliceBinarySearchBy, Some(f)) => {
                let (r, rt) = self.adapter_call_c(&mut body, &f, "ctx", &[p]);
                let d = self.disc(&rt, &format!("(&{r})"));
                let _ = writeln!(body, "  return (int32_t){d} - 1;");
            }
            (B::SliceBinarySearchByKey, Some(f)) => {
                let (k, kt) = self.adapter_call_c(&mut body, &f, "((void**)ctx)[0]", &[p]);
                let kp = ctype(&CTy::Ref(Box::new(kt.clone())));
                let c = self.cmp3_c(&mut body, &kt, &format!("(&{k})"), &format!("(({kp})((void**)ctx)[1])"), false);
                if needs_drop_c(self.p, &kt) {
                    self.want(Glue::Drop, &kt);
                    let _ = writeln!(body, "  drop_{}(&{k});", mangle(&kt));
                }
                let _ = writeln!(body, "  return {c};");
            }
            _ => {
                let c = self.cmp3_c(&mut body, elem, &p, &format!("(({pt})ctx)"), false);
                let _ = writeln!(body, "  return {c};");
            }
        }
        let _ = writeln!(self.prelude, "static int32_t {name}(void *ctx, const void *p) {{
{body}}}");
        name
    }

    fn eq_expr(&mut self, t: &CTy, a: &str, b: &str) -> String {
        match t {
            CTy::Unit => "1".into(),
            // A fieldless enum with the structural `==`: equal discriminants, no glue call
            // (read through the pointers: the enum's definition).
            CTy::Adt(_) if fieldless_enum(self.p, t) => {
                self.note_held(t);
                format!("({} == {})", self.disc(t, a), self.disc(t, b))
            }
            CTy::Int(i) if is128(*i) => format!("({a}->lo == {b}->lo && {a}->hi == {b}->hi)"),
            CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) | CTy::FnPtr(..) => format!("(*{a} == *{b})"),
            _ => {
                self.want(Glue::Eq, t);
                format!("eq_{}({a}, {b})", mangle(t))
            }
        }
    }

    /// Emits one intrinsic call as a plain runtime call (section 3.2: no
    /// IR node per family, codegen emits the C call direct). This is the
    /// second privilege line behind check: an intrinsic that reaches
    /// codegen from a crate its registry row does not allow is a
    /// compiler bug, so it stops here instead of emitting the call.
    fn intrinsic(&mut self, id: u32, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let def = lang::intrinsic(id);
        let krate = self.p.fn_shipped_crate(self.body.fn_id);
        assert!(
            def.allows(krate),
            "internal: intrinsic `core::intrinsics::{}` reached codegen from a crate that may not call it",
            def.name
        );
        assert!(def.implemented, "internal: intrinsic `core::intrinsics::{}` reached codegen with no body", def.name);
        let mut args: Vec<String> = Vec::new();
        for (o, sig) in ops.iter().zip(def.params) {
            let v = self.operand(o, loc, post).0;
            // A `&[u8]` reaches C as its pointer and its length.
            args.push(if *sig == SigTy::Bytes { format!("({v}).ptr, ({v}).len") } else { v });
        }
        if matches!(def.ret, SigTy::Never | SigTy::Unit) {
            // The C callee returns void (and for `!`, never returns). The
            // comma form still gives the assignment a value of the right
            // shape: `()`, or the dead continuation's.
            format!("({}({}), ((lust_Unit){{}}))", def.c_symbol, args.join(", "))
        } else if def.ret == SigTy::Bytes {
            // A `&[u8]` comes back as a lust_str: rebuild the slice value.
            let sl = ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))));
            format!("({{ lust_str __b = {}({}); ({sl}){{ .ptr = __b.ptr, .len = __b.len }}; }})", def.c_symbol, args.join(", "))
        } else {
            format!("{}({})", def.c_symbol, args.join(", "))
        }
    }

    fn builtin(&mut self, b: Builtin, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        use Builtin as B;
        // `thread::spawn` reads its closure's body fn (cgen/sync.rs).
        if let B::Sync(
            op @ (crate::check::sync::SyncOp::ThreadSpawn
            | crate::check::sync::SyncOp::ScopeSpawn
            | crate::check::sync::SyncOp::ThreadScope
            | crate::check::sync::SyncOp::CondvarWaitWhile
            | crate::check::sync::SyncOp::CondvarWaitTimeoutWhile
            | crate::check::sync::SyncOp::AtomicFetchUpdate
            | crate::check::sync::SyncOp::OnceGetOrInit
            | crate::check::sync::SyncOp::BuilderSpawn
            | crate::check::sync::SyncOp::BuilderSpawnScoped),
        ) = b
        {
            return self.thread_closure_call(op, ops, loc, post);
        }
        if b == B::Sync(crate::check::sync::SyncOp::CatchUnwind) {
            return self.catch_unwind_call(ops, loc, post);
        }
        if b == B::Sync(crate::check::sync::SyncOp::ArcNewCyclic) || b == B::RcNewCyclic {
            return self.new_cyclic(ops, loc, post, b != B::RcNewCyclic);
        }
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in ops {
            let (v, t) = self.operand(o, loc, post);
            vals.push(v);
            tys.push(t);
        }
        let int_of = |t: &CTy| match t {
            CTy::Int(i) => *i,
            _ => IntTy::I64,
        };
        // The (element type, data pointer, length) C expressions of
        // a Vec, slice, or array operand, in whichever shape the
        // method receiver arrived: `&Vec` (pointer to lust_Vec),
        // `&[T]` (the fat slice value), `&&[T]` (pointer to it),
        // `&[T; N]` (pointer to the array), or a by-value array.
        if let Some(v) = self.fmt_builtin(b, &vals, &tys, loc) {
            return v;
        }
        // Owning fat pointers (cgen/own.rs): their counts, `ptr_eq`,
        // and the conversions that build one.
        if let Some(v) = self.own_builtin(b, &vals, &tys, loc) {
            return v;
        }
        if let B::Sync(op) = b {
            return self.sync_builtin(op, &vals, &tys, loc);
        }
        // The R4 slice and Vec methods (cgen/slices.rs).
        if let Some(v) = self.slices_builtin(b, ops, &vals, &tys) {
            return v;
        }
        let slice_like = |t: &CTy, val: &str| -> (CTy, String, String) {
            match t {
                CTy::Ref(inner) => match &**inner {
                    CTy::Vec(e) => ((**e).clone(), format!("(({}*){val}->ptr)", ctype(e)), format!("{val}->len")),
                    CTy::Slice(e) => ((**e).clone(), format!("{val}->ptr"), format!("{val}->len")),
                    CTy::Array(e, n) => ((**e).clone(), format!("{val}->v"), format!("((uint64_t){n})")),
                    _ => unreachable!(),
                },
                CTy::Slice(e) => ((**e).clone(), format!("{val}.ptr"), format!("{val}.len")),
                CTy::Array(e, n) => ((**e).clone(), format!("{val}.v"), format!("((uint64_t){n})")),
                _ => unreachable!(),
            }
        };
        match b {
            B::Sync(_) | B::RcNewCyclic => unreachable!("sync builtins and new_cyclic emit in cgen/sync.rs"),
            B::ExtendParam => unreachable!("extend on a type parameter exists only in template checks"),
            // `by_ref`: the `&mut Self` receiver is the result.
            B::IterByRef => vals[0].clone(),
            B::OwnFrom(_) | B::OwnIntoString | B::OwnSliceAlloc(_) | B::OwnSlicePush => unreachable!("owning pointer builtins emit in cgen/own.rs"),
            B::SliceSplitAt(_) | B::SliceSplitEnd(_) | B::StrSplitAt(_) | B::SliceStrip(_) | B::SliceTrimAscii(_) | B::SliceAsChunks(_) => {
                unreachable!("dest-typed: cgen/slices.rs slice_split_builtin")
            }
            B::IntToLeBytes | B::IntToBeBytes | B::IntToNeBytes | B::IntFromLeBytes | B::IntFromBeBytes | B::IntFromNeBytes => {
                unreachable!("byte conversions emit in cgen/bytes.rs")
            }
            // Emitted by `fmt_builtin` above (cgen/fmt.rs).
            B::FmtWriteStr
            | B::FmtWriteChar
            | B::FmtPad
            | B::FmtPadIntegral
            | B::FmtWidth
            | B::FmtPrecision
            | B::FmtFill
            | B::FmtAlternate
            | B::FmtSignPlus
            | B::FmtSignMinus
            | B::FmtSignAwareZeroPad
            | B::FmtDebugStruct
            | B::FmtDebugTuple
            | B::FmtDebugList
            | B::FmtDebugSet
            | B::FmtDebugMap
            | B::DsField
            | B::DtField
            | B::DlEntry
            | B::DmEntry
            | B::DmKey
            | B::DmValue
            | B::FmtFinish
            | B::FmtFinishNonExhaustive
            | B::FmtWriteFmt
            | B::FmtCallDisplay
            | B::FmtCallDebug
            | B::ConvIdent
            | B::ConvStrBytes
            | B::ConvArraySlice
            | B::ConvDeref
            | B::ConvRcInner
            | B::CowIntoOwned
            | B::CowToMut
            | B::CowAddStr
            | B::CowAddAssignStr
            | B::CowDeref => unreachable!("fmt and conversion builtins emit in cgen/fmt.rs"),
            // The operand was moved into the call: no drop ever runs.
            B::MemForget => "((lust_Unit){})".into(),
            // `fmt::format(args)`: the value `args.to_string()` formats.
            B::FmtFormat => {
                let tmp = self.tmp();
                let ct = CTy::Fmt(crate::ty::fmt::FmtTy::Arguments);
                let _ = writeln!(self.out, "    {} {tmp} = {};", ctype(&ct), vals[0]);
                self.to_string_value(&ct, &format!("(&{tmp})"), loc)
            }
            // `mem::discriminant`'s reads (std source, library/core/src/mem.rs):
            // the declared discriminant of the enum behind the pointer as an
            // i128, and a code for the type rustc keeps it in.
            B::DiscriminantValue => {
                let CTy::Ref(t) = &tys[0] else { unreachable!() };
                let discs = if disc_holder(self.p, t).is_some() { adt_discs(self.p, t) } else { Vec::new() };
                if discs.is_empty() {
                    return scalar_lit(0, 16, true);
                }
                let idx = self.disc(t, &vals[0]);
                if discs_sequential(&discs) {
                    format!("((lust_i128){{(uint64_t)({idx}), 0}})")
                } else {
                    let lits: Vec<String> = discs.iter().map(|&d| scalar_lit(d as u128, 16, true)).collect();
                    format!("((lust_i128[]){{{}}})[{idx}]", lits.join(", "))
                }
            }
            B::DiscriminantKind => {
                let CTy::Ref(t) = &tys[0] else { unreachable!() };
                let code = crate::ty::layout::disc_kind_code(disc_holder(self.p, t).unwrap_or(IntTy::U8));
                format!("((uint8_t){code})")
            }
            // Interior writes of std source cells (W-STD-C): the slot is
            // an `Option<T>` behind a shared reference. `once_init` runs
            // only on a `None` slot, so nothing is overwritten.
            B::OnceInit => {
                let CTy::Ref(opt) = &tys[0] else { unreachable!() };
                let some = self.make_variant(opt, 1, &[vals[1].clone()]);
                let _ = writeln!(self.out, "    *({}) = {some};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::OnceTake => {
                let CTy::Ref(opt) = &tys[0] else { unreachable!() };
                let ot = ctype(opt);
                let (pa, old) = (self.tmp(), self.tmp());
                let none = self.make_variant(opt, 0, &[]);
                let _ = writeln!(self.out, "    {ot}* {pa} = {}; {ot} {old} = *{pa}; *{pa} = {none};", vals[0]);
                old
            }
            B::HashNew
            | B::HashWithCapacity
            | B::HashWithHasher
            | B::HashWithCapacityAndHasher
            | B::HashDefault
            | B::HashLen
            | B::HashIsEmpty
            | B::HashClear
            | B::HashCapacity
            | B::MapInsert
            | B::MapGet
            | B::MapGetMut
            | B::MapContainsKey
            | B::MapRemove
            | B::MapRemoveEntry
            | B::MapRetain
            | B::SetRetain
            | B::MapEntry
            | B::EntryOrInsert
            | B::EntryOrDefault
            | B::EntryKey
            | B::EntryOccupied
            | B::EntryIntoMut
            | B::EntryInsert
            | B::EntryGetMut
            | B::EntryInsertEntry
            | B::EntryAsOccupied
            | B::EntryAsVacant
            | B::VacIntoKey
            | B::MapGetKeyValue
            | B::OccKey
            | B::OccGet
            | B::OccGetMut
            | B::OccIntoMut
            | B::OccInsert
            | B::OccRemove
            | B::OccRemoveEntry
            | B::SetInsert
            | B::SetContains
            | B::SetRemove
            | B::SetGet
            | B::HashIterNew
            | B::HashIterNext
            | B::HashIterLen
            | B::HashExtendReserve
            | B::HashReserve
            | B::HashInto
            | B::HashOne
            | B::BuildHasher
            | B::HasherCall => unreachable!("hash builtins emit in cgen/hash.rs"),
            B::StrSplitNext | B::StrSplitNextBack | B::StrSplitUpper | B::StrSplitOnce | B::StrRSplitOnce | B::StrMatchesNext | B::StrMatchesNextBack | B::StrPatFind | B::StrPatRfind | B::StrPatContains | B::StrPatStartsWith | B::StrPatEndsWith | B::StrPatStripPrefix | B::StrPatStripSuffix | B::StrTrimMatches | B::StrTrimStartMatches | B::StrTrimEndMatches | B::StrPatReplace | B::StrPatReplacen => {
                unreachable!("split builtins emit in cgen/split.rs")
            }
            B::HashExtend | B::VecExtend | B::StringExtend | B::IterArrayIntoIter | B::IterRepeatN | B::SliceJoinBorrow | B::SliceConcatBorrow | B::SliceCloneFromWritten | B::ArrayIterAsSlice | B::ArrayFromFn | B::ArrayMap | B::StrMatches | B::StrEncodeUtf16 | B::StrParse => {
                unreachable!("expanded with its iterator (lower/iter.rs)")
            }
            B::ConvInto => unreachable!("expanded per conversion (lower/iter.rs)"),
            B::PrimFromCast => unreachable!("lowered as a cast (lower.rs)"),
            B::NonZeroNew => unreachable!("lowered as an aggregate (lower.rs)"),
            B::NonZeroGet => format!("(({0}).f0)", vals[0]),
            B::WaitTimedOut => format!("((*{0}).f0)", vals[0]),
            B::MaybeUninitWrite => format!("(((*{0}).f0 = {1}), &(*{0}).f0)", vals[0], vals[1]),
            B::MaybeUninitAsPtr | B::MaybeUninitAsMutPtr => format!("(&(*{0}).f0)", vals[0]),
            B::MaybeUninitUninit | B::MaybeUninitZeroed | B::MaybeUninitNew | B::VecSpareCapacityMut | B::BoxNewUninit | B::BoxNewZeroed | B::BoxWrite | B::BoxNewUninitSlice => {
                unreachable!("dest-typed compound literals in the call dispatch")
            }
            B::RcNewUninit | B::ArcNewUninit => unreachable!("lowered as two calls (lower.rs)"),
            B::EntryOrInsertWith | B::EntryOrInsertWithKey | B::EntryAndModify => unreachable!("expanded with its closure (lower/iter.rs)"),
            B::MemDrop => {
                // The operand was moved into the call, so its own
                // drop flag is already clear; this is its one drop.
                if needs_drop_c(self.p, &tys[0]) {
                    self.want(Glue::Drop, &tys[0]);
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {} {t} = {};", ctype(&tys[0]), vals[0]);
                    let _ = writeln!(self.out, "    drop_{}(&{t});", mangle(&tys[0]));
                }
                "((lust_Unit){})".into()
            }
            B::StringNew => "lust_string_new()".into(),
            B::StringFrom => match &tys[0] {
                CTy::Char => {
                    // Rust allocates exactly the char's UTF-8 length.
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    lust_String {t} = lust_string_with_capacity({0} < 0x80u ? 1 : {0} < 0x800u ? 2 : {0} < 0x10000u ? 3 : 4); lust_string_push_char(&{t}, {0});",
                        vals[0]
                    );
                    t
                }
                CTy::String => vals[0].clone(),
                _ => format!("lust_string_from({})", vals[0]),
            },
            B::StringWithCapacity => format!("lust_string_with_capacity({})", vals[0]),
            B::VecNew | B::VecWithCapacity => unreachable!("lowered to VecLit"),
            B::BoxNew => {
                let et = ctype(&tys[0]);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {et} *{t} = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *{t} = {};", vals[0]);
                t
            }
            // Leaking a box is just forgetting it: the moved
            // operand's drop flag is already clear, and the
            // pointer value is the `&mut T` result.
            B::BoxLeak => vals[0].clone(),
            // The box's C value is the payload pointer, thin or fat.
            B::BoxAsPtr => format!("(*{})", vals[0]),
            B::RcNew => {
                let it = format!("RcI_{}", mangle(&tys[0]));
                let t = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {it} *{t} = ({it}*)lust_alloc({}, _Alignof({it})); {t}->strong = 1; {t}->weak = 1; {} = {};",
                    rc_size(&it, &tys[0]),
                    rc_value(&t, &tys[0]),
                    vals[0]
                );
                t
            }
            // An `Rc<dyn Tr>`'s two counts sit right before its value; the
            // weak count holds the strong refs' implicit weak ref (W-STD-A).
            B::RcStrongCount | B::RcWeakCount if matches!(&tys[0], CTy::Ref(r) if **r == CTy::RcDyn) => {
                let h = own::counts(&CTy::Dyn, &format!("(*{})", vals[0]));
                if b == B::RcStrongCount { format!("{h}[0]") } else { format!("({h}[1] - 1)") }
            }
            B::RcStrongCount => format!("(*{})->strong", vals[0]),
            B::ExitCodeFrom => format!("((uint8_t){})", vals[0]),
            // The slice over the buffer, which is never freed.
            B::VecLeak => {
                let CTy::Vec(e) = &tys[0] else { unreachable!("leak on a Vec") };
                let (et, st) = (ctype(e), ctype(&CTy::Slice(e.clone())));
                let v = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {v} = {};", vals[0]);
                format!("(({st}){{ ({et}*){v}.ptr, {v}.len }})")
            }
            B::VecIntoBoxedSlice => {
                // Rust shrinks the buffer to the length first.
                let CTy::Vec(e) = &tys[0] else { unreachable!("into_boxed_slice on a Vec") };
                let (et, st) = (ctype(e), ctype(&CTy::Slice(e.clone())));
                let v = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {v} = {}; lust_vec_shrink_to(&{v}, 0, sizeof({et}), _Alignof({et}));", vals[0]);
                format!("(({st}){{ ({et}*){v}.ptr, {v}.len }})")
            }
            B::BoxSliceIntoVec => {
                // A zero-sized element's Vec stores capacity 0 (see vec_cap).
                let CTy::BoxSlice(e) = &tys[0] else { unreachable!("into_vec on a Box<[T]>") };
                format!("((lust_Vec){{ (void*)({0}).ptr, ({0}).len, sizeof({1}) ? ({0}).len : 0 }})", vals[0], ctype(e))
            }
            B::BoxSliceIntoIter => format!("((lust_VecIter){{ (void*)({0}).ptr, ({0}).len, ({0}).len, 0 }})", vals[0]),
            B::ParseIntErrorKind => format!("(&({})->f0)", vals[0]),
            B::FromStrRadix(it) => {
                // core panics on a radix outside 2..=36 before parsing,
                // at its `from_str_radix` line for the type's sign.
                let sloc = std_loc(0, if it.signed() { 1866 } else { 1867 }, 1);
                let _ = writeln!(self.out, "    lust_radix_check({}, {sloc});", vals[1]);
                self.parse_int_c(it, &str_of(&vals[0], &tys[0]), &vals[1])
            }
            // The primitive int `FromStr` (tf-str), at radix 10.
            B::ParseInt(it) => self.parse_int_c(it, &str_of(&vals[0], &tys[0]), "10"),
            B::ParseFloat(f) => {
                let p = self.p;
                let (Some(pfe), Some(fek)) = (
                    p.tys.local_adt_of(crate::check::generics::parse_float_error_def()),
                    p.tys.local_adt_of(crate::check::generics::float_error_kind_def()),
                ) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let val_ty = CTy::Float(f);
                let res = CTy::Result(Box::new(val_ty.clone()), Box::new(CTy::Adt(pfe)));
                self.note_held(&res);
                let (t, v, kind) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let (ct, rf) = if f == FloatTy::F32 { ("float", "lust_str_parse_f32") } else { ("double", "lust_str_parse_f64") };
                let _ = writeln!(self.out, "    {ct} {v}; int {kind}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if ({rf}({a}, &{v}, &{kind})) {{ {ok_f} = {v}; {ok_d} }}");
                let kct = CTy::Adt(fek);
                let (k0, k1) = (self.make_variant(&kct, 0, &[]), self.make_variant(&kct, 1, &[]));
                let _ = writeln!(self.out, "    else {{ {err_f}.f0 = {kind} ? {k1} : {k0}; {err_d} }}");
                t
            }
            B::ParseBool => {
                let p = self.p;
                let Some(pbe) = p.tys.local_adt_of(crate::check::generics::parse_bool_error_def()) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let res = CTy::Result(Box::new(CTy::Bool), Box::new(CTy::Adt(pbe)));
                self.note_held(&res);
                let (t, v) = (self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    uint8_t {v}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if (lust_parse_bool({a}, &{v})) {{ {ok_f} = {v}; {ok_d} }}");
                let _ = writeln!(self.out, "    else {{ {err_f} = (({}){{}}); {err_d} }}", ctype(&CTy::Adt(pbe)));
                t
            }
            B::ParseChar => {
                let p = self.p;
                let (Some(pce), Some(cek)) = (
                    p.tys.local_adt_of(crate::check::generics::parse_char_error_def()),
                    p.tys.local_adt_of(crate::check::generics::char_error_kind_def()),
                ) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let res = CTy::Result(Box::new(CTy::Char), Box::new(CTy::Adt(pce)));
                self.note_held(&res);
                let (t, v, kind) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    uint32_t {v}; int {kind}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if (lust_parse_char({a}, &{v}, &{kind})) {{ {ok_f} = {v}; {ok_d} }}");
                let kct = CTy::Adt(cek);
                let (k0, k1) = (self.make_variant(&kct, 0, &[]), self.make_variant(&kct, 1, &[]));
                let _ = writeln!(self.out, "    else {{ {err_f}.f0 = {kind} ? {k1} : {k0}; {err_d} }}");
                t
            }
            B::StringFromUtf8 | B::StrFromUtf8 => {
                // Validate, then build `Ok(text)` or `Err(error)` with
                // Rust's `valid_up_to` and `error_len` (runtime core.c).
                let p = self.p;
                let string = b == B::StringFromUtf8;
                let (Some(fe), Some(ue)) = (p.tys.local_adt_of(crate::check::generics::from_utf8_error_def()), p.tys.local_adt_of(crate::check::generics::utf8_error_def()))
                else {
                    unreachable!("from_utf8 type-checks only with std's error Adts")
                };
                let (ok, err) = if string { (CTy::String, CTy::Adt(fe)) } else { (CTy::Ref(Box::new(CTy::Str)), CTy::Adt(ue)) };
                let res = CTy::Result(Box::new(ok), Box::new(err));
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::U8)));
                let (t, vu, el) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let (ptr, len, ok_val, bytes) = if string {
                    let v = self.tmp();
                    let _ = writeln!(self.out, "    lust_Vec {v} = {};", vals[0]);
                    (
                        format!("((const uint8_t*){v}.ptr)"),
                        format!("{v}.len"),
                        format!("(lust_String){{ (uint8_t*){v}.ptr, {v}.len, {v}.cap }}"),
                        Some(v),
                    )
                } else {
                    let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                    let ok_val = format!("(lust_str){{ (uint8_t*){ptr}, {len} }}");
                    (format!("((const uint8_t*){ptr})"), len, ok_val, None)
                };
                // The `Utf8Error` part of the error value.
                let u = if string { format!("{err_f}.f1") } else { err_f.clone() };
                let o = format!("{u}.f1");
                let (some_f, some_d, none_d) = (variant_field(p, &opt, &o, 1, 0), disc_set(p, &opt, &o, 1), disc_set(p, &opt, &o, 0));
                let rt = ctype(&res);
                let _ = writeln!(self.out, "    uint64_t {vu} = 0; uint8_t {el} = 0; {rt} {t};");
                let _ = writeln!(self.out, "    if (lust_utf8_check({ptr}, {len}, &{vu}, &{el})) {{ {ok_f} = {ok_val}; {ok_d} }}");
                let keep = bytes.map_or(String::new(), |v| format!("{err_f}.f0 = {v}; "));
                let _ = writeln!(
                    self.out,
                    "    else {{ {keep}{u}.f0 = {vu}; if ({el}) {{ {some_f} = {el}; {some_d} }} else {{ {none_d} }} {err_d} }}"
                );
                t
            }
            B::StringFromUtf8Lossy => {
                // `Cow::Borrowed` of the bytes as a `str` when they are
                // valid UTF-8, else `Cow::Owned` of the lossy text in a
                // String that starts with the input's capacity, as
                // std's `from_utf8_lossy` allocates (runtime sys.c
                // appends valid runs and U+FFFD replacements).
                let p = self.p;
                let a = p
                    .gx
                    .adt_instance_of
                    .iter()
                    .position(|o| {
                        matches!(o, Some((d, args)) if *d == crate::check::generics::cow_def()
                            && p.tys.args(*args).first().and_then(|g| g.as_ty()) == Some(STR))
                    })
                    .expect("from_utf8_lossy type-checks only with the Cow<str> instance");
                let cow = CTy::Adt(AdtId(a as u32));
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, vu, el, s) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let (f0, f1) = (variant_field(p, &cow, &t, 0, 0), variant_field(p, &cow, &t, 1, 0));
                let (d0, d1) = (disc_set(p, &cow, &t, 0), disc_set(p, &cow, &t, 1));
                let ct = ctype(&cow);
                let _ = writeln!(self.out, "    uint64_t {vu} = 0; uint8_t {el} = 0; {ct} {t};");
                let _ = writeln!(
                    self.out,
                    "    if (lust_utf8_check((const uint8_t*){ptr}, {len}, &{vu}, &{el})) {{ {f0} = (lust_str){{ (uint8_t*){ptr}, {len} }}; {d0} }}"
                );
                let _ = writeln!(
                    self.out,
                    "    else {{ lust_String {s} = lust_string_with_capacity({len}); lust_sys_utf8_lossy((const uint8_t*){ptr}, {len}, &{s}); {f1} = {s}; {d1} }}"
                );
                t
            }
            B::FromUtf8ErrorUtf8Error => format!("(*{}).f1", vals[0]),
            B::FromUtf8ErrorAsBytes => {
                let sl = ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))));
                format!("(({sl}){{ (uint8_t*)(*{0}).f0.ptr, (*{0}).f0.len }})", vals[0])
            }
            B::FromUtf8ErrorIntoBytes => format!("({}).f0", vals[0]),
            B::Utf8ErrorValidUpTo => format!("(*{}).f0", vals[0]),
            // `std::panic::Location` (check/caller.rs): a fresh value for
            // the packed location, which lives as long as the program.
            B::LocationCaller => {
                // One node per distinct location, kept on a per-site static
                // list: the value lives as long as the program, is shared by
                // equal locations, and stays reachable (no leak).
                let p = self.p;
                let a = p.tys.local_adt_of(crate::check::generics::location_def()).expect("Location is a std Adt");
                let ct = ctype(&CTy::Adt(a));
                let fslot = names::fn_tag(self.slots.of(self.body.fn_id));
                let (t, l, n) = (self.tmp(), self.tmp(), self.tmp());
                let node = format!("lc{fslot}_{n}");
                let _ = writeln!(self.prelude, "static struct {node} {{ lust_loc k; struct {node} *next; {ct} v; }} *{node}_head;");
                let _ = writeln!(
                    self.out,
                    "    lust_loc {l} = (lust_loc)({loc}); struct {node} *{n} = {node}_head; while ({n} && {n}->k != {l}) {n} = {n}->next;\n    if (!{n}) {{ {n} = (struct {node}*)lust_alloc(sizeof(struct {node}), _Alignof(struct {node})); {n}->k = {l}; {n}->next = {node}_head; {node}_head = {n}; const char *fp; uint32_t ln; lust_loc_where({l}, &fp, &ln); uint64_t fl = 0; while (fp[fl]) fl++; {n}->v.f0 = (lust_str){{(uint8_t*)fp, fl}}; {n}->v.f1 = ln; {n}->v.f2 = (uint32_t)({l} & 0xFFFFF); }}\n    {ct} *{t} = &{n}->v;"
                );
                t
            }
            B::LocationFile => format!("(*{}).f0", vals[0]),
            B::LocationLine => format!("(*{}).f1", vals[0]),
            B::LocationColumn => format!("(*{}).f2", vals[0]),
            B::Utf8ErrorErrorLen => {
                let p = self.p;
                let (o8, o64) = (CTy::Option(Box::new(CTy::Int(IntTy::U8))), CTy::Option(Box::new(CTy::Int(IntTy::Usize))));
                let src = format!("(*{}).f1", vals[0]);
                let t = self.tmp();
                let disc = disc_call(p, &o8, &format!("&{src}"));
                let (some_f, some_d, none_d) = (variant_field(p, &o64, &t, 1, 0), disc_set(p, &o64, &t, 1), disc_set(p, &o64, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {} {t}; if ({disc}) {{ {some_f} = (uint64_t){}; {some_d} }} else {{ {none_d} }}",
                    ctype(&o64),
                    variant_field(p, &o8, &src, 1, 0)
                );
                t
            }
            B::RcWeakCount => format!("((*{})->weak - 1)", vals[0]),
            B::RcGetMut => {
                let inner = match &tys[0] { CTy::Ref(r) => (**r).clone(), _ => unreachable!() };
                let elem = match &inner { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem.clone()))));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let v = &vals[0];
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ((*{v})->strong == 1 && (*{v})->weak == 1) {{ {field} = {};{some} }}", rc_ptr(&format!("(*{v})"), &elem));
                t
            }
            B::RcMakeMut => {
                let inner = match &tys[0] { CTy::Ref(r) => (**r).clone(), _ => unreachable!() };
                let elem = match &inner { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let it = format!("RcI_{}", mangle(&elem));
                let v = &vals[0];
                // A fresh block's size, and the value moved or cloned into it.
                self.note_held(&elem);
                let (val, size) = (rc_value(&format!("(*{v})"), &elem), rc_size(&it, &elem));
                let n_val = rc_value("n", &elem);
                let cloned = if is_copy_c(self.p, &elem) {
                    val.clone()
                } else {
                    self.want(Glue::Clone, &elem);
                    format!("clone_{}(&{val})", mangle(&elem))
                };
                // Shared: clone the value into a fresh header and leave
                // the old count one lower. Unique but Weak-held: move
                // the value out and let the Weaks keep the old header
                // (strong 0, its implicit weak ref gone), as in Rust.
                let _ = writeln!(
                    self.out,
                    "    if ((*{v})->strong > 1) {{ {it} *n = ({it}*)lust_alloc({size}, _Alignof({it})); n->strong = 1; n->weak = 1; {n_val} = {cloned}; (*{v})->strong--; *{v} = n; }}\n    else if ((*{v})->weak > 1) {{ {it} *n = ({it}*)lust_alloc({size}, _Alignof({it})); n->strong = 1; n->weak = 1; {n_val} = {val}; (*{v})->strong = 0; (*{v})->weak--; *{v} = n; }}"
                );
                rc_ptr(&format!("(*{v})"), &elem)
            }
            B::DefaultGlue => unreachable!("the default glue call is emitted at its call terminator"),
            B::SliceTryInto => unreachable!("the slice-to-array call is emitted at its call terminator"),
            B::VecTryInto => unreachable!("the Vec-to-array call is emitted at its call terminator"),
            B::TlsWith
            | B::TlsTryWith
            | B::TlsWithBorrow
            | B::TlsWithBorrowMut
            | B::TlsSet
            | B::TlsGet
            | B::TlsTake
            | B::TlsReplace
            | B::TlsTryGet
            | B::TlsCloneRc => {
                unreachable!("lower/tls.rs expands LocalKey calls before codegen")
            }
            B::TlsAccess | B::TlsTryAccess | B::TlsInitWith => self.tls_builtin(b, &vals, &tys, loc, &ops[0]),
            B::RcTryUnwrap => {
                let elem = match &tys[0] { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let res = CTy::Result(Box::new(elem.clone()), Box::new(CTy::Rc(Box::new(elem.clone()))));
                let rt = ctype(&res);
                let t = self.tmp();
                let v = &vals[0];
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let et = ctype(&elem);
                let it = format!("RcI_{}", mangle(&elem));
                let _ = writeln!(self.out, "    {rt} {t};");
                let _ = writeln!(
                    self.out,
                    "    if ({v}->strong == 1) {{ {set_ok} {ok_f} = {}; {v}->strong = 0; if (--{v}->weak == 0) lust_rc_free({v}, _Alignof({it})); }} else {{ {set_err} {err_f} = {v}; }}",
                    rc_value(v, &elem)
                );
                let _ = et;
                t
            }
            B::RcIntoInner | B::RcUnwrapOrClone => {
                // The last strong Rc gives up its value (the header stays
                // while Weak refs do); any other just drops its count:
                // into_inner answers None, unwrap_or_clone a clone.
                let CTy::Rc(elem) = &tys[0] else { unreachable!("into_inner on an Rc") };
                let elem = (**elem).clone();
                let it = format!("RcI_{}", mangle(&elem));
                let v = self.tmp();
                let _ = writeln!(self.out, "    {it}* {v} = {};", vals[0]);
                let free = format!("{v}->strong = 0; if (--{v}->weak == 0) lust_rc_free({v}, _Alignof({it}));");
                let val = rc_value(&v, &elem);
                if b == B::RcIntoInner {
                    let opt = CTy::Option(Box::new(elem.clone()));
                    let t = self.tmp();
                    let (f, some, none) = (variant_field(self.p, &opt, &t, 1, 0), disc_set(self.p, &opt, &t, 1), disc_set(self.p, &opt, &t, 0));
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if ({v}->strong == 1) {{ {f} = {val}; {some} {free} }} else {{ {v}->strong--; {none} }}",
                        ctype(&opt)
                    );
                    t
                } else {
                    self.note_held(&elem);
                    let c = if is_copy_c(self.p, &elem) {
                        val.clone()
                    } else {
                        self.want(Glue::Clone, &elem);
                        format!("clone_{}(&{val})", mangle(&elem))
                    };
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {} {t}; if ({v}->strong == 1) {{ {t} = {val}; {free} }} else {{ {t} = {c}; {v}->strong--; }}", ctype(&elem));
                    t
                }
            }
            B::EnvArgs => unreachable!("a dest-typed compound literal in the call dispatch"),
            B::EnvArg => format!("lust_env_arg({}, {})", vals[0], vals[1]),
            B::StrLen => format!("{}.len", vals[0]),
            B::StrIsEmpty => format!("({}.len == 0)", vals[0]),
            B::StrToString => format!("lust_string_from({})", vals[0]),
            B::StringLen | B::VecLen => format!("({})->len", vals[0]),
            B::SliceLen => match &tys[0] {
                CTy::Slice(_) => format!("{}.len", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) => format!("{}.len", vals[0]),
                    _ => format!("({})->len", vals[0]),
                },
                _ => format!("{}.len", vals[0]),
            },
            B::SliceIsEmpty => match &tys[0] {
                CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => format!("({n} == 0)"),
                    CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                    _ => format!("(({})->len == 0)", vals[0]),
                },
                _ => format!("({}.len == 0)", vals[0]),
            },
            B::StringIsEmpty | B::VecIsEmpty => format!("(({})->len == 0)", vals[0]),
            B::StringPushStr => {
                let _ = writeln!(self.out, "    lust_string_push_str({}, {});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringPush => {
                let _ = writeln!(self.out, "    lust_string_push_char({}, {});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringAsStr | B::StringAsMutStr => format!("lust_string_as_str({})", vals[0]),
            B::StringCapacity => format!("({})->cap", vals[0]),
            B::StringReserve | B::StringReserveExact | B::StringShrinkToFit | B::StringShrinkTo => {
                let vv = &vals[0];
                let call = match b {
                    B::StringReserve => format!("lust_string_reserve({vv}, {})", vals[1]),
                    B::StringReserveExact => format!("lust_string_reserve_exact({vv}, {})", vals[1]),
                    B::StringShrinkToFit => format!("lust_string_shrink_to({vv}, 0)"),
                    _ => format!("lust_string_shrink_to({vv}, {})", vals[1]),
                };
                let _ = writeln!(self.out, "    {call};");
                "((lust_Unit){})".into()
            }
            B::StringPop => {
                let t = self.tmp();
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({0}->len) {{ {field} = lust_string_pop({0});{some} }}", vals[0]);
                t
            }
            B::StringRemove => format!("lust_string_remove({}, {}, {loc})", vals[0], vals[1]),
            B::StringInsert => {
                let _ = writeln!(self.out, "    lust_string_insert_char({}, {}, {}, {loc});", vals[0], vals[1], vals[2]);
                "((lust_Unit){})".into()
            }
            B::StringInsertStr => {
                let _ = writeln!(self.out, "    lust_string_insert_bytes({}, {}, ({2}).ptr, ({2}).len, {loc});", vals[0], vals[1], vals[2]);
                "((lust_Unit){})".into()
            }
            B::StringTruncate => {
                let _ = writeln!(self.out, "    lust_string_truncate({}, {}, {loc});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringClear => {
                let _ = writeln!(self.out, "    {}->len = 0;", vals[0]);
                "((lust_Unit){})".into()
            }
            B::CloneInto => {
                // `ToOwned::clone_into` on str (into a String) and on a
                // Copy slice (into a Vec): read the source into
                // temporaries, clear the target (its buffer stays),
                // then copy in, growing as push and extend grow.
                let dst = &vals[1];
                if matches!(&tys[0], CTy::Ref(inner) if **inner == CTy::Str) || matches!(&tys[0], CTy::Str) {
                    let s = self.tmp();
                    let _ = writeln!(self.out, "    lust_str {s} = {}; {dst}->len = 0; lust_string_push_str({dst}, {s});", vals[0]);
                } else {
                    let CTy::Ref(v) = &tys[1] else { unreachable!("clone_into target is a &mut Vec") };
                    let CTy::Vec(e) = &**v else { unreachable!("clone_into target is a &mut Vec") };
                    let et = ctype(e);
                    let (_, sptr, slen) = slice_like(&tys[0], &vals[0]);
                    let (sp, sn, i) = (self.tmp(), self.tmp(), self.tmp());
                    let _ = writeln!(
                        self.out,
                        "    {et} *{sp} = {sptr};\n    uint64_t {sn} = {slen};\n    {dst}->len = 0;\n    lust_vec_reserve({dst}, {sn}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = 0; {i} < {sn}; {i}++) (({et}*){dst}->ptr)[{dst}->len++] = {sp}[{i}];"
                    );
                }
                "((lust_Unit){})".into()
            }
            B::StringSplitOff => format!("lust_string_split_off({}, {}, {loc})", vals[0], vals[1]),
            B::StringAsBytes => {
                let sl = CTy::Slice(Box::new(CTy::Int(IntTy::U8)));
                let (st, t) = (ctype(&sl), self.tmp());
                let _ = writeln!(self.out, "    {st} {t} = {{ {0}->ptr, {0}->len }};", vals[0]);
                t
            }
            B::StringIntoBytes => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = {{ (void*){0}.ptr, {0}.len, {0}.cap }};", vals[0]);
                t
            }
            B::StrStripPrefix | B::StrStripSuffix => {
                let a = str_of(&vals[0], &tys[0]);
                let (sa, sp) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    lust_str {sa} = {a}; lust_str {sp} = {};", vals[1]);
                let t = self.tmp();
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(CTy::Str))));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let (cond, val) = if b == B::StrStripPrefix {
                    (format!("lust_str_starts_with({sa}, {sp})"), format!("(lust_str){{ {sa}.ptr + {sp}.len, {sa}.len - {sp}.len }}"))
                } else {
                    (format!("lust_str_ends_with({sa}, {sp})"), format!("(lust_str){{ {sa}.ptr, {sa}.len - {sp}.len }}"))
                };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {val};{some} }}");
                t
            }
            B::StrTrimStart => format!("lust_str_trim_start({})", str_of(&vals[0], &tys[0])),
            B::StrTrimEnd => format!("lust_str_trim_end({})", str_of(&vals[0], &tys[0])),
            B::StrReplace => format!("lust_str_replace({}, {}, {})", str_of(&vals[0], &tys[0]), vals[1], vals[2]),
            B::StrReplacen => format!("lust_str_replacen({}, {}, {}, {})", str_of(&vals[0], &tys[0]), vals[1], vals[2], vals[3]),
            B::StrIsAscii => {
                let s = str_of(&vals[0], &tys[0]);
                format!("lust_bytes_is_ascii({s}.ptr, {s}.len)")
            }
            B::StrMakeAsciiUppercase | B::StrMakeAsciiLowercase => {
                let (s, i) = (self.tmp(), self.tmp());
                let (lo, hi, d) = if b == B::StrMakeAsciiUppercase { ('a', 'z', "-= 32") } else { ('A', 'Z', "+= 32") };
                let _ = writeln!(
                    self.out,
                    "    lust_str {s} = {};\n    for (uint64_t {i} = 0; {i} < {s}.len; {i}++) if ({s}.ptr[{i}] >= '{lo}' && {s}.ptr[{i}] <= '{hi}') {s}.ptr[{i}] {d};",
                    str_of(&vals[0], &tys[0])
                );
                "((lust_Unit){})".into()
            }
            B::StrEqIgnoreAsciiCase => {
                let s = str_of(&vals[0], &tys[0]);
                format!("lust_bytes_eq_ignore_ascii_case({s}.ptr, {s}.len, {}.ptr, {}.len)", vals[1], vals[1])
            }
            B::StrRepeat => format!("lust_str_repeat({}, {}, {loc})", str_of(&vals[0], &tys[0]), vals[1]),
            B::StrGetRange => {
                // `[T]::get`'s bounds, then both ends on char boundaries.
                let a = str_of(&vals[0], &tys[0]);
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(CTy::Str))));
                self.note_held(&opt);
                let (t, sa, s0, e0) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let bound = |i: &str| format!("({i} == {sa}.len || ({sa}.ptr[{i}] & 0xC0) != 0x80)");
                let _ = writeln!(self.out, "    {} {t}; {} lust_str {sa} = {a};", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint64_t {s0} = 0, {e0} = 0;\n      if (lust_range_bounds_get({sa}.len, {}, {}, {}, {}, &{s0}, &{e0}) && {} && {}) {{ {field} = (lust_str){{ {sa}.ptr + {s0}, {e0} - {s0} }};{some} }} }}",
                    vals[1],
                    vals[2],
                    vals[3],
                    vals[4],
                    bound(&s0),
                    bound(&e0)
                );
                t
            }
            B::StrIsCharBoundary => {
                let sa = self.tmp();
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    lust_str {sa} = {a};");
                format!("({0} <= {sa}.len && ({0} == {sa}.len || ({sa}.ptr[{0}] & 0xC0) != 0x80))", vals[1])
            }
            B::VecPush => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                // The value must be read before `lust_vec_push_slot` can reallocate the
                // buffer: `v.push(v[0])` in one C assignment could read the freed buffer.
                // A whole local or a constant is never in that buffer: it goes straight
                // to the slot, with no copy in between.
                let src = if matches!(&ops[1], Operand::Const(_)) || matches!(&ops[1], Operand::Copy(p) | Operand::Move(p) if p.proj.is_empty()) {
                    vals[1].clone()
                } else {
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {et} {t} = {};", vals[1]);
                    t
                };
                let _ = writeln!(self.out, "    *({et}*)lust_vec_push_slot({}, sizeof({et}), _Alignof({et})) = {src};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::Clone => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                if is_copy_c(self.p, inner) || **inner == CTy::Str {
                    format!("(*{})", vals[0])
                } else if matches!(**inner, CTy::RefCell(_)) {
                    // `RefCell::clone` is `#[track_caller]`: its borrow
                    // panics at this call, which the clone glue (called
                    // without a location) cannot name, so test here.
                    self.want(Glue::Clone, inner);
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    {}* {t} = {}; if ({t}->f0 < 0) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", {loc});",
                        ctype(inner),
                        vals[0]
                    );
                    format!("clone_{}({t})", mangle(inner))
                } else {
                    self.want(Glue::Clone, inner);
                    format!("clone_{}({})", mangle(inner), vals[0])
                }
            }
            B::CloneFrom => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                self.want(Glue::CloneFrom, inner);
                let _ = writeln!(self.out, "    clonefrom_{}({}, {});", mangle(inner), vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::ToString => {
                match tys[0].clone() {
                    CTy::Ref(inner) => self.to_string_value(&inner, &vals[0], loc),
                    // A dyn receiver arrives as the fat value itself
                    // (`Box<dyn Error>::to_string`, F3): spill it so
                    // the fmt shim reads it by address, as a format
                    // argument does.
                    t @ (CTy::Dyn | CTy::BoxDyn | CTy::RcDyn) => {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {};", ctype(&t), vals[0]);
                        self.to_string_value(&t, &format!("(&{tmp})"), loc)
                    }
                    _ => unreachable!(),
                }
            }
            B::WrappingAdd | B::WrappingSub | B::WrappingMul => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let how = match b {
                        B::WrappingAdd => "add",
                        B::WrappingSub => "sub",
                        _ => "mul",
                    };
                    format!("lust_{f}_{how}({}, {})", vals[0], vals[1])
                } else {
                    let c = int_c(it);
                    let op = match b {
                        B::WrappingAdd => "+",
                        B::WrappingSub => "-",
                        _ => "*",
                    };
                    format!("(({c})((uint64_t)({}) {op} (uint64_t)({})))", vals[0], vals[1])
                }
            }
            B::WrappingDiv
            | B::WrappingRem
            | B::WrappingNeg
            | B::WrappingPow
            | B::WrappingShl
            | B::WrappingShr
            | B::WrappingAbs
            | B::CheckedAdd
            | B::CheckedSub
            | B::CheckedMul
            | B::CheckedDiv
            | B::CheckedRem
            | B::CheckedNeg
            | B::CheckedAbs
            | B::CheckedPow
            | B::CheckedShl
            | B::CheckedShr
            | B::SaturatingAdd
            | B::SaturatingSub
            | B::SaturatingMul
            | B::SaturatingDiv
            | B::SaturatingNeg
            | B::SaturatingAbs
            | B::SaturatingPow
            | B::OverflowingAdd
            | B::OverflowingSub
            | B::OverflowingMul
            | B::OverflowingDiv
            | B::OverflowingRem
            | B::OverflowingNeg
            | B::OverflowingAbs
            | B::OverflowingPow
            | B::OverflowingShl
            | B::OverflowingShr
            | B::CountOnes
            | B::CountZeros
            | B::LeadingZeros
            | B::TrailingZeros
            | B::LeadingOnes
            | B::TrailingOnes
            | B::RotateLeft
            | B::RotateRight
            | B::SwapBytes
            | B::ReverseBits
            | B::DivCeil
            | B::DivEuclid
            | B::RemEuclid
            | B::Signum
            | B::IsPositive
            | B::IsNegative
            | B::IsPowerOfTwo
            | B::IsMultipleOf
            | B::NextMultipleOf
            | B::CheckedNextMultipleOf
            | B::UnsignedAbs
            | B::UnboundedShl
            | B::UnboundedShr
            | B::CastSigned
            | B::CastUnsigned
            | B::Isqrt
            | B::CheckedIsqrt
            | B::NextPowerOfTwo
            | B::CheckedNextPowerOfTwo
            | B::Ilog2
            | B::Ilog10
            | B::Ilog
            | B::CheckedIlog2
            | B::CheckedIlog10
            | B::CheckedIlog
            | B::BitWidth
            | B::HighestOne
            | B::LowestOne
            | B::IsolateHighestOne
            | B::IsolateLowestOne
            | B::IntMidpoint
            | B::IntAbsDiff
            | B::StrictAdd
            | B::StrictSub
            | B::StrictMul
            | B::StrictDiv
            | B::StrictRem
            | B::StrictDivEuclid
            | B::StrictRemEuclid
            | B::StrictNeg
            | B::StrictAbs
            | B::StrictPow
            | B::StrictShl
            | B::StrictShr
            | B::MixedCheckedAdd
            | B::MixedCheckedSub
            | B::MixedWrappingAdd
            | B::MixedWrappingSub
            | B::MixedSaturatingAdd
            | B::MixedSaturatingSub
            | B::MixedOverflowingAdd
            | B::MixedOverflowingSub
            | B::MixedStrictAdd
            | B::MixedStrictSub
            | B::CheckedSignedDiff
            | B::CarryingAdd
            | B::BorrowingSub
            | B::CarryingMul
            | B::CarryingMulAdd => self.int_method_c(b, &vals, &tys, loc),
            B::FloatSqrt
            | B::FloatPowi
            | B::FloatPowf
            | B::FloatExp
            | B::FloatLn
            | B::FloatLog
            | B::FloatLog2
            | B::FloatLog10
            | B::FloatMulAdd
            | B::FloatFloor
            | B::FloatCeil
            | B::FloatRound
            | B::FloatTrunc
            | B::FloatFract
            | B::FloatAbs
            | B::FloatSignum
            | B::FloatRecip
            | B::FloatMin
            | B::FloatMax
            | B::FloatIsNan
            | B::FloatIsInfinite
            | B::FloatIsFinite
            | B::FloatIsSignPositive
            | B::FloatIsSignNegative
            | B::FloatToBits
            | B::FloatCopysign
            | B::F32FromBits
            | B::F64FromBits => self.float_method_c(b, &vals, &tys),
            B::CharLenUtf8 => format!("((uint64_t)({0} < 0x80u ? 1 : {0} < 0x800u ? 2 : {0} < 0x10000u ? 3 : 4))", vals[0]),
            B::CharLenUtf16 => format!("((uint64_t)({0} < 0x10000u ? 1 : 2))", vals[0]),
            B::CharEncodeUtf8 | B::CharEncodeUtf16 => {
                let (d, n, t) = (self.tmp(), self.tmp(), self.tmp());
                let dt = ctype(&tys[1]);
                let (helper, sloc) = if b == B::CharEncodeUtf8 {
                    ("lust_char_encode_utf8", std_loc(1, 2518, 9))
                } else {
                    ("lust_char_encode_utf16", std_loc(1, 2612, 13))
                };
                let _ = writeln!(
                    self.out,
                    "    {dt} {d} = {}; uint64_t {n} = {helper}({}, {d}.ptr, {d}.len, {sloc});",
                    vals[1], vals[0]
                );
                if b == B::CharEncodeUtf8 {
                    let _ = writeln!(self.out, "    lust_str {t} = {{ {d}.ptr, {n} }};");
                } else {
                    let _ = writeln!(self.out, "    {dt} {t} = {{ {d}.ptr, {n} }};");
                }
                t
            }
            B::CharIsAscii => format!("(*{0} < 128u)", vals[0]),
            B::CharIsAsciiPunctuation => {
                format!(
                    "(((*{0} >= 33u && *{0} <= 47u) || (*{0} >= 58u && *{0} <= 64u) || (*{0} >= 91u && *{0} <= 96u) || (*{0} >= 123u && *{0} <= 126u)))",
                    vals[0]
                )
            }
            B::CharIsAsciiGraphic => format!("(*{0} >= 33u && *{0} <= 126u)", vals[0]),
            B::CharIsAsciiHexdigit => {
                format!("(((*{0} >= '0' && *{0} <= '9') || ((*{0} | 32) >= 'a' && (*{0} | 32) <= 'f')))", vals[0])
            }
            B::CharIsAsciiControl => format!("(*{0} < 32u || *{0} == 127u)", vals[0]),
            B::CharIsDigitRadix => format!("(lust_digit({}, {}, {}) != 0xFFFFFFFFu)", vals[0], vals[1], std_loc(1, 407, 9)),
            // `abs` and `pow` inherit the caller's overflow checks
            // (`#[rustc_inherit_overflow_checks]`): off, they wrap.
            B::Abs if !self.p.overflow_checks => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    format!("lust_wrapping_abs_i128({})", vals[0])
                } else {
                    format!("(({0}) < 0 ? ({1})(0ull - (uint64_t)({0})) : ({0}))", vals[0], int_c(it))
                }
            }
            B::Pow if !self.p.overflow_checks => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    format!("lust_wrapping_pow_{}({}, {})", int_fn(it), vals[0], vals[1])
                } else {
                    format!("(({})lust_wrapping_pow((uint64_t)({}), {}, {}))", int_c(it), vals[0], vals[1], it.bits())
                }
            }
            B::Abs => format!("lust_abs_{}({}, {})", int_fn(int_of(&tys[0])), vals[0], num_loc(int_of(&tys[0]), false)),
            B::Pow => format!("lust_pow_{}({}, {}, {})", int_fn(int_of(&tys[0])), vals[0], vals[1], num_loc(int_of(&tys[0]), true)),
            B::Min | B::Max => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let rel = if b == B::Min { "<" } else { ">" };
                    format!("(lust_{f}_cmp({0}, {1}) {rel} 0 ? {0} : {1})", vals[0], vals[1])
                } else if b == B::Min {
                    format!("({0} < {1} ? {0} : {1})", vals[0], vals[1])
                } else {
                    format!("({0} > {1} ? {0} : {1})", vals[0], vals[1])
                }
            }
            B::CmpCode | B::PCmpCode => {
                let (g, pre) = if b == B::PCmpCode { (Glue::PCmp, "pcmp") } else { (Glue::Cmp, "cmp") };
                // Both operands are references to the compared type (a
                // slice operand is the fat value itself).
                let (t, a, b) = match &tys[0] {
                    CTy::Slice(_) => (tys[0].clone(), format!("(&{})", vals[0]), format!("(&{})", vals[1])),
                    CTy::Ref(inner) => ((**inner).clone(), vals[0].clone(), vals[1].clone()),
                    other => (other.clone(), format!("(&{})", vals[0]), format!("(&{})", vals[1])),
                };
                self.want(g, &t);
                format!("{pre}_{}({a}, {b})", mangle(&t))
            }
            // `vec::IntoIter` (W-STD-A): the moved-in buffer, then
            // `next` and `next_back` take from `front..len`.
            B::IterVecIntoIter => format!("((lust_VecIter){{ {0}.ptr, {0}.len, {0}.cap, 0 }})", vals[0]),
            B::VecIterLen => format!("({0}->len - {0}->front)", vals[0]),
            B::VecIterCap => {
                let CTy::Ref(it) = &tys[0] else { unreachable!("vec::IntoIter cap takes &lust_VecIter") };
                let CTy::VecIter(e) = &**it else { unreachable!("vec::IntoIter cap takes &lust_VecIter") };
                vec_cap(&ctype(e), &vals[0])
            }
            B::VecIterFront => format!("({0}->front)", vals[0]),
            B::CharsBytesLeft => format!("({0}->s.len - {0}->pos)", vals[0]),
            B::VecIterNext | B::VecIterNextBack => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecIter(e) => (**e).clone(),
                        _ => unreachable!("vec::IntoIter next takes &mut lust_VecIter"),
                    },
                    _ => unreachable!("vec::IntoIter next takes &mut lust_VecIter"),
                };
                let opt = CTy::Option(Box::new(e.clone()));
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let idx = if b == B::VecIterNext { format!("{v}->front++") } else { format!("--{v}->len") };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    if ({v}->front < {v}->len) {{ {field} = (({}*){v}->ptr)[{idx}];{some} }}", ctype(&e));
                t
            }
            // The drains: construction checks the range in the
            // runtime; `next` and `next_back` take from `front..back`
            // of the drained buffer (as `vec::Drain` and
            // `string::Drain`).
            // Only flag-mode unwinding (panic=unwind without unwind tables) needs the drains'
            // check of a panic left pending by the range check; elsewhere a panic never returns.
            B::VecDrain | B::StringDrain => {
                let f = if matches!(b, B::VecDrain) { "lust_vec_drain" } else { "lust_string_drain" };
                let t = if self.p.unwind && !self.p.unwind_tables { "" } else { "_t" };
                format!("{f}{t}({}, {}, {}, {}, {}, {loc})", vals[0], vals[1], vals[2], vals[3], vals[4])
            }
            B::VecDrainLen => format!("({0}->back - {0}->front)", vals[0]),
            B::VecDrainNext | B::VecDrainNextBack => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecDrain(e) => (**e).clone(),
                        _ => unreachable!("vec::Drain next takes &mut lust_VecDrain"),
                    },
                    _ => unreachable!("vec::Drain next takes &mut lust_VecDrain"),
                };
                let opt = CTy::Option(Box::new(e.clone()));
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let idx = if b == B::VecDrainNext { format!("{v}->front++") } else { format!("--{v}->back") };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(
                    self.out,
                    "    if ({v}->front < {v}->back) {{ {field} = (({}*)((lust_Vec*){v}->vec)->ptr)[{idx}];{some} }}",
                    ctype(&e)
                );
                t
            }
            B::VecDrainAsSlice => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecDrain(e) => (**e).clone(),
                        _ => unreachable!("vec::Drain as_slice takes &lust_VecDrain"),
                    },
                    _ => unreachable!("vec::Drain as_slice takes &lust_VecDrain"),
                };
                let et = ctype(&e);
                let sl = CTy::Slice(Box::new(e));
                let (st, t) = (ctype(&sl), self.tmp());
                let vv = &vals[0];
                let _ = writeln!(self.out, "    {st} {t} = {{ (({et}*)((lust_Vec*){vv}->vec)->ptr) + {vv}->front, {vv}->back - {vv}->front }};");
                t
            }
            B::StrDrainNext | B::StrDrainNextBack => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                if b == B::StrDrainNext {
                    let _ = writeln!(
                        self.out,
                        "    if ({it}->front < {it}->back) {{ {field} = lust_utf8_next(((lust_String*){it}->vec)->ptr, &{it}->front);{some} }}"
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    if ({it}->front < {it}->back) {{ {field} = lust_utf8_prev(((lust_String*){it}->vec)->ptr, &{it}->back);{some} }}"
                    );
                }
                t
            }
            B::StrDrainAsStr => {
                let (t, vv) = (self.tmp(), &vals[0]);
                let _ = writeln!(self.out, "    lust_str {t} = {{ ((lust_String*){vv}->vec)->ptr + {vv}->front, {vv}->back - {vv}->front }};");
                t
            }
            // Expanded into plain IR before codegen (lower/iter.rs).
            B::IterLen | B::RangeStartBound | B::RangeEndBound | B::BoundAsRef | B::BoundMap | B::BoundCloned | B::RangeIsEmpty | B::RangeContains | B::RangeInclStart | B::RangeInclEnd => {
                unreachable!("iterator expansion left a builtin for codegen")
            }
            // `Rc` weak refs, `RefCell`, and `Cell` (W-STD-A, check/cells.rs).
            // The `RcI` header keeps Rust's counts: `weak` includes the one
            // implicit weak ref the strong refs hold; `Weak::new()` is the
            // dangling `UINTPTR_MAX` pointer.
            B::RcDowngrade => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = *{}; {t}->weak++;", ctype(&deref_cty(&tys[0])), vals[0]);
                t
            }
            // `Rc<dyn Tr>`: the addresses, not the vtables (ptr::addr_eq).
            B::RcPtrEq if matches!(&tys[0], CTy::Ref(r) if **r == CTy::RcDyn) => format!("((*{}).data == (*{}).data)", vals[0], vals[1]),
            B::RcPtrEq | B::WeakPtrEq => format!("(*{} == *{})", vals[0], vals[1]),
            B::WeakNew => "((void*)~(uint64_t)0)".into(),
            // std: the value's address, or the dangling sentinel itself.
            B::WeakAsPtr => {
                let w = self.tmp();
                let _ = writeln!(self.out, "    {} {w} = *{};", ctype(&deref_cty(&tys[0])), vals[0]);
                format!("({w} == (void*)~(uint64_t)0 ? (void*)~(uint64_t)0 : (void*)&{w}->v)")
            }
            B::WeakUpgrade => {
                let w = deref_cty(&tys[0]);
                let CTy::Weak(e) = &w else { unreachable!("Weak::upgrade on a Weak") };
                let opt = CTy::Option(Box::new(CTy::Rc(e.clone())));
                self.note_held(&opt);
                let (t, p) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {} {p} = *{}; if ({p} != (void*)~(uint64_t)0 && {p}->strong > 0) {{ {p}->strong++; {field} = {p}; {some} }}",
                    ctype(&w),
                    vals[0]
                );
                t
            }
            B::WeakStrongCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : (*{0})->strong)", vals[0]),
            B::WeakWeakCount => format!("(*{0} == (void*)~(uint64_t)0 || (*{0})->strong == 0 ? (uint64_t)0 : (*{0})->weak - 1)", vals[0]),
            B::RefCellNew => {
                let t = self.tmp();
                let rc = CTy::RefCell(Box::new(tys[0].clone()));
                self.note_held(&rc);
                let _ = writeln!(self.out, "    {} {t}; {t}.f0 = 0; {t}.f1 = {};", ctype(&rc), vals[0]);
                t
            }
            B::RefCellBorrow => {
                let t = self.tmp();
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {t} = {}; if ({t}->f0 < 0 || {t}->f0 == 0x7fffffffffffffffLL) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", {loc}); {t}->f0++;",
                    ctype(&rc),
                    vals[0]
                );
                t
            }
            B::RefCellBorrowMut => {
                let t = self.tmp();
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {t} = {}; if ({t}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {loc}); {t}->f0 = -1;",
                    ctype(&rc),
                    vals[0]
                );
                t
            }
            // `try_borrow` (`try_borrow_mut`): `borrow`'s flag test, the
            // guard in `Ok`, else `Err` of the unit error struct (W-STD-B).
            B::RefCellTryBorrow | B::RefCellTryBorrowMut => {
                let m = b == B::RefCellTryBorrowMut;
                let rc = deref_cty(&tys[0]);
                let CTy::RefCell(el) = &rc else { unreachable!("try_borrow on a &RefCell") };
                let def = if m { crate::check::generics::borrow_mut_error_def() } else { crate::check::generics::borrow_error_def() };
                let err = CTy::Adt(self.p.tys.local_adt_of(def).expect("the RefCell error Adts always exist"));
                let res = CTy::Result(Box::new(CTy::Guard(el.clone(), m)), Box::new(err.clone()));
                self.note_held(&res);
                let (p, t) = (self.tmp(), self.tmp());
                let ok = self.make_variant(&res, 0, std::slice::from_ref(&p));
                let fail = self.make_variant(&res, 1, &[zero_lit(self.p, &err)]);
                let (busy, take) = if m {
                    (format!("{p}->f0 != 0"), format!("{p}->f0 = -1"))
                } else {
                    (format!("{p}->f0 < 0 || {p}->f0 == 0x7fffffffffffffffLL"), format!("{p}->f0++"))
                };
                let _ = writeln!(
                    self.out,
                    "    {}* {p} = {}; {} {t}; if ({busy}) {t} = {fail}; else {{ {take}; {t} = {ok}; }}",
                    ctype(&rc),
                    vals[0],
                    ctype(&res)
                );
                t
            }
            B::RefCellIntoInner => format!("{}.f1", vals[0]),
            B::RefCellReplace => {
                let (c, old) = (self.tmp(), self.tmp());
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {c} = {}; if ({c}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {loc}); {} {old} = {c}->f1; {c}->f1 = {};",
                    ctype(&rc),
                    vals[0],
                    ctype(&tys[1]),
                    vals[1]
                );
                old
            }
            B::RefCellSwap => {
                let (a, bb, tmp) = (self.tmp(), self.tmp(), self.tmp());
                let rc = deref_cty(&tys[0]);
                let CTy::RefCell(e) = &rc else { unreachable!("RefCell::swap on a RefCell") };
                let _ = writeln!(
                    self.out,
                    "    {rt}* {a} = {}; {rt}* {bb} = {}; if ({a}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {la}); {a}->f0 = -1; if ({bb}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {lb}); {et} {tmp} = {a}->f1; {a}->f1 = {bb}->f1; {bb}->f1 = {tmp}; {a}->f0 = 0;",
                    vals[0],
                    vals[1],
                    rt = ctype(&rc),
                    et = ctype(e),
                    // `swap` is not track_caller: its two `borrow_mut`s panic in cell.rs.
                    la = std_loc(9, 1083, 30),
                    lb = std_loc(9, 1083, 56)
                );
                "((lust_Unit){})".into()
            }
            B::RefCellGetMut => format!("(&({})->f1)", vals[0]),
            B::CellNew | B::CellIntoInner => vals[0].clone(),
            B::CellGet => format!("(*{})", vals[0]),
            B::CellGetMut => vals[0].clone(),
            B::CellTake | B::RefCellTake => {
                // `replace(T::default())` (core); RefCell's panics if borrowed.
                let CTy::Ref(cell) = &tys[0] else { unreachable!("take on a &Cell") };
                let el = match &**cell {
                    CTy::Cell(e) | CTy::RefCell(e) => (**e).clone(),
                    _ => unreachable!("take on a cell"),
                };
                let def = match &el {
                    CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(self.p, &el),
                    t => {
                        self.want(Glue::Default, t);
                        format!("default_{}()", mangle(t))
                    }
                };
                let (c, old) = (self.tmp(), self.tmp());
                let et = ctype(&el);
                if b == B::RefCellTake {
                    let _ = writeln!(
                        self.out,
                        "    {}* {c} = {}; if ({c}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {}); {et} {old} = {c}->f1; {c}->f1 = {def};",
                        ctype(cell),
                        vals[0],
                        // `take` is not track_caller: its `replace` panics in cell.rs.
                        std_loc(9, 1434, 14)
                    );
                } else {
                    let _ = writeln!(self.out, "    {et}* {c} = {}; {et} {old} = *{c}; *{c} = {def};", vals[0]);
                }
                old
            }
            B::CellSet | B::CellReplace => {
                let (c, old) = (self.tmp(), self.tmp());
                let et = ctype(&tys[1]);
                let _ = writeln!(self.out, "    {et}* {c} = {}; {et} {old} = *{c}; *{c} = {};", vals[0], vals[1]);
                if b == B::CellReplace {
                    return old;
                }
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(self.out, "    drop_{}(&{old});", mangle(&tys[1]));
                }
                "((lust_Unit){})".into()
            }
            B::CellSwap => {
                let (a, bb, tmp) = (self.tmp(), self.tmp(), self.tmp());
                let et = match deref_cty(&tys[0]) {
                    CTy::Cell(e) => ctype(&e),
                    other => ctype(&other),
                };
                let _ = writeln!(
                    self.out,
                    "    {et}* {a} = {}; {et}* {bb} = {}; if ({a} != {bb}) {{ {et} {tmp} = *{a}; *{a} = *{bb}; *{bb} = {tmp}; }}",
                    vals[0],
                    vals[1]
                );
                "((lust_Unit){})".into()
            }
            // The sort family (W-STD-A, runtime/sort.h): a comparator
            // adapter per call site, then Rust 1.99's driftsort or
            // ipnsort over the element bytes.
            B::SliceSort | B::SliceSortUnstable | B::SliceSortBy | B::SliceSortUnstableBy | B::SliceSortByKey | B::SliceSortUnstableByKey => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (size, align) = c_size_align(self.p, &e);
                let clo = ops.get(1).map(|o| self.adapter_callee(o));
                let adapter = self.sort_adapter(b, &e, clo);
                let ctx = match (vals.get(1), tys.get(1)) {
                    (Some(v), Some(t)) => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {v};", ctype(t));
                        Some((c, t.clone()))
                    }
                    _ => None,
                };
                let cx = ctx.as_ref().map_or("0".to_string(), |(c, _)| format!("(void*)&{c}"));
                // Rust picks the small sort by Copy-ness and freeze-ness
                // (no Cell or RefCell inline).
                let freeze = u8::from(is_freeze_c(self.p, &e, &mut HashSet::new()));
                if matches!(b, B::SliceSort | B::SliceSortBy | B::SliceSortByKey) {
                    let _ = writeln!(self.out, "    lust_sort_stable({ptr}, {len}, {size}, {align}, {freeze}, {cx}, {adapter});");
                } else {
                    let copy = u8::from(is_copy_c(self.p, &e));
                    let _ = writeln!(self.out, "    lust_sort_unstable({ptr}, {len}, {size}, {align}, {freeze}, {copy}, {cx}, {adapter});");
                }
                if let Some((c, t)) = ctx
                    && needs_drop_c(self.p, &t)
                {
                    self.want(Glue::Drop, &t);
                    let _ = writeln!(self.out, "    drop_{}(&{c});", mangle(&t));
                }
                "((lust_Unit){})".into()
            }
            B::SliceBinarySearch | B::SliceBinarySearchBy | B::SliceBinarySearchByKey => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let size = c_size_align(self.p, &e).0;
                let clo = match b {
                    B::SliceBinarySearchBy => Some(self.adapter_callee(&ops[1])),
                    B::SliceBinarySearchByKey => Some(self.adapter_callee(&ops[2])),
                    _ => None,
                };
                let adapter = self.search_adapter(b, &e, clo);
                let cx = match b {
                    B::SliceBinarySearch => format!("(void*){}", vals[1]),
                    B::SliceBinarySearchBy => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                        format!("(void*)&{c}")
                    }
                    _ => {
                        let (c, k) = (self.tmp(), self.tmp());
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[2]), vals[2]);
                        let _ = writeln!(self.out, "    void *{k}[2] = {{ (void*)&{c}, (void*){} }};", vals[1]);
                        format!("(void*){k}")
                    }
                };
                let r = self.tmp();
                let _ = writeln!(self.out, "    int64_t {r} = lust_binary_search({ptr}, {len}, {size}, {cx}, {adapter});");
                let res = CTy::Result(Box::new(CTy::Int(IntTy::Usize)), Box::new(CTy::Int(IntTy::Usize)));
                self.note_held(&res);
                let t = self.tmp();
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (set_ok, set_err) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                let _ = writeln!(self.out, "    {} {t};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if ({r} >= 0) {{ {set_ok} {ok_f} = (uint64_t){r}; }} else {{ {set_err} {err_f} = (uint64_t)(-{r} - 1); }}"
                );
                t
            }
            B::IterIter
            | B::IterIterMut
            | B::IterNext
            | B::IterMap
            | B::IterFilter
            | B::IterFilterMap
            | B::IterEnumerate
            | B::IterRev
            | B::IterTake
            | B::IterSkip
            | B::IterStepBy
            | B::IterChain
            | B::IterZip
            | B::IterCopied
            | B::IterCloned
            | B::IterTakeWhile
            | B::IterMapWhile
            | B::IterSkipWhile
            | B::IterPeekable
            | B::IterPeek
            | B::IterNextIf
            | B::IterNextIfEq
            | B::IterInspect
            | B::IterCount
            | B::IterEq
            | B::IterNe
            | B::IterLast
            | B::IterNth
            | B::IterAny
            | B::IterAll
            | B::IterFind
            | B::IterFindMap
            | B::IterPosition
            | B::IterRposition
            | B::IterWindows
            | B::IterChunks
            | B::IterSliceSplit
            | B::IterChunkBy
            | B::IterUtf8Chunks
            | B::IterRemainder
            | B::IterFlatten
            | B::IterFlattenInto
            | B::IterFlatMap
            | B::HashFromArray
            | B::DlEntries
            | B::DmEntries
            | B::StrSplit
            | B::IterSizeHint
            | B::IterNextBack
            | B::StrCharIndices
            | B::StrBytes
            | B::IterFold
            | B::IterTryFold
            | B::IterForEach
            | B::IterPartition
            | B::IterUnzip
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
            | B::FromIter
            | B::IterSum
            | B::IterProduct
            | B::IterOptRes => unreachable!("iterator builtins are expanded before codegen (lower/iter.rs)"),
            B::VecPop | B::VecGet | B::VecFirst | B::VecLast | B::VecGetMut | B::VecFirstMut | B::VecLastMut => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (opt, r) = if b == B::VecPop {
                    (CTy::Option(Box::new(e.clone())), "")
                } else {
                    (CTy::Option(Box::new(CTy::Ref(Box::new(e.clone())))), "&")
                };
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let (cond, idx) = match b {
                    B::VecPop => (format!("{len} > 0"), format!("--{v}->len")),
                    B::VecGet | B::VecGetMut => (format!("{} < {len}", vals[1]), vals[1].clone()),
                    B::VecFirst | B::VecFirstMut => (format!("{len} > 0"), "0".into()),
                    _ => (format!("{len} > 0"), format!("{len} - 1")),
                };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                // Release C: the element reference is never null, so the niche check that reads
                // the Option back folds (`lust_ref_nn`, runtime/inl.h).
                let nn = if !r.is_empty() && names::release() { format!(" lust_ref_nn({field});") } else { String::new() };
                let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {r}{ptr}[{idx}];{nn}{some} }}");
                t
            }
            // A byte (u8 or i8) is memchr's search, as std's SliceContains specialization.
            B::VecContains if matches!(slice_like(&tys[0], &vals[0]).0, CTy::Int(IntTy::U8 | IntTy::I8)) => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                format!("(lust_memchr((uint32_t)*(const uint8_t *){}, (const uint8_t *){ptr}, {len}) != 18446744073709551615ull)", vals[1])
            }
            B::VecContains => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, i) = (self.tmp(), self.tmp());
                let elem = format!("(&{ptr}[{i}])");
                let eq = self.eq_expr(&e, &elem, &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    uint8_t {t} = 0;\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) if ({eq}) {{ {t} = 1; break; }}"
                );
                t
            }
            B::VecSwap => {
                // `Vec::swap` and `[T]::swap` share the builtin:
                // `slice_like` reads either receiver form.
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (et, t) = (ctype(&e), self.tmp());
                let (a, bb) = (&vals[1], &vals[2]);
                let _ = writeln!(
                    self.out,
                    "    lust_bounds({a}, {len}, {loc}); lust_bounds({bb}, {len}, {loc});\n    {et} {t} = {ptr}[{a}]; {ptr}[{a}] = {ptr}[{bb}]; {ptr}[{bb}] = {t};"
                );
                "((lust_Unit){})".into()
            }
            B::SliceStartsWith | B::SliceEndsWith => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, nptr, nlen) = slice_like(&tys[1], &vals[1]);
                let (t, i, off) = (self.tmp(), self.tmp(), self.tmp());
                let elem_a = format!("(&{ptr}[{off} + {i}])");
                let elem_b = format!("(&{nptr}[{i}])");
                let eq = self.eq_expr(&e, &elem_a, &elem_b);
                let off_expr = if b == B::SliceStartsWith { "0".to_string() } else { format!("{len} - {nlen}") };
                let _ = writeln!(
                    self.out,
                    "    uint64_t {off} = {nlen} <= {len} ? ({off_expr}) : 0;\n    uint8_t {t} = {nlen} <= {len};\n    for (uint64_t {i} = 0; {t} && {i} < {nlen}; {i}++) if (!({eq})) {{ {t} = 0; break; }}"
                );
                t
            }
            B::SliceFill => {
                // Core `clone_from`s into every element but the
                // last, which takes the value itself; an empty
                // slice drops the value. The clonefrom glue is
                // core's body per type (buffer reuse included).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let (tv, i) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {tv} = {};", vals[1]);
                if is_copy_c(self.p, &e) {
                    let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {ptr}[{i}] = {tv};");
                } else {
                    self.want(Glue::CloneFrom, &e);
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = 0; {i} + 1 < {len}; {i}++) clonefrom_{}(&{ptr}[{i}], &{tv});",
                        mangle(&e)
                    );
                    if needs_drop_c(self.p, &e) {
                        self.want(Glue::Drop, &e);
                        let jm = mangle(&e);
                        let _ = writeln!(
                            self.out,
                            "    if ({len} > 0) {{ drop_{jm}(&{ptr}[{len} - 1]); {ptr}[{len} - 1] = {tv}; }} else {{ drop_{jm}(&{tv}); }}"
                        );
                    } else {
                        let _ = writeln!(self.out, "    if ({len} > 0) {ptr}[{len} - 1] = {tv};");
                    }
                }
                "((lust_Unit){})".into()
            }
            // core's non-`TrivialClone` `clone_from_slice`: the length
            // assert, then `self[i].clone_from(&src[i])` in order.
            B::SliceCloneFromSlice => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, sptr, slen) = slice_like(&tys[1], &vals[1]);
                self.want(Glue::CloneFrom, &e);
                let i = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    if ({slen} != {len}) lust_panic_cstr(\"destination and source slices have different lengths\", {loc});\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) clonefrom_{}(&{ptr}[{i}], &{sptr}[{i}]);",
                    mangle(&e)
                );
                "((lust_Unit){})".into()
            }
            // The length assert, then one memcpy (T is Copy, and a `&mut` and a `&` slice
            // cannot overlap), as core's `copy_nonoverlapping`. An element loop made a
            // `[u8; 8]` copy 8 byte stores, and the next 8-byte read of the bytes stalled on
            // store forwarding; the C compiler makes a memcpy of a known length one move.
            // A zero-sized T copies nothing.
            B::SliceCopyFromSlice => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, sptr, slen) = slice_like(&tys[1], &vals[1]);
                let copy = if c_size_align(self.p, &e).0 == 0 {
                    String::new()
                } else {
                    format!("\n    lust_memcpy({ptr}, {sptr}, {len} * sizeof({}));", ctype(&e))
                };
                let _ = writeln!(
                    self.out,
                    "    if ({slen} != {len}) lust_panic_nn(\"copy_from_slice: source slice length (\", {slen}, \") does not match destination slice length (\", {len}, \")\", {loc});{copy}"
                );
                "((lust_Unit){})".into()
            }
            B::SliceEqIgnoreAsciiCase
            | B::SliceIsAscii
            | B::SliceRotateLeft
            | B::SliceRotateRight
            | B::SlicePartitionPoint
            | B::VecExtendFromWithin
            | B::VecDedupBy
            | B::VecDedupByKey
            | B::SpliceBegin
            | B::SpliceReserve
            | B::SpliceGap
            | B::SplicePut
            | B::SpliceMoveTail => unreachable!("emitted by cgen/slices.rs"),
            B::VecSplice => unreachable!("expanded in lower/iter.rs"),
            B::VecResizeWith => unreachable!("expanded in lower/iter.rs"),
            B::SliceCopyWithin => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let _ = writeln!(
                    self.out,
                    "    lust_slice_copy_within({ptr}, {len}, sizeof({et}), {}, {}, {}, {}, {}, {loc});",
                    vals[1], vals[2], vals[3], vals[4], vals[5]
                );
                "((lust_Unit){})".into()
            }
            B::SliceGetRange | B::SliceGetRangeMut => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let sl = CTy::Slice(Box::new(e));
                let opt = CTy::Option(Box::new(sl.clone()));
                self.note_held(&opt);
                let (t, s0, e0) = (self.tmp(), self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint64_t {s0} = 0, {e0} = 0;\n      if (lust_range_bounds_get({len}, {}, {}, {}, {}, &{s0}, &{e0})) {{ {field} = ({}){{ {ptr} + {s0}, {e0} - {s0} }};{some} }} }}",
                    vals[1],
                    vals[2],
                    vals[3],
                    vals[4],
                    ctype(&sl)
                );
                t
            }
            B::SliceJoinStr | B::SliceConcatStr => {
                // Core's exact capacity: the sum of the parts (and
                // separators) is reserved once, then copied in.
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                // `Box<str>`, `Rc<str>`, and `Arc<str>` are the fat `str`
                // value itself; a `Cow<str>` views its variant.
                let view = |el: &str| -> String {
                    match &e {
                        CTy::String => format!("lust_string_as_str(&{el})"),
                        CTy::Adt(_) => fmt::cow_view_expr(self.p, &e, &format!("(&{el})")).expect("a Cow<str> part").1,
                        _ => el.to_string(),
                    }
                };
                let (t, i, tot) = (self.tmp(), self.tmp(), self.tmp());
                let sep = if b == B::SliceJoinStr { vals[1].clone() } else { "((lust_str){ (const uint8_t*)\"\", 0 })".to_string() };
                let _ = writeln!(
                    self.out,
                    "    uint64_t {tot} = 0;\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) {tot} += {}.len;\n    if ({len} > 1) {tot} += ({sep}).len * ({len} - 1);\n    lust_String {t} = lust_string_with_capacity({tot});\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) {{ if ({i}) lust_string_push_str(&{t}, {sep}); lust_string_push_str(&{t}, {}); }}",
                    view(&format!("{ptr}[{i}]")),
                    view(&format!("{ptr}[{i}]"))
                );
                t
            }
            B::SliceConcatVec | B::SliceJoinVecElem | B::SliceJoinVecSlice => {
                // The `Vec<T>` join/concat family: with_capacity of
                // the exact total, then each part cloned in order
                // (separators interleaved, as core's extend does).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let inner = match &e {
                    CTy::Vec(i) | CTy::Slice(i) | CTy::BoxSlice(i) | CTy::Array(i, _) => (**i).clone(),
                    _ => unreachable!(),
                };
                let iet = ctype(&inner);
                // The (data, len) C text of one part element.
                let part = |el: &str| -> (String, String) {
                    match &e {
                        CTy::Vec(_) => (format!("(({iet}*){el}.ptr)"), format!("{el}.len")),
                        CTy::Array(_, n) => (format!("{el}.v"), format!("((uint64_t){n})")),
                        _ => (format!("{el}.ptr"), format!("{el}.len")),
                    }
                };
                let copy_inner = is_copy_c(self.p, &inner);
                let cloned = |src: String| -> String {
                    if copy_inner {
                        src
                    } else {
                        format!("clone_{}(&{src})", mangle(&inner))
                    }
                };
                if !copy_inner {
                    self.want(Glue::Clone, &inner);
                }
                let (t, i, j, tot) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let (sp1, sl1) = part(&format!("{ptr}[{i}]"));
                let mut body = String::new();
                let _ = writeln!(body, "    uint64_t {tot} = 0;");
                let _ = writeln!(body, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {tot} += {sl1};");
                match b {
                    B::SliceJoinVecElem => {
                        let _ = writeln!(body, "    if ({len} > 1) {tot} += {len} - 1;");
                    }
                    B::SliceJoinVecSlice => {
                        let (_, _, seplen) = slice_like(&tys[1], &vals[1]);
                        let _ = writeln!(body, "    if ({len} > 1) {tot} += ({seplen}) * ({len} - 1);");
                    }
                    _ => {}
                }
                let _ = writeln!(body, "    lust_Vec {t} = lust_vec_with_capacity({tot}, sizeof({iet}), _Alignof({iet}));");
                let _ = writeln!(body, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {{");
                match b {
                    B::SliceJoinVecElem => {
                        let sepv = if copy_inner {
                            format!("(*{})", vals[1])
                        } else {
                            format!("clone_{}({})", mangle(&inner), vals[1])
                        };
                        let _ = writeln!(body, "      if ({i}) (({iet}*){t}.ptr)[{t}.len++] = {sepv};");
                    }
                    B::SliceJoinVecSlice => {
                        let (_, sepptr, seplen) = slice_like(&tys[1], &vals[1]);
                        let sj = self.tmp();
                        let _ = writeln!(
                            body,
                            "      if ({i}) for (uint64_t {sj} = 0; {sj} < {seplen}; {sj}++) (({iet}*){t}.ptr)[{t}.len++] = {};",
                            cloned(format!("{sepptr}[{sj}]"))
                        );
                    }
                    _ => {}
                }
                let _ = writeln!(
                    body,
                    "      for (uint64_t {j} = 0; {j} < {sl1}; {j}++) (({iet}*){t}.ptr)[{t}.len++] = {};\n    }}",
                    cloned(format!("{sp1}[{j}]"))
                );
                let _ = write!(self.out, "{body}");
                t
            }
            B::VecClear | B::VecTruncate => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let n = if b == B::VecClear { "0".to_string() } else { vals[1].clone() };
                let vv = &vals[0];
                if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    let i = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = {n}; {i} < {vv}->len; {i}++) drop_{}(&(({}*){vv}->ptr)[{i}]);",
                        mangle(e),
                        ctype(e)
                    );
                }
                let _ = writeln!(self.out, "    if ({n} < {vv}->len) {vv}->len = {n};");
                "((lust_Unit){})".into()
            }
            B::VecInsert => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (ti, tx) = (self.tmp(), self.tmp());
                let (vv, i, x) = (&vals[0], &vals[1], &vals[2]);
                // Read the index and the value before the shift: both can
                // read the Vec itself, as in `v.insert(0, v[1])`.
                let _ = writeln!(self.out, "    uint64_t {ti} = {i}; {et} {tx} = {x};");
                if self.p.unwind_tables {
                    // A bad index panics with the value still owned by `insert`: a guard
                    // drops it as the panic unwinds.
                    let (gd, gdis) = self.zc_guard(&tx, e);
                    let _ = writeln!(
                        self.out,
                        "    {{{gd}\n    lust_vec_insert_at({vv}, {ti}, sizeof({et}), _Alignof({et}), {loc});{gdis} }}\n    (({et}*){vv}->ptr)[{ti}] = {tx};"
                    );
                    return "((lust_Unit){})".into();
                }
                if self.p.unwind {
                    // A bad index panics with the value still owned by
                    // `insert`, which drops it as it unwinds.
                    let drop_x = self.unw_cleanup_drop(&tx, e);
                    let _ = writeln!(self.out, "    if ({ti} > {vv}->len) {{ (void)(lust_vec_insert_at({vv}, {ti}, sizeof({et}), _Alignof({et}), {loc}), 0);{drop_x} }} else {{");
                }
                let _ = writeln!(self.out, "    lust_vec_insert_at({vv}, {ti}, sizeof({et}), _Alignof({et}), {loc});\n    (({et}*){vv}->ptr)[{ti}] = {tx};");
                if self.p.unwind {
                    let _ = writeln!(self.out, "    }}");
                }
                "((lust_Unit){})".into()
            }
            B::VecRemove => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, i) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    lust_vec_check_remove({vv}, {i}, {loc});\n    {et} {t} = (({et}*){vv}->ptr)[{i}];\n    lust_vec_remove_at({vv}, {i}, sizeof({et}));"
                );
                t
            }
            B::VecCapacity => {
                let CTy::Ref(v) = &tys[0] else { unreachable!("capacity takes &Vec") };
                let CTy::Vec(e) = &**v else { unreachable!("capacity takes &Vec") };
                vec_cap(&ctype(e), &vals[0])
            }
            B::VecReserve | B::VecReserveExact | B::VecShrinkToFit | B::VecShrinkTo => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let call = match b {
                    B::VecReserve => format!("lust_vec_reserve({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                    B::VecReserveExact => format!("lust_vec_reserve_exact({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                    B::VecShrinkToFit => format!("lust_vec_shrink_to({vv}, 0, sizeof({et}), _Alignof({et}))"),
                    _ => format!("lust_vec_shrink_to({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                };
                let _ = writeln!(self.out, "    {call};");
                "((lust_Unit){})".into()
            }
            B::VecSwapRemove => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, i) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    if ({i} >= {vv}->len) lust_panic_nn(\"swap_remove index (is \", {i}, \") should be < len (is \", {vv}->len, \")\", {});\n    {et} {t} = (({et}*){vv}->ptr)[{i}];\n    (({et}*){vv}->ptr)[{i}] = (({et}*){vv}->ptr)[{vv}->len - 1];\n    {vv}->len--;",
                    std_loc(3, 2258, 13)
                );
                t
            }
            B::VecAppend => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (vv, o) = (&vals[0], &vals[1]);
                let n = self.tmp();
                // Elements move bitwise; the source keeps its
                // buffer and capacity with length 0, as in Rust.
                let _ = writeln!(
                    self.out,
                    "    uint64_t {n} = {o}->len;\n    lust_vec_reserve({vv}, {n}, sizeof({et}), _Alignof({et}));\n    memcpy(({et}*){vv}->ptr + {vv}->len, {o}->ptr, {n} * sizeof({et}));\n    {vv}->len += {n};\n    {o}->len = 0;"
                );
                "((lust_Unit){})".into()
            }
            B::VecExtendFromSlice => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (_, sptr, slen) = slice_like(&tys[1], &vals[1]);
                let (sp, sn, i) = (self.tmp(), self.tmp(), self.tmp());
                let vv = &vals[0];
                // The source pointer and length are read into
                // temporaries before the reserve can reallocate
                // (the receiver cannot alias the source in Rust,
                // but the operand text may name the same locals).
                let _ = writeln!(
                    self.out,
                    "    {et} *{sp} = {sptr};\n    uint64_t {sn} = {slen};\n    lust_vec_reserve({vv}, {sn}, sizeof({et}), _Alignof({et}));"
                );
                if is_copy_c(self.p, e) {
                    // A trivial Clone is a byte copy (std's TrivialClone path),
                    // so a zero-sized element costs nothing for any length.
                    let _ = writeln!(self.out, "    memcpy(({et}*){vv}->ptr + {vv}->len, {sp}, {sn} * sizeof({et}));\n    {vv}->len += {sn};");
                } else {
                    self.want(Glue::Clone, e);
                    let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {sn}; {i}++) (({et}*){vv}->ptr)[{vv}->len++] = clone_{}(&{sp}[{i}]);", mangle(e));
                }
                "((lust_Unit){})".into()
            }
            B::VecSplitOff => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, at) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    if ({at} > {vv}->len) lust_panic_nn(\"`at` split index (is \", {at}, \") should be <= len (is \", {vv}->len, \")\", {loc});\n    lust_Vec {t} = lust_vec_with_capacity({vv}->len - {at}, sizeof({et}), _Alignof({et}));\n    memcpy({t}.ptr, ({et}*){vv}->ptr + {at}, ({vv}->len - {at}) * sizeof({et}));\n    {t}.len = {vv}->len - {at};\n    {vv}->len = {at};"
                );
                t
            }
            B::VecResize => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (vv, n) = (&vals[0], &vals[1]);
                let (tv, i) = (self.tmp(), self.tmp());
                // The value is read first: it may come from the
                // Vec the resize then reallocates or truncates.
                let _ = writeln!(self.out, "    {et} {tv} = {};", vals[2]);
                if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    let i2 = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    if ({n} < {vv}->len) {{ for (uint64_t {i2} = {n}; {i2} < {vv}->len; {i2}++) drop_{}(&(({et}*){vv}->ptr)[{i2}]); }}\n    if ({n} <= {vv}->len) {{ drop_{}(&{tv}); }}",
                        mangle(e),
                        mangle(e)
                    );
                }
                let _ = writeln!(self.out, "    if ({n} <= {vv}->len) {{ {vv}->len = {n}; }} else {{");
                if self.p.unwind_tables {
                    // A capacity overflow panic never returns: a guard drops the value.
                    let (gd, gdis) = self.zc_guard(&tv, e);
                    let _ = writeln!(self.out, "      {{{gd} lust_vec_reserve({vv}, {n} - {vv}->len, sizeof({et}), _Alignof({et}));{gdis} }}");
                } else if self.p.unwind {
                    // After a capacity overflow panic (panic=unwind) the Vec is
                    // unchanged and the value is dropped; `(void)` keeps
                    // `wrap_calls` from unwinding before that drop (the
                    // statement's own check unwinds after it).
                    let _ = writeln!(self.out, "      (void)lust_vec_reserve({vv}, {n} - {vv}->len, sizeof({et}), _Alignof({et}));");
                    let _ = writeln!(self.out, "      if ({} >= {n}) {{", vec_cap(&et, vv));
                } else {
                    let _ = writeln!(self.out, "      lust_vec_reserve({vv}, {n} - {vv}->len, sizeof({et}), _Alignof({et}));");
                }
                if is_copy_c(self.p, e) {
                    let _ = writeln!(self.out, "      while ({vv}->len < {n}) (({et}*){vv}->ptr)[{vv}->len++] = {tv};");
                } else {
                    self.want(Glue::Clone, e);
                    // Clones first, the value itself last, as Rust's
                    // `repeat_n` yields them: (count - 1) clones.
                    let _ = writeln!(
                        self.out,
                        "      for (uint64_t {i} = {vv}->len; {i} + 1 < {n}; {i}++) (({et}*){vv}->ptr)[{i}] = clone_{}(&{tv});\n      (({et}*){vv}->ptr)[{n} - 1] = {tv};\n      {vv}->len = {n};",
                        mangle(e)
                    );
                }
                if self.p.unwind && !self.p.unwind_tables {
                    if needs_drop_c(self.p, e) {
                        self.want(Glue::Drop, e);
                        // The frame holds the exception while the drop runs.
                        let _ = writeln!(self.out, "      }} else if (lust_unw_pending && lust_unw_take(&ex)) {{ drop_{}(&{tv}); lust_unw_resume(&ex); }}", mangle(e));
                    } else {
                        let _ = writeln!(self.out, "      }}");
                    }
                }
                let _ = writeln!(self.out, "    }}");
                "((lust_Unit){})".into()
            }
            B::VecDedup => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let (w, r) = (self.tmp(), self.tmp());
                let elem_r = format!("(&(({et}*){vv}->ptr)[{r}])");
                let elem_w = format!("(&(({et}*){vv}->ptr)[{w} - 1])");
                let eq = self.eq_expr(e, &elem_r, &elem_w);
                let drop_dup = if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    format!("drop_{}(&(({et}*){vv}->ptr)[{r}]); ", mangle(e))
                } else {
                    String::new()
                };
                // A duplicate drops as soon as it is found, before
                // the next comparison, as in Rust.
                let _ = writeln!(
                    self.out,
                    "    if ({vv}->len > 1) {{\n      uint64_t {w} = 1;\n      for (uint64_t {r} = 1; {r} < {vv}->len; {r}++) {{\n        if ({eq}) {{ {drop_dup}}} else {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }}\n      }}\n      {vv}->len = {w};\n    }}"
                );
                "((lust_Unit){})".into()
            }
            B::VecRetain | B::VecRetainMut => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let f = self.adapter_callee(&ops[1]);
                let (w, r, c) = (self.tmp(), self.tmp(), self.tmp());
                let mut body = String::new();
                let zc = self.p.unwind_tables;
                let rg = if zc { self.tmp() } else { String::new() };
                if zc {
                    body.push_str("    {\n");
                }
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(body, "    uint64_t {w} = 0, {r} = 0;");
                let mut env_disarm = String::new();
                if zc {
                    // Unwind tables: the env drops and the rest moves down behind the
                    // kept ones (std's `BackshiftOnDrop`) as a panic unwinds; cleanup
                    // variables run in reverse order, so the backshift goes first.
                    let (gd, gdis) = self.zc_guard(&c, &tys[1]);
                    env_disarm = gdis;
                    let _ = writeln!(
                        body,
                        "   {gd}\n    struct lust_retain_guard {rg} __attribute__((cleanup(lust_retain_guard_end))) = {{ (lust_Vec *){vv}, &{r}, &{w}, sizeof({et}), 1 }};"
                    );
                }
                let _ = writeln!(body, "    for (; {r} < {vv}->len; {r}++) {{");
                let elem_r = format!("(&(({et}*){vv}->ptr)[{r}])");
                let (keep, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[elem_r]);
                // panic=unwind: a panic in the predicate keeps the element
                // it saw; one in a rejected element's drop counts that one
                // removed. Either way the rest moves down behind the kept
                // ones (std's `BackshiftOnDrop`), so nothing is lost.
                let mine = "lust_unw_pending && lust_unw_mine()";
                if self.p.unwind && !zc {
                    let _ = writeln!(body, "      if ({mine}) break;");
                }
                // A removed element drops as soon as it is rejected,
                // before the predicate sees the next one, as in Rust.
                let drop_rej = if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    if zc {
                        // The element counts removed while its drop runs.
                        format!("{r}++; drop_{}(&(({et}*){vv}->ptr)[{r} - 1]); {r}--; ", mangle(e))
                    } else {
                        let after = if self.p.unwind { format!(" if ({mine}) {{ {r}++; break; }}") } else { String::new() };
                        format!("(void)(drop_{}(&(({et}*){vv}->ptr)[{r}]), 0);{after} ", mangle(e))
                    }
                } else {
                    String::new()
                };
                let _ = writeln!(
                    body,
                    "      if ({keep}) {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }} else {{ {drop_rej}}}"
                );
                let _ = writeln!(body, "    }}");
                if zc {
                    let _ = writeln!(body, "    {rg}.armed = 0; {vv}->len = {w};");
                } else if self.p.unwind {
                    let n = self.tmp();
                    let _ = writeln!(body, "    uint64_t {n} = {vv}->len - {r}; {vv}->len = {w} + {n};");
                    let _ = writeln!(body, "    if ({n} && {w} != {r}) lust_memmove((({et}*){vv}->ptr) + {w}, (({et}*){vv}->ptr) + {r}, {n} * sizeof({et}));");
                } else {
                    let _ = writeln!(body, "    {vv}->len = {w};");
                }
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    if zc {
                        let _ = writeln!(body, "   {env_disarm} drop_{}(&{c});", mangle(&tys[1]));
                    } else if self.p.unwind {
                        let drop_c = self.unw_cleanup_drop(&c, &tys[1]);
                        let _ = writeln!(body, "    if ({mine}) {{{drop_c} }} else drop_{}(&{c});", mangle(&tys[1]));
                    } else {
                        let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                    }
                }
                if zc {
                    body.push_str("    }\n");
                }
                let _ = write!(self.out, "{body}");
                "((lust_Unit){})".into()
            }
            B::BoolThenSome | B::BoolThen => {
                let elem = if b == B::BoolThenSome {
                    tys[1].clone()
                } else {
                    self.adapter_callee_ret(&self.adapter_callee(&ops[1]))
                };
                let opt = CTy::Option(Box::new(elem));
                self.note_held(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                if b == B::BoolThenSome {
                    // The value is eager: it was evaluated as an
                    // argument whether the bool holds or not. On
                    // `false` it drops with the Option it never
                    // entered, as in Rust.
                    let _ = writeln!(self.out, "    if ({}) {{ {field} = {};{some} }}", vals[0], vals[1]);
                    if needs_drop_c(self.p, &tys[1]) {
                        self.want(Glue::Drop, &tys[1]);
                        let d = self.tmp();
                        let _ = writeln!(self.out, "    if (!{}) {{ {} {d} = {}; drop_{}(&{d}); }}", vals[0], ctype(&tys[1]), vals[1], mangle(&tys[1]));
                    }
                } else {
                    let f = self.adapter_callee(&ops[1]);
                    let c = self.tmp();
                    let mut body = String::new();
                    let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                    let _ = writeln!(body, "    if ({}) {{", vals[0]);
                    let (v, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[]);
                    let _ = writeln!(body, "      {field} = {v};{some}");
                    let _ = writeln!(body, "    }}");
                    if needs_drop_c(self.p, &tys[1]) {
                        // An `FnOnce` closure's call takes its env by value
                        // (check rejects a boxed one here), so it drops
                        // only when it did not run.
                        let once = matches!(f.0, sync::Callee::Closure(_, true));
                        self.want(Glue::Drop, &tys[1]);
                        let guard = if once { format!("if (!{}) ", vals[0]) } else { String::new() };
                        let _ = writeln!(body, "    {guard}drop_{}(&{c});", mangle(&tys[1]));
                    }
                    let _ = write!(self.out, "{body}");
                }
                t
            }
            B::VecReverse => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let (i, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    for (uint64_t {i} = 0; {i} < {len} / 2; {i}++) {{ {et} {t} = {ptr}[{i}]; {ptr}[{i}] = {ptr}[{len} - 1 - {i}]; {ptr}[{len} - 1 - {i}] = {t}; }}"
                );
                "((lust_Unit){})".into()
            }
            // `slice::from_ref(&T)` and `from_mut` (fx-option-rest):
            // a one-element slice at the reference itself.
            B::SliceFromRef => {
                let CTy::Ref(e) = &tys[0] else { unreachable!() };
                let et = ctype(e);
                let sl = CTy::Slice(e.clone());
                let (st, t) = (ctype(&sl), self.tmp());
                let vv = &vals[0];
                let _ = writeln!(self.out, "    {st} {t} = {{ ({et}*){vv}, 1 }};");
                t
            }
            // The safe raw pointer surface (w-cinterop): every value is
            // the C address itself.
            B::PtrFromRef => vals[0].clone(),
            B::PtrNull => "((void*)0)".into(),
            // A fat operand (tf-fatptr): `eq` compares the address and
            // the metadata (check rejects it for dyn pointers),
            // `addr_eq` the addresses only.
            B::PtrEqFn if let CTy::FatPtr(e) = &tys[0] => match **e {
                CTy::Dyn => format!("(({0}).data == ({1}).data && ({0}).vt == ({1}).vt)", vals[0], vals[1]),
                _ => format!("((void*)({0}).ptr == (void*)({1}).ptr && ({0}).len == ({1}).len)", vals[0], vals[1]),
            },
            B::PtrEqFn | B::PtrAddrEqFn | B::PtrFnAddrEqFn => format!("({} == {})", ptr_addr(&vals[0], &tys[0]), ptr_addr(&vals[1], &tys[1])),
            B::PtrIsNull => format!("({} == 0)", ptr_addr(&vals[0], &tys[0])),
            B::PtrCast => ptr_addr(&vals[0], &tys[0]),
            B::PtrCastMut => vals[0].clone(),
            B::PtrLen => format!("(({}).len)", vals[0]),
            B::PtrAddr => format!("((uint64_t)(uintptr_t){})", ptr_addr(&vals[0], &tys[0])),
            B::PtrWithAddr => format!("((void*)(uintptr_t)({}))", vals[1]),
            // `Rc::as_ptr`: the payload behind the counts. An `Rc<dyn
            // Tr>`, `Rc<str>` or `Rc<[T]>` is already the fat view of it.
            B::SmartAsPtr if owning_fat_ref(&tys[0]) => format!("(*{})", vals[0]),
            B::SmartAsPtr => match deref_cty(&tys[0]) {
                CTy::Rc(e) | CTy::Sync(crate::ty::sync::SyncTy::Arc, e) => rc_ptr(&format!("(*{})", vals[0]), &e),
                _ => format!("(&(*{})->v)", vals[0]),
            },
            B::SeqAsPtr => slice_like(&tys[0], &vals[0]).1,
            B::StrAsPtr => match &tys[0] {
                CTy::Ref(inner) if **inner == CTy::String => format!("({})->ptr", vals[0]),
                _ => format!("({}).ptr", vals[0]),
            },
            B::VecAsSlice | B::VecAsMutSlice => {
                // `Vec`, arrays, and slices all give the same
                // fat value (core's `as_slice` family).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let sl = CTy::Slice(Box::new(e));
                let (st, t) = (ctype(&sl), self.tmp());
                let _ = writeln!(self.out, "    {st} {t} = {{ {ptr}, {len} }};");
                t
            }
            B::SliceToVec | B::VecFrom => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                // `Vec::from([T; N])` moves its elements; the
                // slice forms clone them. Both allocate exactly.
                let moves = b == B::VecFrom && matches!(tys[0], CTy::Array(..));
                let (t, i) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({len}, sizeof({et}), _Alignof({et}));");
                if moves || is_copy_c(self.p, &e) {
                    // A move or a trivial Clone is a byte copy (std's
                    // TrivialClone path): free for zero-sized elements.
                    let _ = writeln!(self.out, "    memcpy({t}.ptr, {ptr}, {len} * sizeof({et}));");
                } else {
                    self.want(Glue::Clone, &e);
                    let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) (({et}*){t}.ptr)[{i}] = clone_{}(&{ptr}[{i}]);", mangle(&e));
                }
                let _ = writeln!(self.out, "    {t}.len = {len};");
                t
            }
            B::StrFind | B::StrRfind => {
                let a = str_of(&vals[0], &tys[0]);
                let f = if b == B::StrFind { "lust_str_find" } else { "lust_str_rfind" };
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::Usize)));
                self.note_held(&opt);
                let (t, idx) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    int64_t {idx} = {f}({a}, {});", vals[1]);
                let _ = writeln!(self.out, "    if ({idx} >= 0) {{ {field} = (uint64_t){idx};{some} }}");
                t
            }
            B::StrContains | B::StrStartsWith | B::StrEndsWith => {
                let a = str_of(&vals[0], &tys[0]);
                let f = match b {
                    B::StrContains => "lust_str_contains",
                    B::StrStartsWith => "lust_str_starts_with",
                    _ => "lust_str_ends_with",
                };
                format!("{f}({a}, {})", vals[1])
            }
            B::StrTrim => format!("lust_str_trim({})", str_of(&vals[0], &tys[0])),
            B::StrToAsciiLowercase => format!("lust_str_ascii_case({}, 0)", str_of(&vals[0], &tys[0])),
            B::StrToAsciiUppercase => format!("lust_str_ascii_case({}, 1)", str_of(&vals[0], &tys[0])),
            B::StringFromUtf16Lossy => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                format!("lust_string_from_utf16_lossy({ptr}, {len})")
            }
            B::StrToUppercase => format!("lust_str_case({}, 1)", str_of(&vals[0], &tys[0])),
            B::StrToLowercase => format!("lust_str_case({}, 0)", str_of(&vals[0], &tys[0])),
            B::StrChars => format!("lust_chars({})", str_of(&vals[0], &tys[0])),
            B::CharsNext => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ =
                    writeln!(self.out, "    if ({it}->pos < {it}->s.len) {{ {field} = lust_utf8_next({it}->s.ptr, &{it}->pos);{some} }}");
                t
            }
            B::CharsNextBack => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({it}->pos < {it}->s.len) {{ {field} = lust_utf8_prev({it}->s.ptr, &{it}->s.len);{some} }}");
                t
            }
            B::CharsCount => format!("lust_chars_count({})", vals[0]),
            // `Utf8Chunks::next` (tf-slice): the iterator is a
            // one-field tuple of the bytes left; a chunk is the
            // (valid, invalid) pair the runtime scan splits off.
            B::Utf8ChunksNext => {
                let it = &vals[0];
                let chunk = CTy::Tuple(vec![CTy::Ref(Box::new(CTy::Str)), CTy::Slice(Box::new(CTy::Int(IntTy::U8)))]);
                let opt = CTy::Option(Box::new(chunk.clone()));
                self.note_held(&opt);
                let (t, vl, us) = (self.tmp(), self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    if ({it}->f0.len > 0) {{ uint64_t {vl} = 0, {us} = 0;\n      lust_utf8_chunk_step({it}->f0.ptr, {it}->f0.len, &{vl}, &{us});\n      {field}.f0 = (lust_str){{ {it}->f0.ptr, {vl} }};\n      {field}.f1 = ({}){{ {it}->f0.ptr + {vl}, {us} - {vl} }};{some}\n      {it}->f0.ptr += {us}; {it}->f0.len -= {us}; }}",
                    ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))))
                );
                t
            }
            B::Utf8ChunkValid => format!("(*{}).f0", vals[0]),
            B::Utf8ChunkInvalid => format!("(*{}).f1", vals[0]),
            B::CharIsDigit => format!("(*{0} >= '0' && *{0} <= '9')", vals[0]),
            B::CharIsAlphabetic => format!("((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z')", vals[0]),
            B::CharIsAlphanumeric => format!("((*{0} >= '0' && *{0} <= '9') || ((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z'))", vals[0]),
            B::CharIsWhitespace => format!("(*{0} == ' ' || *{0} == '\\t' || *{0} == '\\n' || *{0} == '\\r' || *{0} == 12)", vals[0]),
            B::CharIsUppercase => format!("(*{0} >= 'A' && *{0} <= 'Z')", vals[0]),
            B::CharIsLowercase => format!("(*{0} >= 'a' && *{0} <= 'z')", vals[0]),
            B::CharIsAlphabeticUnicode => format!("lust_char_is_alphabetic({})", vals[0]),
            B::CharIsNumericUnicode => format!("lust_char_is_numeric({})", vals[0]),
            B::CharIsAlphanumericUnicode => format!("lust_char_is_alphanumeric({})", vals[0]),
            B::CharIsLowercaseUnicode => format!("lust_char_is_lowercase({})", vals[0]),
            B::CharIsUppercaseUnicode => format!("lust_char_is_uppercase({})", vals[0]),
            B::CharIsWhitespaceUnicode => format!("lust_is_space({})", vals[0]),
            B::CharIsControlUnicode => format!("lust_char_is_control({})", vals[0]),
            B::CharFromU32 => {
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = {}; if (d <= 0x10FFFFu && !(d >= 0xD800u && d <= 0xDFFFu)) {{ {field} = d;{some} }} }}",
                    vals[0]
                );
                t
            }
            B::CharFromDigit => {
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = lust_from_digit({}, {}, {}); if (d != 0xFFFFFFFFu) {{ {field} = d;{some} }} }}",
                    vals[0],
                    vals[1],
                    std_loc(2, 332, 9)
                );
                t
            }
            B::CharToUppercase => format!("((*{0} >= 'a' && *{0} <= 'z') ? *{0} - 32 : *{0})", vals[0]),
            B::CharToLowercase => format!("((*{0} >= 'A' && *{0} <= 'Z') ? *{0} + 32 : *{0})", vals[0]),
            B::MakeAsciiLowercase | B::MakeAsciiUppercase => {
                let p = self.tmp();
                let et = ctype(match &tys[0] {
                    CTy::Ref(inner) => inner,
                    other => other,
                });
                let expr = if b == B::MakeAsciiLowercase {
                    format!("((*{p} >= 'A' && *{p} <= 'Z') ? *{p} + 32 : *{p})")
                } else {
                    format!("((*{p} >= 'a' && *{p} <= 'z') ? *{p} - 32 : *{p})")
                };
                let _ = writeln!(self.out, "    {et}* {p} = {}; *{p} = ({et}){expr};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::CharToDigit => {
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::U32)));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = lust_digit({}, {}, {}); if (d != 0xFFFFFFFFu) {{ {field} = d;{some} }} }}",
                    vals[0],
                    vals[1],
                    std_loc(1, 407, 9)
                );
                t
            }
            B::MemSwap => {
                // A byte exchange through a stack temp: both places
                // stay initialized, so their drop flags are untouched.
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                let et = ctype(inner);
                let (pa, pb, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {et}* {pa} = {}; {et}* {pb} = {}; {et} {t}; lust_memcpy(&{t}, {pa}, sizeof({et})); lust_memcpy({pa}, {pb}, sizeof({et})); lust_memcpy({pb}, &{t}, sizeof({et}));",
                    vals[0], vals[1]
                );
                "((lust_Unit){})".into()
            }
            B::MemReplace => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                let et = ctype(inner);
                let (pa, nv, old) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {et}* {pa} = {}; {et} {nv} = {}; {et} {old}; lust_memcpy(&{old}, {pa}, sizeof({et})); lust_memcpy({pa}, &{nv}, sizeof({et}));",
                    vals[0], vals[1]
                );
                old
            }
            B::MemTake => unreachable!("take lowers to a default fill plus MemReplace"),
            // The value through a slot whose address escapes into an empty
            // asm (runtime.h `lust_black_box`), as rustc's black_box does: an
            // optimizer keeps what it would otherwise drop (an unused
            // allocation, a benchmark's work).
            B::HintBlackBox => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {}; lust_black_box(&{t});", ctype(&tys[0]), vals[0]);
                t
            }
            B::CmpMax | B::CmpMin => {
                // Check limited these to primitive total orders. On
                // a tie the first argument wins, as `Ord::max` and
                // `Ord::min` specify (the loser would drop, but a
                // primitive has no destructor).
                let ct = ctype(&tys[0]);
                let (a, bb) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {ct} {a} = {}; {ct} {bb} = {};", vals[0], vals[1]);
                let ge = b == B::CmpMax;
                match &tys[0] {
                    CTy::Int(it) if is128(*it) => {
                        let f = if *it == IntTy::I128 { "lust_i128_cmp" } else { "lust_u128_cmp" };
                        if ge { format!("(({f}({a}, {bb}) >= 0) ? {a} : {bb})") } else { format!("(({f}({a}, {bb}) <= 0) ? {a} : {bb})") }
                    }
                    _ => {
                        if ge {
                            format!("(({a} >= {bb}) ? {a} : {bb})")
                        } else {
                            format!("(({a} <= {bb}) ? {a} : {bb})")
                        }
                    }
                }
            }
        }
    }

    // ---------- Formatting ----------

    /// The C for one inherent integer method (see the family arms in
    /// `builtin`). Widths up to 64 run through the generic word ops in
    /// core.c; 128-bit values use the two-word helpers for the subset
    /// the checker lets through.
    /// The int parse of `a` (a `lust_str` expression) at `radix` (a
    /// `u32` expression already checked to be in 2..=36): the runtime
    /// parses into two words plus an `IntErrorKind` tag; here they
    /// become the `Result` and its error struct (tf-str, R26).
    fn parse_int_c(&mut self, it: IntTy, a: &str, radix: &str) -> String {
        let p = self.p;
        let (Some(pie), Some(iek)) = (
            p.tys.local_adt_of(crate::check::generics::parse_int_error_def()),
            p.tys.local_adt_of(crate::check::generics::int_error_kind_def()),
        ) else {
            unreachable!("parse type-checks only with std's error Adts")
        };
        let val_ty = CTy::Int(it);
        let res = CTy::Result(Box::new(val_ty.clone()), Box::new(CTy::Adt(pie)));
        self.note_held(&res);
        let (t, lo, hi, kind) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
        let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
        let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
        let _ = writeln!(self.out, "    uint64_t {lo}, {hi}; int {kind}; {} {t};", ctype(&res));
        let _ = writeln!(
            self.out,
            "    if (lust_parse_int_radix({a}, {radix}, {}, {}, &{lo}, &{hi}, &{kind})) {{ {ok_f} = {}; {ok_d} }}",
            u8::from(it.signed()),
            it.bits(),
            if it.bits() >= 128 { format!("(({}){{ {lo}, {hi} }})", ctype(&val_ty)) } else { format!("(({}){lo})", ctype(&val_ty)) }
        );
        let kct = CTy::Adt(iek);
        let kinds: Vec<String> = (0..4).map(|v| self.make_variant(&kct, v, &[])).collect();
        let _ = writeln!(
            self.out,
            "    else {{ {err_f}.f0 = {kind} == 0 ? {} : {kind} == 1 ? {} : {kind} == 2 ? {} : {}; {err_d} }}",
            kinds[0], kinds[1], kinds[2], kinds[3]
        );
        t
    }

    fn int_method_c(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let it = match &tys[0] {
            CTy::Int(i) => *i,
            _ => IntTy::I64,
        };
        if is128(it) {
            return self.int128_method_c(b, vals, it, loc);
        }
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let a = &vals[0];
        let ua = format!("((uint64_t)({a}))");
        let ub = if vals.len() > 1 { format!("((uint64_t)({}))", vals[1]) } else { String::new() };
        let mask = if bits >= 64 { "~0ull".to_string() } else { format!("((1ull << {bits}) - 1ull)") };
        let masked_a = format!("({ua} & {mask})");
        let div0 = |b: Builtin| -> &'static str {
            if matches!(b, B::WrappingRem | B::CheckedRem | B::SaturatingDiv) {
                "attempt to calculate the remainder with a divisor of zero"
            } else {
                "attempt to divide by zero"
            }
        };
        // A checked_op call into fresh (out, rc) temporaries. Returns
        // the statement text; rc is 1 ok, 0 overflow, -1 div by zero.
        let checked_call = |this: &mut Self, a64: &str, b64: &str, op: i32| -> (String, String) {
            let (o, rc) = (this.tmp(), this.tmp());
            let _ = write!(this.out, "    uint64_t {o}; int {rc} = lust_checked_op({a64}, {b64}, {bits}, {}, {op}, &{o});\n", sgn as i32);
            (o, rc)
        };
        match b {
            B::WrappingDiv | B::WrappingRem => {
                let op = if b == B::WrappingDiv { 3 } else { 4 };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                let msg = div0(b);
                // The signed forms divide inside core; the unsigned ones at the caller.
                let at = if sgn { num_loc(it, false) } else { loc.to_string() };
                let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{msg}\", {at});");
                format!("(({ct}){o})")
            }
            B::WrappingNeg => format!("(({ct})((0ull - {ua}) & {mask}))"),
            B::WrappingAbs => format!("(({a} < 0 ? ({ct})((0ull - {ua}) & {mask}) : {a}))"),
            B::WrappingPow => format!("(({ct})lust_wrapping_pow({ua}, {}, {bits}))", vals[1]),
            B::WrappingShl => format!("(({ct})(({masked_a} << ({} & {})) & {mask}))", vals[1], bits - 1),
            B::WrappingShr => {
                if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({} & {})) & (int64_t){mask}))", vals[1], bits - 1)
                } else {
                    format!("(({ct})({masked_a} >> ({} & {})))", vals[1], bits - 1)
                }
            }
            B::CheckedAdd | B::CheckedSub | B::CheckedMul | B::CheckedDiv | B::CheckedRem => {
                let op = match b {
                    B::CheckedAdd => 0,
                    B::CheckedSub => 1,
                    B::CheckedMul => 2,
                    B::CheckedDiv => 3,
                    _ => 4,
                };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedNeg => {
                let (o, rc) = checked_call(self, "0ull", &ua, 1);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let (o, rc) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                    sgn as i32
                );
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedShl | B::CheckedShr => {
                let amt = &vals[1];
                let r = if b == B::CheckedShl {
                    format!("(({ct})(({masked_a} << ({amt} & 63u)) & {mask}))")
                } else if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({amt} & 63u)) & (int64_t){mask}))")
                } else {
                    format!("(({ct})({masked_a} >> ({amt} & 63u)))")
                };
                self.int_option_c(&r, &format!("{amt} < {bits}u"), it)
            }
            B::StrictAdd | B::StrictSub | B::StrictMul | B::StrictDiv | B::StrictRem => {
                let (op, verb) = match b {
                    B::StrictAdd => (0, "add"),
                    B::StrictSub => (1, "subtract"),
                    B::StrictMul => (2, "multiply"),
                    B::StrictDiv => (3, "divide"),
                    _ => (4, "calculate the remainder"),
                };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                let div0msg = if op == 4 {
                    "attempt to calculate the remainder with a divisor of zero"
                } else {
                    "attempt to divide by zero"
                };
                let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{div0msg}\", {loc});");
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to {verb} with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictNeg => {
                let (o, rc) = checked_call(self, "0ull", &ua, 1);
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to negate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let (o, rc) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                    sgn as i32
                );
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to negate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to exponentiate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictShl | B::StrictShr => {
                let amt = &vals[1];
                let (msg, r) = if b == B::StrictShl {
                    ("attempt to shift left with overflow", format!("(({ct})(({masked_a} << ({amt} & 63u)) & {mask}))"))
                } else if sgn {
                    ("attempt to shift right with overflow", format!("(({ct})(((int64_t)({a}) >> ({amt} & 63u)) & (int64_t){mask}))"))
                } else {
                    ("attempt to shift right with overflow", format!("(({ct})({masked_a} >> ({amt} & 63u)))"))
                };
                let t = self.tmp();
                let _ = writeln!(self.out, "    if ({amt} >= {bits}u) lust_panic_cstr(\"{msg}\", {loc}); {ct} {t} = {r};");
                t
            }
            B::MixedCheckedAdd
            | B::MixedCheckedSub
            | B::MixedWrappingAdd
            | B::MixedWrappingSub
            | B::MixedSaturatingAdd
            | B::MixedSaturatingSub
            | B::MixedOverflowingAdd
            | B::MixedOverflowingSub
            | B::MixedStrictAdd
            | B::MixedStrictSub => self.mixed_op_c(b, vals, it, loc),
            B::CheckedSignedDiff => {
                let masked_b = format!("({ub} & {mask})");
                let sct = int_c(it.counterpart());
                let smax = format!("(({sct}){}ll)", if bits >= 64 { i64::MAX } else { (1i64 << (bits - 1)) - 1 });
                let (x, y) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = {masked_b};");
                let diff = format!("(({sct})(({x} - {y}) & {mask}))");
                let fits = format!(
                    "({x} >= {y} ? ({x} - {y}) <= (uint64_t){smax} : ({y} - {x}) <= (uint64_t){smax} + 1ull)"
                );
                self.int_option_c(&diff, &fits, it.counterpart())
            }
            B::CarryingAdd | B::BorrowingSub => {
                let masked_b = format!("({ub} & {mask})");
                let (x, y, t) = (self.tmp(), self.tmp(), self.tmp());
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = {masked_b};");
                if b == B::CarryingAdd {
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {{ uint64_t s = {x} + {y} + ({} ? 1ull : 0ull); {t}.f0 = ({ct})(s & {mask}); {t}.f1 = s > {mask} || s < {x} || ({} && s == {x} && {y} == {mask}); }}",
                        vals[2], vals[2]
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {t}.f0 = ({ct})(({x} - {y} - ({} ? 1ull : 0ull)) & {mask}); {t}.f1 = {x} < {y} || ({} && {x} == {y});",
                        vals[2],
                        vals[2]
                    );
                }
                t
            }
            B::CarryingMul | B::CarryingMulAdd => {
                let masked_b = format!("({ub} & {mask})");
                let (p, t) = (self.tmp(), self.tmp());
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Int(it)]);
                let tt = ctype(&tup);
                let add = if b == B::CarryingMulAdd {
                    format!("lust_u128_add(lust_u128_add({p}, (lust_u128){{{}, 0}}), (lust_u128){{{}, 0}})", format!("({} & {mask})", vals[2]), format!("((uint64_t)({}) & {mask})", vals[3]))
                } else {
                    format!("lust_u128_add({p}, (lust_u128){{{}, 0}})", format!("({} & {mask})", vals[2]))
                };
                let hi = if bits >= 64 {
                    format!("{p}.hi")
                } else {
                    format!("(({p}.lo >> {bits}) | ({p}.hi << (64 - {bits})))")
                };
                let _ = writeln!(
                    self.out,
                    "    lust_u128 {p} = lust_u128_mul((lust_u128){{{masked_a}, 0}}, (lust_u128){{{masked_b}, 0}}); {p} = {add}; {tt} {t}; {t}.f0 = ({ct})({p}.lo & {mask}); {t}.f1 = ({ct})({hi} & {mask});",
                );
                t
            }
            _ => self.int_method_c2(b, vals, it, loc),
        }
    }

    /// One mixed-sign operation (`checked_add_unsigned` and kin):
    /// the receiver keeps its type, the argument has the other
    /// signedness at the same width. Computes the wrapped result
    /// and the overflow flag on the masked 64-bit forms, then
    /// shapes them by family: checked -> Option, wrapping -> the
    /// value, saturating -> clamped, overflowing -> (value, flag),
    /// strict -> panic on overflow.
    fn mixed_op_c(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let sub = matches!(b, B::MixedCheckedSub | B::MixedWrappingSub | B::MixedSaturatingSub | B::MixedOverflowingSub | B::MixedStrictSub);
        let (x, y, r, ovf) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
        let mask: String = if bits >= 64 { "~0ull".into() } else { format!("((1ull << {bits}) - 1ull)") };
        let max_u = if sgn {
            if bits >= 64 { "0x7FFFFFFFFFFFFFFFull".to_string() } else { format!("{}ull", (1u128 << (bits - 1)) - 1) }
        } else {
            mask.clone()
        };
        let min_u = if sgn { format!("(1ull << {})", bits - 1) } else { "0ull".to_string() };
        let _ = writeln!(self.out, "    {ct} {x} = {}; uint64_t {y} = (uint64_t)({}) & {mask};", vals[0], vals[1]);
        if sgn {
            // Signed receiver, unsigned magnitude argument.
            // The room below is `x - MIN`: on the sign-extended word,
            // `x - 2^(bits-1)` taken mod 2^bits (the mask), as `x + 2^(bits-1)`.
            let (thr, op) = if sub { (format!("(((uint64_t){x} - {min_u}) & {mask})"), "-") } else { (format!("({max_u} - (uint64_t){x})"), "+") };
            let _ = writeln!(self.out, "    uint64_t {r} = ((uint64_t){x} {op} {y}) & {mask}; int {ovf} = {y} > {thr};");
        } else {
            // Unsigned receiver, signed argument: its sign decides
            // which end can overflow. A negative argument's
            // magnitude is its two's-complement negation.
            let sct = int_c(it.counterpart());
            let (neg_room, pos_room) = if sub {
                (format!("({mask} - ({x} & {mask}))"), format!("({x} & {mask})"))
            } else {
                (format!("({x} & {mask})"), format!("({mask} - ({x} & {mask}))"))
            };
            let _ = writeln!(
                self.out,
                "    uint64_t {r} = (({x} {} {y}) & {mask}); int {ovf} = (({sct}){y} < 0) ? (((0ull - {y}) & {mask}) > {neg_room}) : ({y} > {pos_room});",
                if sub { "-" } else { "+" }
            );
        }
        let val = format!("(({ct}){r})");
        match b {
            B::MixedWrappingAdd | B::MixedWrappingSub => val,
            B::MixedCheckedAdd | B::MixedCheckedSub => self.int_option_c(&val, &format!("!{ovf}"), it),
            B::MixedOverflowingAdd | B::MixedOverflowingSub => {
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = {val}; {t}.f1 = {ovf};");
                t
            }
            B::MixedSaturatingAdd | B::MixedSaturatingSub => {
                // One overflow direction per form, named by the
                // argument's sign for an unsigned receiver: adding
                // or subtracting an unsigned magnitude can only
                // pass the top (add) or the bottom (sub) end.
                let t = self.tmp();
                let hi = format!("(({ct}){max_u})");
                let lo = if sgn {
                    if bits >= 64 {
                        format!("(({ct})(-9223372036854775807ll - 1))")
                    } else {
                        format!("(({ct}){}ll)", -(1i128 << (bits - 1)))
                    }
                } else {
                    format!("(({ct})0)")
                };
                let clamp = if sgn {
                    if sub { lo } else { hi }
                } else if sub {
                    format!("((({}){} < 0) ? {hi} : {lo})", int_c(it.counterpart()), y)
                } else {
                    format!("((({}){} < 0) ? {lo} : {hi})", int_c(it.counterpart()), y)
                };
                let _ = writeln!(self.out, "    {ct} {t} = {ovf} ? {clamp} : {val};");
                t
            }
            _ => {
                let verb = if sub { "subtract" } else { "add" };
                let t = self.tmp();
                let _ = writeln!(self.out, "    if ({ovf}) lust_panic_cstr(\"attempt to {verb} with overflow\", {loc}); {ct} {t} = {val};");
                t
            }
        }
    }

    /// An Option<int> value holding `expr` when `cond` holds, else None.
    fn int_option_c(&mut self, expr: &str, cond: &str, it: IntTy) -> String {
        use std::fmt::Write as _;
        let opt = CTy::Option(Box::new(CTy::Int(it)));
        let ot = ctype(&opt);
        let t = self.tmp();
        let field = variant_field(self.p, &opt, &t, 1, 0);
        let some = disc_set(self.p, &opt, &t, 1);
        let some = if some.is_empty() { String::new() } else { format!(" {some}") };
        let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
        let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {expr};{some} }}");
        t
    }

    /// The saturating, overflowing, and bit inspection families.
    fn int_method_c2(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let a = &vals[0];
        let ua = format!("((uint64_t)({a}))");
        let ub = if vals.len() > 1 { format!("((uint64_t)({}))", vals[1]) } else { String::new() };
        let mask: String = if bits >= 64 { "~0ull".into() } else { format!("((1ull << {bits}) - 1ull)") };
        let masked_a = format!("({ua} & {mask})");
        let max_lit = if sgn {
            if bits >= 64 { format!("(({ct})0x7FFFFFFFFFFFFFFFll)") } else { format!("(({ct}){}ll)", (1i128 << (bits - 1)) - 1) }
        } else if bits >= 64 {
            format!("(({ct})~0ull)")
        } else {
            format!("(({ct}){}ull)", (1u128 << bits) - 1)
        };
        let min_lit = if sgn {
            if bits >= 64 { format!("(({ct})(-9223372036854775807ll - 1))") } else { format!("(({ct}){}ll)", -(1i128 << (bits - 1))) }
        } else {
            format!("(({ct})0)")
        };
        let sa = format!("((int64_t)({a}))");
        let sb = if vals.len() > 1 { format!("((int64_t)({}))", vals[1]) } else { String::new() };
        let sat_op = |b: Builtin| -> Option<i32> {
            Some(match b {
                B::SaturatingAdd | B::OverflowingAdd => 0,
                B::SaturatingSub | B::OverflowingSub => 1,
                B::SaturatingMul | B::OverflowingMul => 2,
                B::SaturatingDiv | B::OverflowingDiv => 3,
                B::OverflowingRem => 4,
                _ => return None,
            })
        };
        if let Some(op) = sat_op(b) {
            let (o, rc) = (self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_op({ua}, {ub}, {bits}, {}, {op}, &{o});", sgn as i32);
            let div0msg = if op == 4 { "attempt to calculate the remainder with a divisor of zero" } else { "attempt to divide by zero" };
            // The signed forms divide inside core; the unsigned ones at the caller.
            let at = if sgn { num_loc(it, false) } else { loc.to_string() };
            let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{div0msg}\", {at});");
            if matches!(b, B::SaturatingAdd | B::SaturatingSub | B::SaturatingMul | B::SaturatingDiv) {
                // Clamp to the endpoint the true result passes.
                let clamp = if !sgn {
                    if op == 1 { min_lit.clone() } else { max_lit.clone() }
                } else {
                    match op {
                        0 | 1 => format!("({sa} >= 0 ? {max_lit} : {min_lit})"),
                        2 => format!("((({sa} < 0) != ({sb} < 0)) ? {min_lit} : {max_lit})"),
                        _ => max_lit.clone(),
                    }
                };
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t} = {rc} == 1 ? ({ct}){o} : {clamp};");
                return t;
            }
            // Overflowing: (wrapping result, overflowed).
            let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
            let tt = ctype(&tup);
            let t = self.tmp();
            let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = ({ct}){o}; {t}.f1 = {rc} == 0;");
            return t;
        }
        match b {
            B::SaturatingNeg | B::SaturatingAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let t = self.tmp();
                let inner = if b == B::SaturatingNeg {
                    format!("{x} == {min_lit} ? {max_lit} : -{x}")
                } else {
                    format!("{x} == {min_lit} ? {max_lit} : ({x} < 0 ? -{x} : {x})")
                };
                let _ = writeln!(self.out, "    {ct} {t} = {inner};");
                t
            }
            B::OverflowingNeg | B::OverflowingAbs => {
                let (o, rc) = (self.tmp(), self.tmp());
                if b == B::OverflowingNeg {
                    let _ =
                        writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_op(0ull, {ua}, {bits}, {}, 1, &{o});", sgn as i32);
                } else {
                    let x = self.tmp();
                    let _ = writeln!(self.out, "    {ct} {x} = {a};");
                    let _ = writeln!(
                        self.out,
                        "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                        sgn as i32
                    );
                }
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = ({ct}){o}; {t}.f1 = {rc} == 0;");
                t
            }
            B::SaturatingPow | B::OverflowingPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                if b == B::SaturatingPow {
                    let clamp = if sgn { format!("(({sa} < 0 && ({} & 1u)) ? {min_lit} : {max_lit})", vals[1]) } else { max_lit.clone() };
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {ct} {t} = {rc} == 1 ? ({ct}){o} : {clamp};");
                    t
                } else {
                    let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                    let tt = ctype(&tup);
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {t}.f0 = ({ct})lust_wrapping_pow({ua}, {}, {bits}); {t}.f1 = {rc} == 0;",
                        vals[1]
                    );
                    t
                }
            }
            B::OverflowingShl | B::OverflowingShr => {
                let amt = &vals[1];
                let r = if b == B::OverflowingShl {
                    format!("(({ct})(({masked_a} << ({amt} & {})) & {mask}))", bits - 1)
                } else if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({amt} & {})) & (int64_t){mask}))", bits - 1)
                } else {
                    format!("(({ct})({masked_a} >> ({amt} & {})))", bits - 1)
                };
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = {r}; {t}.f1 = {amt} >= {bits}u;");
                t
            }
            B::CountOnes => format!("lust_count_ones64({masked_a})"),
            B::CountZeros => format!("({bits}u - lust_count_ones64({masked_a}))"),
            B::LeadingZeros => format!("lust_leading_zeros64({masked_a}, {bits})"),
            B::TrailingZeros => format!("lust_trailing_zeros64({masked_a}, {bits})"),
            B::LeadingOnes => format!("lust_leading_zeros64((~{ua}) & {mask}, {bits})"),
            B::TrailingOnes => format!("lust_trailing_zeros64((~{ua}) & {mask}, {bits})"),
            B::RotateLeft | B::RotateRight => {
                let (x, n) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}; uint32_t {n} = {} & {};", vals[1], bits - 1);
                if b == B::RotateLeft {
                    format!("(({ct})((({x} << {n}) | ({x} >> (({bits} - {n}) & {}))) & {mask}))", bits - 1)
                } else {
                    format!("(({ct})((({x} >> {n}) | ({x} << (({bits} - {n}) & {}))) & {mask}))", bits - 1)
                }
            }
            B::SwapBytes => {
                let (x, r, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}, {r} = 0; for (uint32_t {i} = 0; {i} < {bits} / 8; {i}++) {r} = ({r} << 8) | (({x} >> (8 * {i})) & 0xFFull);"
                );
                format!("(({ct}){r})")
            }
            B::ReverseBits => {
                let (x, r, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}, {r} = 0; for (uint32_t {i} = 0; {i} < {bits}; {i}++) {r} |= (({x} >> {i}) & 1ull) << ({bits} - 1 - {i});"
                );
                format!("(({ct}){r})")
            }
            B::DivCeil => format!("(({ct})lust_div_ceil({ua}, {ub}, {bits}, {loc}))"),
            B::DivEuclid | B::StrictDivEuclid => format!("(({ct})lust_div_euclid({ua}, {ub}, {bits}, {}, {loc}))", sgn as i32),
            B::RemEuclid | B::StrictRemEuclid => format!("(({ct})lust_rem_euclid({ua}, {ub}, {bits}, {}, {loc}))", sgn as i32),
            B::Signum => format!("(({ct})(({a} > 0) - ({a} < 0)))"),
            B::IsPositive => format!("({a} > 0)"),
            B::IsNegative => format!("({a} < 0)"),
            B::IsPowerOfTwo => format!("({masked_a} != 0 && ({masked_a} & ({masked_a} - 1)) == 0)"),
            B::IsMultipleOf => {
                let masked_b = format!("({ub} & {mask})");
                format!("({masked_b} == 0 ? {masked_a} == 0 : ({masked_a} % {masked_b}) == 0)")
            }
            B::NextMultipleOf | B::CheckedNextMultipleOf => {
                let (x, y, add, t) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let nloc = num_loc(it, false);
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = ({ub} & {mask});");
                if b == B::NextMultipleOf {
                    let _ = writeln!(
                        self.out,
                        "    if ({y} == 0) lust_panic_cstr(\"attempt to calculate the remainder with a divisor of zero\", {nloc});"
                    );
                }
                let _ = writeln!(
                    self.out,
                    "    uint64_t {add} = {y} == 0 ? 0 : ({x} % {y} == 0 ? 0 : {y} - {x} % {y}); {ct} {t} = ({ct})(({x} + {add}) & {mask});"
                );
                if b == B::NextMultipleOf {
                    // core's `self + (rhs - r)` inherits the overflow checks: off, it wraps.
                    if self.p.overflow_checks {
                        let _ = writeln!(self.out, "    if ({add} > ({mask}) - {x}) lust_panic_cstr(\"attempt to add with overflow\", {nloc});");
                    }
                    t
                } else {
                    self.int_option_c(&t, &format!("{y} != 0 && {add} <= ({mask}) - {x}"), it)
                }
            }
            B::UnsignedAbs => {
                let uct = int_c(it.counterpart());
                format!("(({uct})(({a} < 0 ? (0ull - {ua}) : {ua}) & {mask}))")
            }
            // The difference of the 64-bit images wraps to the distance.
            B::IntAbsDiff => {
                let (uct, gt) = if sgn {
                    (int_c(it.counterpart()), format!("{sa} > {sb}"))
                } else {
                    (int_c(it), format!("{masked_a} > ({ub} & {mask})"))
                };
                format!("(({uct})(({gt} ? ({ua} - {ub}) : ({ub} - {ua})) & {mask}))")
            }
            B::UnboundedShl => format!("(({}) >= {bits}u ? ({ct})0 : ({ct})(({masked_a} << {}) & {mask}))", vals[1], vals[1]),
            B::UnboundedShr => {
                if sgn {
                    format!("(({}) >= {bits}u ? ({ct})(({a} < 0) ? -1 : 0) : ({ct})(((int64_t)({a}) >> {}) & (int64_t){mask}))", vals[1], vals[1])
                } else {
                    format!("(({}) >= {bits}u ? ({ct})0 : ({ct})({masked_a} >> {}))", vals[1], vals[1])
                }
            }
            B::CastSigned | B::CastUnsigned => format!("(({})({a}))", int_c(it.counterpart())),
            B::BitWidth => format!("({bits}u - lust_leading_zeros64({masked_a}, {bits}))"),
            B::HighestOne => self.int_option_c(&format!("({bits}u - 1u - lust_leading_zeros64({masked_a}, {bits}))"), &format!("{masked_a} != 0"), IntTy::U32),
            B::LowestOne => self.int_option_c(&format!("lust_trailing_zeros64({masked_a}, {bits})"), &format!("{masked_a} != 0"), IntTy::U32),
            B::IsolateLowestOne => format!("(({ct})({masked_a} & (0ull - {masked_a}) & {mask}))"),
            B::IsolateHighestOne => {
                let (x, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}; {ct} {t} = {x} == 0 ? ({ct})0 : ({ct})((1ull << ({bits} - 1 - lust_leading_zeros64({x}, {bits}))) & {mask});"
                );
                t
            }
            // R13: `one_less_than_next_power_of_two() + 1`, the add
            // overflowing at core's `uint_impl!` line; the checked form
            // answers None there.
            B::NextPowerOfTwo | B::CheckedNextPowerOfTwo => {
                let (x, m, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}; uint64_t {m} = {x} <= 1 ? 0 : (({mask}) >> lust_leading_zeros64({x} - 1, {bits}));"
                );
                if b == B::NextPowerOfTwo {
                    // The `+ 1` inherits the overflow checks: off, it wraps to 0.
                    if self.p.overflow_checks {
                        let nloc = num_loc(it, false);
                        let _ = writeln!(self.out, "    if ({m} == ({mask})) lust_panic_cstr(\"attempt to add with overflow\", {nloc});");
                    }
                    let _ = writeln!(self.out, "    {ct} {t} = ({ct})({m} + 1);");
                    t
                } else {
                    let _ = writeln!(self.out, "    {ct} {t} = ({ct})(({m} + 1) & ({mask}));");
                    self.int_option_c(&t, &format!("{m} != ({mask})"), it)
                }
            }
            // R13: floor logarithms of a positive value; the unchecked
            // forms panic at the caller (`ilog` checks its base first).
            B::Ilog2 | B::Ilog10 | B::Ilog | B::CheckedIlog2 | B::CheckedIlog10 | B::CheckedIlog => {
                let (x, base, r, ok) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let pos = if sgn { format!("({a} > 0)") } else { format!("({a} != 0)") };
                let base_v = match b {
                    B::Ilog2 | B::CheckedIlog2 => "2".to_string(),
                    B::Ilog10 | B::CheckedIlog10 => "10".to_string(),
                    _ => format!("({ub} & {mask})"),
                };
                let base_ok = match b {
                    B::Ilog | B::CheckedIlog if sgn => format!("({} >= 2)", vals[1]),
                    B::Ilog | B::CheckedIlog => format!("({base_v} >= 2)"),
                    _ => "1".to_string(),
                };
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}, {base} = {base_v}; uint8_t {ok} = {base_ok} && {pos}; uint32_t {r} = 0;\n    if ({ok}) while ({x} >= {base}) {{ {x} /= {base}; {r}++; }}"
                );
                match b {
                    B::Ilog | B::Ilog2 | B::Ilog10 => {
                        if b == B::Ilog {
                            let _ = writeln!(
                                self.out,
                                "    if (!({base_ok})) lust_panic_cstr(\"base of integer logarithm must be at least 2\", {loc});"
                            );
                        }
                        let _ = writeln!(self.out, "    if (!{pos}) lust_panic_cstr(\"argument of integer logarithm must be positive\", {loc});");
                        r
                    }
                    _ => self.int_option_c(&r, &ok, IntTy::U32),
                }
            }
            B::Isqrt | B::CheckedIsqrt => {
                let root = format!("lust_isqrt64({masked_a})");
                if b == B::CheckedIsqrt {
                    self.int_option_c(&format!("(({ct}){root})"), &format!("{a} >= 0"), it)
                } else if sgn {
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    if ({a} < 0) lust_panic_cstr(\"argument of integer square root cannot be negative\", {loc}); {ct} {t} = ({ct}){root};"
                    );
                    t
                } else {
                    format!("(({ct}){root})")
                }
            }
            // `midpoint` rounds toward zero and cannot overflow:
            // opposite signs sum safely, equal signs go through the
            // unsigned bit trick on the magnitudes.
            B::IntMidpoint => {
                let masked_b = format!("({ub} & {mask})");
                if !sgn {
                    format!("(({ct})((({masked_a} & {masked_b}) + (({masked_a} ^ {masked_b}) >> 1)) & {mask}))")
                } else {
                    let (x, y, t) = (self.tmp(), self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {ct} {x} = {a}, {y} = {};", vals[1]);
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = ({x} < 0) != ({y} < 0) ? ({ct})(((int64_t){x} + (int64_t){y}) / 2) : {x} >= 0 ? ({ct})(((uint64_t){x} & (uint64_t){y}) + (((uint64_t){x} ^ (uint64_t){y}) >> 1)) : ({ct})(0ull - ((((0ull - (uint64_t){x}) & {mask}) & ((0ull - (uint64_t){y}) & {mask})) + ((((0ull - (uint64_t){x}) & {mask}) ^ ((0ull - (uint64_t){y}) & {mask})) >> 1)));"
                    );
                    t
                }
            }
            _ => "0".into(),
        }
    }

    /// The 128-bit subset of the integer methods (the checker keeps
    /// the checked, saturating, and overflowing families out for now).
    fn int128_method_c(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let _ = loc;
        let ct = int_c(it);
        let f = int_fn(it);
        let a = &vals[0];
        let x = self.tmp();
        let _ = writeln!(self.out, "    {ct} {x} = {a};");
        // A uint64 byte swap of the word `w`, as an expression.
        fn bswap(w: &str) -> String {
            let mut parts = Vec::new();
            for i in 0..8 {
                parts.push(format!("(({w} >> {}) & 0xFFull) << {}", 8 * i, 56 - 8 * i));
            }
            format!("({})", parts.join(" | "))
        }
        match b {
            B::WrappingNeg => format!("lust_{f}_sub((({ct}){{0, 0}}), {x})"),
            B::WrappingShl => format!("lust_{f}_shl({x}, {} & 127u)", vals[1]),
            B::WrappingShr => format!("lust_{f}_shr({x}, {} & 127u)", vals[1]),
            B::WrappingAbs => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t} = (int64_t){x}.hi < 0 ? lust_{f}_sub((({ct}){{0, 0}}), {x}) : {x};");
                t
            }
            B::CountOnes => format!("(lust_count_ones64({x}.lo) + lust_count_ones64({x}.hi))"),
            B::CountZeros => format!("(128u - lust_count_ones64({x}.lo) - lust_count_ones64({x}.hi))"),
            B::LeadingZeros => format!("({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64))"),
            B::TrailingZeros => format!("({x}.lo != 0 ? lust_trailing_zeros64({x}.lo, 64) : 64u + lust_trailing_zeros64({x}.hi, 64))"),
            B::LeadingOnes => format!("({x}.hi != ~0ull ? lust_leading_zeros64(~{x}.hi, 64) : 64u + lust_leading_zeros64(~{x}.lo, 64))"),
            B::TrailingOnes => format!("({x}.lo != ~0ull ? lust_trailing_zeros64(~{x}.lo, 64) : 64u + lust_trailing_zeros64(~{x}.hi, 64))"),
            B::RotateLeft | B::RotateRight => {
                let n = self.tmp();
                let _ = writeln!(self.out, "    uint32_t {n} = {} & 127u;", vals[1]);
                let t = self.tmp();
                let (o1, o2) = if b == B::RotateLeft { ("shl", "shr") } else { ("shr", "shl") };
                if it.signed() {
                    // Rotate on the unsigned bit pattern: `lust_i128_shr` is
                    // arithmetic and would fill the high bits with the sign.
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = lust_i128_from_u128(lust_u128_or(lust_u128_{o1}(lust_u128_from_i128({x}), {n}), lust_u128_{o2}(lust_u128_from_i128({x}), (128u - {n}) & 127u)));"
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = lust_u128_or(lust_{f}_{o1}({x}, {n}), lust_{f}_{o2}({x}, (128u - {n}) & 127u));"
                    );
                }
                t
            }
            B::SwapBytes => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t}; {t}.lo = {}; {t}.hi = {};", bswap(&format!("{x}.hi")), bswap(&format!("{x}.lo")));
                t
            }
            B::ReverseBits => {
                let (r, i) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {r} = {{0, 0}}; for (uint32_t {i} = 0; {i} < 64; {i}++) {{ {r}.hi |= (({x}.lo >> {i}) & 1ull) << (63 - {i}); {r}.lo |= (({x}.hi >> {i}) & 1ull) << (63 - {i}); }}"
                );
                r
            }
            B::Signum => {
                let (t, c) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {t} = {{0, 0}}; int32_t {c} = lust_i128_cmp({x}, {t}); {t}.lo = (uint64_t)(int64_t){c}; {t}.hi = (uint64_t)((int64_t){c} >> 63);"
                );
                t
            }
            B::IsPositive => format!("((int64_t){x}.hi > 0 || ({x}.hi == 0 && {x}.lo != 0))"),
            B::IsNegative => format!("((int64_t){x}.hi < 0)"),
            B::IsPowerOfTwo => format!("(lust_count_ones64({x}.lo) + lust_count_ones64({x}.hi) == 1)"),
            B::IsMultipleOf => {
                let (y, r, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {y} = {}; {ct} {r} = {{0, 0}}; int {t} = ({y}.lo == 0 && {y}.hi == 0) ? ({x}.lo == 0 && {x}.hi == 0) : (lust_u128_divmod({x}, {y}, &{r}), {r}.lo == 0 && {r}.hi == 0);",
                    vals[1]
                );
                t
            }
            B::UnboundedShl => format!("(({}) >= 128u ? (({ct}){{0, 0}}) : lust_{f}_shl({x}, {}))", vals[1], vals[1]),
            B::UnboundedShr => {
                if it.signed() {
                    format!("(({}) >= 128u ? (({ct}){{(uint64_t)((int64_t){x}.hi >> 63), (uint64_t)((int64_t){x}.hi >> 63)}}) : lust_{f}_shr({x}, {}))", vals[1], vals[1])
                } else {
                    format!("(({}) >= 128u ? (({ct}){{0, 0}}) : lust_{f}_shr({x}, {}))", vals[1], vals[1])
                }
            }
            B::CastSigned => format!("lust_i128_from_u128({x})"),
            B::CastUnsigned => format!("lust_u128_from_i128({x})"),
            B::UnsignedAbs => {
                let t = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    lust_u128 {t} = lust_u128_from_i128((int64_t){x}.hi < 0 ? lust_i128_sub(((lust_i128){{0, 0}}), {x}) : {x});"
                );
                t
            }
            B::NextMultipleOf | B::CheckedNextMultipleOf => {
                let (y, r, add, t) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let nloc = num_loc(it, false);
                let _ = writeln!(self.out, "    {ct} {y} = {};", vals[1]);
                if b == B::NextMultipleOf {
                    let _ = writeln!(
                        self.out,
                        "    if ({y}.lo == 0 && {y}.hi == 0) lust_panic_cstr(\"attempt to calculate the remainder with a divisor of zero\", {nloc});"
                    );
                }
                let _ = writeln!(
                    self.out,
                    "    {ct} {r} = {{0, 0}}; if ({y}.lo != 0 || {y}.hi != 0) lust_u128_divmod({x}, {y}, &{r}); {ct} {add} = ({r}.lo == 0 && {r}.hi == 0) ? (({ct}){{0, 0}}) : lust_u128_sub({y}, {r}); {ct} {t} = lust_u128_add({x}, {add});"
                );
                if b == B::NextMultipleOf {
                    if self.p.overflow_checks {
                        let _ = writeln!(
                            self.out,
                            "    if (lust_u128_cmp({t}, {x}) < 0) lust_panic_cstr(\"attempt to add with overflow\", {nloc});"
                        );
                    }
                    t
                } else {
                    self.int_option_c(&t, &format!("({y}.lo != 0 || {y}.hi != 0) && lust_u128_cmp({t}, {x}) >= 0"), it)
                }
            }
            B::BitWidth => format!("(128u - ({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64)))"),
            B::HighestOne => self.int_option_c(
                &format!("(127u - ({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64)))"),
                &format!("({x}.lo != 0 || {x}.hi != 0)"),
                IntTy::U32,
            ),
            B::LowestOne => self.int_option_c(
                &format!("({x}.lo != 0 ? lust_trailing_zeros64({x}.lo, 64) : 64u + lust_trailing_zeros64({x}.hi, 64))"),
                &format!("({x}.lo != 0 || {x}.hi != 0)"),
                IntTy::U32,
            ),
            B::IsolateLowestOne => format!("lust_{f}_and({x}, lust_{f}_sub((({ct}){{0, 0}}), {x}))"),
            B::IsolateHighestOne => {
                let (lz, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint32_t {lz} = {x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64); {ct} {t} = ({x}.lo == 0 && {x}.hi == 0) ? (({ct}){{0, 0}}) : lust_{f}_shl((({ct}){{1, 0}}), 127u - {lz});"
                );
                t
            }
            _ => "0".into(),
        }
    }

    /// The C for one inherent float method: mostly the libm call Rust
    /// lowers to, with lust wrappers where Rust's semantics differ.
    fn float_method_c(&mut self, b: Builtin, vals: &[String], tys: &[CTy]) -> String {
        use Builtin as B;
        if matches!(b, B::F32FromBits | B::F64FromBits) {
            return if b == B::F64FromBits {
                format!("lust_f64_from_bits_of({})", vals[0])
            } else {
                format!("lust_f32_from_bits_of({})", vals[0])
            };
        }
        let f = match &tys[0] {
            CTy::Float(f) => *f,
            _ => FloatTy::F64,
        };
        let a = &vals[0];
        let suf = if f == FloatTy::F32 { "f" } else { "" };
        let w = if f == FloatTy::F32 { "f32" } else { "f64" };
        let ct = ctype(&tys[0]);
        match b {
            B::FloatSqrt => format!("sqrt{suf}({a})"),
            B::FloatPowi => format!("lust_{w}_powi({a}, {})", vals[1]),
            B::FloatPowf => format!("pow{suf}({a}, {})", vals[1]),
            B::FloatExp => format!("exp{suf}({a})"),
            B::FloatLn => format!("log{suf}({a})"),
            B::FloatLog => format!("(log{suf}({a}) / log{suf}({}))", vals[1]),
            B::FloatLog2 => format!("log2{suf}({a})"),
            B::FloatLog10 => format!("log10{suf}({a})"),
            B::FloatMulAdd => format!("fma{suf}({a}, {}, {})", vals[1], vals[2]),
            B::FloatFloor => format!("floor{suf}({a})"),
            B::FloatCeil => format!("ceil{suf}({a})"),
            B::FloatRound => format!("round{suf}({a})"),
            B::FloatTrunc => format!("trunc{suf}({a})"),
            B::FloatFract => format!("(({a}) - trunc{suf}({a}))"),
            B::FloatAbs => format!("fabs{suf}({a})"),
            B::FloatSignum => format!("lust_{w}_signum({a})"),
            B::FloatRecip => format!("((({ct})1) / ({a}))"),
            B::FloatMin => format!("lust_{w}_min({a}, {})", vals[1]),
            B::FloatMax => format!("lust_{w}_max({a}, {})", vals[1]),
            B::FloatCopysign => format!("copysign{suf}({a}, {})", vals[1]),
            B::FloatIsNan => format!("({a} != {a})"),
            B::FloatIsInfinite => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) & 0x7FFFFFFFul) == 0x7F800000ul)")
                } else {
                    format!("((lust_f64_to_bits({a}) & 0x7FFFFFFFFFFFFFFFull) == 0x7FF0000000000000ull)")
                }
            }
            B::FloatIsFinite => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) & 0x7FFFFFFFul) < 0x7F800000ul)")
                } else {
                    format!("((lust_f64_to_bits({a}) & 0x7FFFFFFFFFFFFFFFull) < 0x7FF0000000000000ull)")
                }
            }
            B::FloatIsSignPositive => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) >> 31) == 0)")
                } else {
                    format!("((lust_f64_to_bits({a}) >> 63) == 0)")
                }
            }
            B::FloatIsSignNegative => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) >> 31) == 1)")
                } else {
                    format!("((lust_f64_to_bits({a}) >> 63) == 1)")
                }
            }
            B::FloatToBits => format!("lust_{w}_to_bits({a})"),
            _ => "0".into(),
        }
    }
}

// ---------- Compilation units ----------
//
// Unit 0 holds the globals and `main`. Unit 1 holds the shared glue
// (see `GlueSet`); other glue is static in the function units. Unit 4
// holds the per-slot location tables (`loc_unit`). The other units
// hold functions, in groups the driver sizes by C bytes and freezes
// between fresh bases, so an edit that keeps the program's shape
// recompiles only the units it touches (plus unit 0).

/// Function groups for units 2 and up, fixed slot counts. Kept for
/// tests that build units by hand; the driver groups by bytes below.
#[allow(dead_code)]
pub fn group_fns(n: usize, per_unit: usize) -> Vec<std::ops::Range<usize>> {
    (0..n).step_by(per_unit.max(1)).map(|a| a..(a + per_unit).min(n)).collect()
}

/// Function groups sized by generated C bytes: slots in order, a new
/// group when the next slot would push the current one past `target`
/// bytes. A single slot over the target forms its own group, and a
/// group holds at most 4096 slots so a run of empty slots (templates,
/// stubs) cannot make one unit's register function huge. Equal byte
/// sizes give tcc units of near equal cost, where a fixed slot count
/// makes one unit of large functions the tail of the whole compile.
pub fn group_fns_by_bytes(sizes: &[usize], target: usize) -> Vec<std::ops::Range<usize>> {
    let target = target.max(1);
    let mut groups = Vec::new();
    let (mut start, mut bytes) = (0usize, 0usize);
    for (i, &size) in sizes.iter().enumerate() {
        if i > start && (bytes + size > target || i - start >= 4096) {
            groups.push(start..i);
            start = i;
            bytes = 0;
        }
        bytes += size;
    }
    if start < sizes.len() {
        groups.push(start..sizes.len());
    }
    groups
}

/// All glue needed by a set of functions, closed over field types.
//
// Glue placement is hybrid. `shared` holds the keys that live once in the glue unit (unit 1):
// glue that many function units reach (see `compute_shared`). Every other key is emitted as a
// static copy in each function unit that reaches it, so an edit that needs new glue does not
// rebuild the glue unit. `shared` is None until the first `compute_shared`; before that, all
// glue lives in the glue unit, as before.
//
// The maps hash with FxHash: a key is a C type tree, and every glue lookup hashes it (SipHash
// made the release C shard cut and the glue refresh pay for each one). Only `defs` follows
// map order, where order does not matter (see `regen`); every other reader sorts.
#[derive(Default)]
pub struct GlueSet {
    pub protos: crate::intern::FxMap<(Glue, CTy), String>,
    defs: String,
    /// `defs` is not kept up to date: its one reader, the glue unit with no shared set
    /// (`glue_unit`), makes it from `def_map` then. A set keeps `defs` only until a shared set
    /// is picked (the first build), as a refresh that changed a definition rebuilt it for
    /// nothing after that (7 ms for tsgo).
    defs_stale: bool,
    /// Each key's definition on its own, so units can carry static copies of just what they reach.
    def_map: crate::intern::FxMap<(Glue, CTy), String>,
    /// The glue keys each key's definition calls.
    deps: crate::intern::FxMap<(Glue, CTy), Vec<(Glue, CTy)>>,
    /// C types each key's definition names beyond its key type: the signature of a written
    /// method it calls (`glue_callee`). A unit that defines the key must declare them.
    types: crate::intern::FxMap<(Glue, CTy), Vec<CTy>>,
    /// Keys that live in the shared glue unit. Frozen until the next `compute_shared`.
    pub shared: Option<crate::intern::FxSet<(Glue, CTy)>>,
    /// Keys the last `refresh` did not reach: their text may predate a type edit. `add`
    /// regenerates one when a body reaches it again.
    stale: crate::intern::FxSet<(Glue, CTy)>,
    /// Fn slots as of the last `add` or `refresh`: fn pointers in static
    /// data (`ConstValue::FnPtr`) name their slot's trampoline.
    slots: Vec<u32>,
    /// The fn slots each key's definition prints (a written method it
    /// calls, see `glue_callee`), as `FnOut::used`.
    used: crate::intern::FxMap<(Glue, CTy), Vec<u32>>,
    /// Release C: the extern declarations each key's definition needs (`FnOut::externs`).
    externs: crate::intern::FxMap<(Glue, CTy), BTreeSet<String>>,
}

impl GlueSet {
    /// Adds glue for `keys` and everything it needs: new keys, and keys the last `refresh` did
    /// not reach (`stale`), which are regenerated and compared as `refresh` does. Returns
    /// (shared unit content changed, an existing definition changed), as `refresh`. New glue
    /// that no unit shared at freeze time is not in `shared`, so it does not count as a shared
    /// change: the new glue is static in the function units that reach it.
    pub fn add<'k>(&mut self, p: &Program, slots: &[u32], keys: impl Iterator<Item = &'k (Glue, CTy)>) -> (bool, bool) {
        self.slots = slots.to_vec();
        let roots: Vec<(Glue, CTy)> = keys.filter(|k| !self.protos.contains_key(k) || self.stale.contains(k)).cloned().collect();
        self.regen(p, slots, &roots.iter().collect::<Vec<_>>(), false)
    }

    /// Regenerates every reached key's definition from the current
    /// program and replaces the stored text where it differs. A derived
    /// impl (Debug, Clone, Eq, Drop glue) is generated from the Adt's
    /// field and variant types, but its key is only the Adt id: a field
    /// type edit keeps the key, so `add` alone would keep the old text
    /// (a stale Debug body, or C that names a field the new layout form
    /// does not have). The driver calls this when type definitions may
    /// have changed. Returns (shared unit content changed, any existing
    /// definition changed); new keys are added as in `add`. Comparing
    /// the generated text is exact by construction: no second
    /// fingerprint of what `glue_def` reads to keep in sync.
    ///
    /// Keys that no live body reaches now are not regenerated (their
    /// Adt may be gone). They become `stale`, so the next `add` that
    /// reaches one regenerates it: a type edit in a version that does
    /// not use the glue must still reach the version that uses it again.
    pub fn refresh<'k>(&mut self, p: &Program, slots: &[u32], keys: impl Iterator<Item = &'k (Glue, CTy)>) -> (bool, bool) {
        self.slots = slots.to_vec();
        self.regen(p, slots, &keys.collect::<Vec<_>>(), true)
    }

    /// The walk behind `add` and `refresh`: makes each root and its deps. With `all` false, a key
    /// already stored and not stale is kept as is (and its deps are not walked); with `all`, the
    /// stored keys the walk does not reach become stale. Returns the change flags.
    ///
    /// The walk takes the roots from the last one back and a made key's deps before the roots
    /// under them; that order decides where a new definition joins `defs`. What it does with
    /// each key is worked out first (`plan`): a definition is a function of the program, the
    /// slots and the key alone (`glue_def`), so each level of new keys is made on the pool and
    /// compared with the stored entry there. The walk then runs over key indices and touches
    /// the set only where an entry changed (a refresh walks about 0.5 M roots and 23k keys for
    /// tsgo, and made all of them on one thread, 0.2-0.3 s).
    fn regen(&mut self, p: &Program, slots: &[u32], roots: &[&(Glue, CTy)], all: bool) -> (bool, bool) {
        let mut plan = self.plan(p, slots, roots, all);
        let (mut made, mut pending) = (std::mem::take(&mut plan.made), std::mem::take(&mut plan.roots));
        let keys = &plan.keys;
        let mut seen = vec![false; keys.len()];
        let (mut shared_changed, mut regenerated) = (false, false);
        while let Some(i) = pending.pop() {
            let i = i as usize;
            if std::mem::replace(&mut seen[i], true) {
                continue;
            }
            let Some(m) = made[i].take() else { continue };
            let g = &keys[i];
            if m.was_stale {
                self.stale.remove(g);
                // `glue_unit` leaves stale keys out, so a shared one coming back must rebuild it.
                shared_changed |= self.is_shared(g);
            }
            if !m.same_used {
                self.used.insert(g.clone(), m.used);
                self.externs.insert(g.clone(), m.externs);
            }
            if !m.same {
                regenerated |= !m.is_new;
                shared_changed |= self.shared.as_ref().is_none_or(|s| s.contains(g));
                if m.is_new {
                    self.push_def(&m.def);
                }
                self.def_map.insert(g.clone(), m.def);
                self.deps.insert(g.clone(), m.more);
                self.types.insert(g.clone(), m.types);
                self.protos.insert(g.clone(), m.proto);
            }
            pending.extend(m.more_ids);
        }
        if regenerated && !self.defs_stale() {
            // `defs` is the pre-hybrid concatenation; rebuild it from the
            // per-key map. Order does not matter: prototypes precede it.
            self.defs = self.def_map.values().cloned().collect();
        }
        if all {
            // The stored keys the walk did not reach, found on the pool.
            let have: Vec<&(Glue, CTy)> = self.protos.keys().collect();
            let gone = crate::pool::par_map(&have, |k| plan.get(k).is_none_or(|i| !seen[i as usize]));
            let stale = have.into_iter().zip(gone).filter(|&(_, gone)| gone).map(|(k, _)| k.clone()).collect();
            self.stale = stale;
        }
        (shared_changed, regenerated)
    }

    /// True when `defs` is not kept (`defs_stale`): a shared set is picked. It frees `defs` then.
    fn defs_stale(&mut self) -> bool {
        if !self.defs_stale && self.shared.is_some() {
            self.defs_stale = true;
            self.defs = String::new();
        }
        self.defs_stale
    }

    /// Adds a new key's definition to `defs` while the set keeps it.
    fn push_def(&mut self, def: &str) {
        if !self.defs_stale() {
            self.defs.push_str(def);
        }
    }

    /// `regen`'s keys, numbered: the roots in order and every key the walk reaches (a made key's
    /// deps), with the made definition and its verdicts for each key the walk makes (new,
    /// stale, or with `all` any). Each level of new keys is made on the pool, under the
    /// caller's release names and in one layout phase (the program is frozen meanwhile).
    fn plan(&self, p: &Program, slots: &[u32], roots: &[&(Glue, CTy)], all: bool) -> Plan {
        let makes = |g: &(Glue, CTy)| all || !self.protos.contains_key(g) || self.stale.contains(g);
        let mut plan = Plan::of_roots(roots);
        // The roots' keys are new to the plan: those to make, in the order they first appear.
        let mut level: Vec<u32> = (0..plan.keys.len() as u32).filter(|&i| makes(&plan.keys[i as usize])).collect();
        let (names, tag) = (names::current(), layout_phase());
        while !level.is_empty() {
            let make = |&i: &u32| in_layout_phase(tag, || names::with(names.as_ref(), || Made::of(p, slots, &plan.keys[i as usize], self)));
            let outs: Vec<Made> = if level.len() >= 64 { crate::pool::par_map(&level, make) } else { level.iter().map(make).collect() };
            let mut next = Vec::new();
            for (&i, mut m) in level.iter().zip(outs) {
                m.more_ids = m
                    .more
                    .iter()
                    .map(|d| {
                        let (j, new) = plan.id(d);
                        if new && makes(d) {
                            next.push(j);
                        }
                        j
                    })
                    .collect();
                plan.made.resize_with(plan.keys.len(), || None);
                plan.made[i as usize] = Some(m);
            }
            level = next;
        }
        plan.made.resize_with(plan.keys.len(), || None);
        plan
    }

    /// True when a live definition (stale ones are emitted nowhere)
    /// prints a slot `dead` names. The driver refreshes the glue then:
    /// that callee's identity moved to a new slot since the text was made.
    pub fn prints_slot(&self, dead: impl Fn(u32) -> bool) -> bool {
        self.used.iter().any(|(k, used)| !self.stale.contains(k) && used.iter().any(|&s| dead(s)))
    }

    /// The glue keys a set of direct needs reaches, deps included (FxHash: tsgo's fns name
    /// 126k roots).
    fn closure<'a>(&'a self, roots: impl Iterator<Item = &'a (Glue, CTy)>) -> crate::intern::FxSet<&'a (Glue, CTy)> {
        let mut seen = crate::intern::FxSet::default();
        let mut stack: Vec<&(Glue, CTy)> = roots.collect();
        while let Some(k) = stack.pop() {
            if seen.insert(k) {
                if let Some(deps) = self.deps.get(k) {
                    stack.extend(deps.iter());
                }
            }
        }
        seen
    }

    /// Picks the shared set: keys reached by at least `k` function units (`fns` is indexed by
    /// slot, `groups` are the units). The set is closed over deps, so the shared glue unit's
    /// definitions only call each other. Call this only on a fresh base, then keep it frozen:
    /// a key that turned shared later would need the base glue unit rebuilt.
    pub fn compute_shared(&mut self, fns: &[FnOut], groups: &[std::ops::Range<usize>], k: usize) {
        let mut count: crate::intern::FxMap<&(Glue, CTy), usize> = crate::intern::FxMap::default();
        for range in groups {
            for key in self.closure(fns[range.clone()].iter().flat_map(|f| f.glue.iter())) {
                *count.entry(key).or_default() += 1;
            }
        }
        let mut shared: crate::intern::FxSet<(Glue, CTy)> = count.into_iter().filter(|&(_, n)| n >= k).map(|(key, _)| key.clone()).collect();
        // Close over deps (the count already implies this, but keep the glue unit self-contained).
        let mut stack: Vec<(Glue, CTy)> = shared.iter().cloned().collect();
        while let Some(key) = stack.pop() {
            if let Some(deps) = self.deps.get(&key) {
                for dep in deps {
                    if shared.insert(dep.clone()) {
                        stack.push(dep.clone());
                    }
                }
            }
        }
        self.shared = Some(shared);
    }

    fn is_shared(&self, k: &(Glue, CTy)) -> bool {
        self.shared.as_ref().is_some_and(|s| s.contains(k))
    }

    /// Adds the C types that the definition of `k` names to `out`: its key type and the
    /// types in `types`. A unit that holds the definition must declare all of them.
    fn def_types(&self, k: &(Glue, CTy), out: &mut HashSet<CTy>) {
        collect_types(&k.1, out);
        self.types.get(k).into_iter().flatten().for_each(|t| collect_types(t, out));
    }

    /// True for the glue of a struct, enum, Option, Result, tuple, array or RefCell that
    /// copies its fields or passes each field's address to the field's own glue: drop,
    /// clone, eq, the comparisons, default, and a thread-local cell's init and destructor;
    /// and for a Mutex's or RwLock's drop and default, which do that with the value. It
    /// reads through none of the pointers it holds (an Rc's glue reads the counts, a Vec's
    /// its elements). Debug and hash glue expand a pointer field's value in place.
    fn passes_fields(k: &(Glue, CTy)) -> bool {
        match &k.1 {
            CTy::Adt(_) | CTy::Option(_) | CTy::Result(..) | CTy::Tuple(_) | CTy::Array(..) | CTy::RefCell(_) => {
                matches!(k.0, Glue::Drop | Glue::Clone | Glue::Eq | Glue::Cmp | Glue::PCmp | Glue::Default | Glue::TlsInit | Glue::TlsDtor)
            }
            CTy::Sync(s, _) => s.is_lock() && matches!(k.0, Glue::Drop | Glue::Default),
            _ => false,
        }
    }

    /// The blocks that a pointer's drop or clone glue reads in place, as a unit defines them:
    /// the count block (`RcI_T`) of an Rc, Weak, Arc or Arc's Weak; the element of a Box,
    /// Vec, boxed slice or Vec iterator, by the types that hold it by value (`by_value_deps`:
    /// a boxed slice element is its slice struct, an Rc element a pointer with no block); the
    /// cell a RefCell guard gives its borrow back to; the lock a lock guard unlocks. The glue
    /// holds them by value and passes the value in them to the value's own glue by pointer, so
    /// it reads none of the value's fields.
    fn pointer_block(k: &(Glue, CTy)) -> Option<Vec<CTy>> {
        use crate::ty::sync::SyncTy;
        if !matches!(k.0, Glue::Drop | Glue::Clone) {
            return None;
        }
        match &k.1 {
            CTy::Rc(e) | CTy::Weak(e) | CTy::Sync(SyncTy::Arc | SyncTy::ArcWeak, e) => Some(vec![CTy::Rc(e.clone())]),
            CTy::Boxed(e) | CTy::Vec(e) | CTy::BoxSlice(e) | CTy::VecIter(e) | CTy::VecDrain(e) => {
                let mut held = Vec::new();
                by_value_deps(e, &mut held);
                Some(held)
            }
            CTy::Guard(e, _) => Some(vec![CTy::RefCell(e.clone())]),
            CTy::Sync(s, e) => s.guard().map(|(lock, _)| vec![CTy::Sync(lock, e.clone())]),
            _ => None,
        }
    }

    /// `def_types` for a definition that `passes_fields` or reads only its `pointer_block`:
    /// the types it holds by value (its key type, whose fields it reads) go to `held`, and
    /// every type it names to `named`, which a unit only declares.
    fn held_types(&self, k: &(Glue, CTy), held: &mut HashSet<CTy>, named: &mut HashSet<CTy>) {
        let mut by_value = Vec::new();
        by_value_deps(&k.1, &mut by_value);
        self.types.get(k).into_iter().flatten().for_each(|t| by_value_deps(t, &mut by_value));
        held.extend(by_value);
        self.def_types(k, named);
    }
}

/// `GlueSet::regen`'s keys and what its walk does with each (`GlueSet::plan`).
struct Plan {
    /// Every key the walk reaches, by index.
    keys: Vec<(Glue, CTy)>,
    /// Each key's index, in shards by the key's hash (`key_hash`), so the roots' shards fill
    /// on the pool.
    index: Vec<crate::intern::FxMap<(Glue, CTy), u32>>,
    /// The roots' indices, in order.
    roots: Vec<u32>,
    /// By index: the key's new definition, when the walk makes it.
    made: Vec<Option<Made>>,
}

/// A glue key's FxHash, which `Plan` shards its index by.
fn key_hash(g: &(Glue, CTy)) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = crate::intern::FxHasher::default();
    g.hash(&mut h);
    h.finish()
}

/// A root's key with its hash, made once (`Plan::of_roots`): a map of them hashes only that.
struct Hashed<'a>(u64, &'a (Glue, CTy));

impl std::hash::Hash for Hashed<'_> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0);
    }
}

impl PartialEq for Hashed<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl Eq for Hashed<'_> {}

impl Plan {
    /// The plan of `roots` alone: their keys numbered in the order they first appear, and
    /// each root's key index, as numbering the roots in turn (`id`) gives. A refresh numbers
    /// 126k roots of 18.6k keys for tsgo (19 ms on one thread): here the roots hash on the
    /// pool, each shard of their hashes finds its keys' first places there, and the index
    /// fills a shard per task.
    fn of_roots(roots: &[&(Glue, CTy)]) -> Plan {
        let n_shards = (crate::pool::threads() * 4).max(1);
        let shard = |h: u64| (h % n_shards as u64) as usize;
        let hashes: Vec<u64> = crate::pool::par_map(roots, |g| key_hash(g));
        let mut by_shard: Vec<Vec<u32>> = vec![Vec::new(); n_shards];
        hashes.iter().enumerate().for_each(|(at, &h)| by_shard[shard(h)].push(at as u32));
        // Each root's place and its key's first place, a shard per task.
        let firsts: Vec<Vec<(u32, u32)>> = crate::pool::par_map(&by_shard, |ats| {
            let mut first: std::collections::HashMap<Hashed, u32, std::hash::BuildHasherDefault<crate::intern::FxHasher>> = Default::default();
            ats.iter().map(|&at| (at, *first.entry(Hashed(hashes[at as usize], roots[at as usize])).or_insert(at))).collect()
        });
        let mut first = vec![0u32; roots.len()];
        firsts.iter().flatten().for_each(|&(at, f)| first[at as usize] = f);
        // The keys by their first places, in order.
        let places: Vec<u32> = (0..roots.len() as u32).filter(|&at| first[at as usize] == at).collect();
        let mut id_at = vec![0u32; roots.len()];
        places.iter().enumerate().for_each(|(i, &at)| id_at[at as usize] = i as u32);
        let keys: Vec<(Glue, CTy)> = crate::pool::par_map(&places, |&at| roots[at as usize].clone());
        let mut of_shard: Vec<Vec<u32>> = vec![Vec::new(); n_shards];
        places.iter().enumerate().for_each(|(i, &at)| of_shard[shard(hashes[at as usize])].push(i as u32));
        let index = crate::pool::par_map(&of_shard, |is| is.iter().map(|&i| (keys[i as usize].clone(), i)).collect());
        Plan { roots: first.iter().map(|&f| id_at[f as usize]).collect(), keys, index, made: Vec::new() }
    }

    fn shard(&self, g: &(Glue, CTy)) -> usize {
        (key_hash(g) % self.index.len() as u64) as usize
    }

    /// The index of key `g`, when the plan has it.
    fn get(&self, g: &(Glue, CTy)) -> Option<u32> {
        self.index[self.shard(g)].get(g).copied()
    }

    /// The index of key `g`, and whether it is new.
    fn id(&mut self, g: &(Glue, CTy)) -> (u32, bool) {
        let s = self.shard(g);
        if let Some(&i) = self.index[s].get(g) {
            return (i, false);
        }
        let i = self.keys.len() as u32;
        self.keys.push(g.clone());
        self.index[s].insert(g.clone(), i);
        (i, true)
    }
}

/// One glue key's definition and what it needs (`glue_def`), as `GlueSet` stores them, and how
/// they compare with the stored entry.
struct Made {
    proto: String,
    def: String,
    more: Vec<(Glue, CTy)>,
    /// `more` as `Plan` indices.
    more_ids: Vec<u32>,
    types: Vec<CTy>,
    used: Vec<u32>,
    externs: BTreeSet<String>,
    /// No stored entry.
    is_new: bool,
    was_stale: bool,
    /// The stored definition, prototype, deps and types are these.
    same: bool,
    /// The stored slots and extern declarations are these.
    same_used: bool,
}

impl Made {
    fn of(p: &Program, slots: &[u32], g: &(Glue, CTy), set: &GlueSet) -> Made {
        let (mut proto, mut def, mut more, mut types) = (String::new(), String::new(), Vec::new(), Vec::new());
        let rec = Slots::new(slots);
        glue_def(p, &rec, &g.0, &g.1, &mut proto, &mut def, &mut more, &mut types);
        // The set keeps every entry (the front image saves it): no growth slack.
        proto.shrink_to_fit();
        def.shrink_to_fit();
        more.shrink_to_fit();
        types.shrink_to_fit();
        let (mut used, externs) = rec.into_used();
        used.shrink_to_fit();
        let is_new = !set.protos.contains_key(g);
        let same = !is_new
            && set.def_map.get(g) == Some(&def)
            && set.protos.get(g) == Some(&proto)
            && set.deps.get(g) == Some(&more)
            && set.types.get(g) == Some(&types);
        let same_used = set.used.get(g) == Some(&used) && set.externs.get(g) == Some(&externs);
        Made { proto, def, more, more_ids: Vec::new(), types, used, externs, is_new, was_stale: set.stale.contains(g), same, same_used }
    }
}

/// True for an enum whose variants have no fields and whose `==` is structural (no
/// written `PartialEq`): two values are equal when their discriminants are.
fn fieldless_enum(p: &Program, t: &CTy) -> bool {
    let CTy::Adt(a) = t else { return false };
    let adt = p.adt(*a);
    adt.is_enum
        && !adt.variants.is_empty()
        && adt.variants.iter().all(|v| v.fields.is_empty())
        && !p.gx.glue_methods.contains_key(&(*a, p.gx.lang.partial_eq))
}

/// The runtime's panic entry points, declared again as noreturn and cold for a unit of a
/// program with unwind tables: there they throw (mode 2) or abort (mode 0), never return,
/// so the C compiler drops the code after them and keeps them out of the hot path.
fn noreturn_decls() -> &'static str {
    static DECLS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    DECLS.get_or_init(|| {
        const NAMES: &[&str] = &[
            "lust_panic_at", "lust_panic", "lust_panic_lit", "lust_panic_fmt", "lust_panic_dyn", "lust_panic_cstr_dyn",
            "lust_panic_str", "lust_panic_cstr", "lust_panic_cstr_owned", "lust_panic_std", "lust_panic_std_lit",
            "lust_panic_read_buf_overrun", "lust_panic_box", "lust_oom", "lust_oom_size", "lust_vec_capacity_overflow",
            "lust_panic_nn",
        ];
        let mut out = String::new();
        for line in runtime_decls().lines() {
            let l = line.trim();
            if let Some(rest) = l.strip_prefix("void ")
                && let Some((name, _)) = rest.split_once('(')
                && NAMES.contains(&name)
                && l.ends_with(';')
            {
                let _ = writeln!(out, "__attribute__((noreturn, cold)) {l}");
            }
        }
        out
    })
}

pub(crate) fn unit_header() -> String {
    let mut c = String::with_capacity(64 * 1024);
    c.push_str(runtime_decls());
    c.push('\n');
    // After the declarations: inline fast paths of hot helpers for non-tcc units.
    c.push_str(include_str!("runtime/inl.h"));
    c
}

/// The full runtime source, assembled from `src/runtime/`: runtime.h first, then core.c
/// with its `#include` lines replaced by the included text (panic.c inline; float.h and
/// hash.h at the end). Units compile from strings, so file includes cannot read files;
/// declaration units get float.h's prototypes only (`with_impls` false),
/// the runtime unit gets float.c's and hash.c's bodies too. The runtime stays one
/// amalgamated unit (see `runtime_unit`), so the split files are source fragments, not
/// separate translation units, and the includes are also what a plain C compiler
/// follows when a test harness includes runtime.h and core.c directly. The panic
/// include sits where the panic section belonged in the old single runtime.c: after
/// the string helpers it calls, before the checked math that calls it.
fn runtime_source(with_impls: bool) -> String {
    let header = include_str!("runtime/float.h");
    let header = if with_impls {
        let body = include_str!("runtime/float.c").replacen("#include \"ryu_tables.h\"", include_str!("runtime/ryu_tables.h"), 1);
        header.replacen("#include \"float.c\"", &body, 1)
    } else {
        header.replacen("#include \"float.c\"", "", 1)
    };
    let fmt = include_str!("runtime/fmt.h");
    let fmt = fmt.replacen("#include \"fmt.c\"", if with_impls { include_str!("runtime/fmt.c") } else { "" }, 1);
    // The hash core's declarations are not in the common unit header:
    // they cost about 26 KB of C per unit and no generated code calls
    // the core yet. The runtime unit carries header plus bodies, so
    // the symbols link; a unit whose code calls the core adds
    // `hash_decls()` to its header.
    let hash = if with_impls { hash_source(true) } else { String::new() };
    let deps = include_str!("runtime/deps.h").replacen("#include \"deps.c\"", if with_impls { include_str!("runtime/deps.c") } else { "" }, 1);
    let core = include_str!("runtime/core.c")
        .replacen("#include \"escape_table.h\"", include_str!("runtime/escape_table.h"), 1)
        .replacen("#include \"unicode_table.h\"", include_str!("runtime/unicode_table.h"), 1);
    // The Unicode case tables (W-STD-B) only where the bodies are.
    let core = core.replacen("#include \"case_tables.h\"", if with_impls { include_str!("runtime/case_tables.h") } else { "" }, 1);
    let (h, core, panic) = (include_str!("runtime/runtime.h"), core.as_str(), include_str!("runtime/panic.c"));
    let mut src = String::with_capacity(h.len() + core.len() + panic.len() + header.len() + hash.len());
    src.push_str(h);
    src.push_str(core);
    let src = src.replacen("#include \"panic.c\"\n", panic, 1);
    let src = src.replacen("#include \"thread.c\"\n", include_str!("runtime/thread.c"), 1);
    let src = src.replacen("#include \"kconst.c\"\n", include_str!("runtime/kconst.c"), 1);
    let src = src.replacen("#include \"float.h\"", &header, 1);
    let src = src.replacen("#include \"fmt.h\"", &fmt, 1);
    let src = src.replacen("#include \"sort.h\"", include_str!("runtime/sort.h"), 1);
    let src = src.replacen("#include \"hash.h\"", &hash, 1);
    let src = src.replacen("#include \"deps.h\"", &deps, 1);
    let src = src.replacen("#include \"sync.c\"\n", include_str!("runtime/sync.c"), 1);
    let stdc =
        include_str!("runtime/stdc.h").replacen("#include \"stdc.c\"", if with_impls { include_str!("runtime/stdc.c") } else { "" }, 1);
    let src = src.replacen("#include \"stdc.h\"", &stdc, 1);
    let sys_body = include_str!("runtime/sys.c").replacen("#include \"syswin.c\"", include_str!("runtime/syswin.c"), 1);
    let sys = include_str!("runtime/sys.h").replacen("#include \"sys.c\"", if with_impls { &sys_body } else { "" }, 1);
    let src = src.replacen("#include \"sys.h\"", &sys, 1);
    let sysio_body = include_str!("runtime/sysio.c").replacen("#include \"sysiowin.c\"", include_str!("runtime/sysiowin.c"), 1);
    let sysio = include_str!("runtime/sysio.h").replacen("#include \"sysio.c\"", if with_impls { &sysio_body } else { "" }, 1);
    let src = src.replacen("#include \"sysio.h\"", &sysio, 1);
    let sysnet_body = include_str!("runtime/sysnet.c").replacen("#include \"sysnetwin.c\"", include_str!("runtime/sysnetwin.c"), 1);
    let sysnet = include_str!("runtime/sysnet.h").replacen("#include \"sysnet.c\"", if with_impls { &sysnet_body } else { "" }, 1);
    let src = src.replacen("#include \"sysnet.h\"", &sysnet, 1);
    let sysx_body = include_str!("runtime/sysx.c").replacen("#include \"sysxwin.c\"", include_str!("runtime/sysxwin.c"), 1);
    let sysx = include_str!("runtime/sysx.h").replacen("#include \"sysx.c\"", if with_impls { &sysx_body } else { "" }, 1);
    src.replacen("#include \"sysx.h\"", &sysx, 1)
}

/// Removes C comments, replacing each with one space (the C meaning of a
/// comment). String and char literals pass through untouched. The
/// runtime header is about a third comments by bytes, and every unit
/// would otherwise make tcc lex them again.
fn strip_c_comments(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => {
                let quote = b[i];
                let start = i;
                i += 1;
                while i < b.len() && b[i] != quote {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
                i = (i + 1).min(b.len());
                out.push_str(&src[start..i]);
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'*' => {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(b.len());
                out.push(' ');
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'/' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                out.push(' ');
            }
            _ => {
                let start = i;
                while i < b.len() && b[i] != b'"' && b[i] != b'\'' && b[i] != b'/' {
                    i += 1;
                }
                if i == start {
                    i += 1;
                    out.push('/');
                } else {
                    out.push_str(&src[start..i]);
                }
            }
        }
    }
    out
}

/// One conditional group in `strip_impl_blocks`.
enum ImplFrame {
    /// A conditional that does not decide on `LUST_IMPL`: its lines pass through.
    Other,
    /// A conditional decided on `LUST_IMPL` (undefined here): only the
    /// branch `active` names survives, and no directive lines remain.
    Impl { active: bool, taken: bool },
    /// A conditional nested inside a dropped branch: counts depth only.
    Dropped,
}

/// Whether the condition of a `#if`/`#ifdef`/`#ifndef`/`#elif` line is
/// decidable with `LUST_IMPL` undefined. `word` is the directive name,
/// `rest` what follows it. None when the condition does not mention
/// `LUST_IMPL`, or mentions it in a shape this does not evaluate: the
/// caller then leaves the group to the C preprocessor.
fn impl_cond(word: &str, rest: &str) -> Option<bool> {
    match word {
        "ifdef" | "ifndef" => {
            let name = rest.split_whitespace().next().unwrap_or("");
            (name == "LUST_IMPL").then_some(word == "ifndef")
        }
        "if" | "elif" => {
            if !rest.contains("LUST_IMPL") {
                return None;
            }
            let expr = rest.replace("defined(LUST_IMPL)", "0").replace("defined LUST_IMPL", "0");
            let compact: String = expr.chars().filter(|c| !c.is_whitespace()).collect();
            match compact.as_str() {
                "0" => Some(false),
                "!0" => Some(true),
                c if c.contains("0&&") || c.contains("&&0") => Some(false),
                c if c.contains("1||") || c.contains("||1") => Some(true),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Removes `#ifdef LUST_IMPL` groups (and the other decidable shapes,
/// see `impl_cond`) from runtime text, keeping any `#else` branch.
/// Declaration units never define `LUST_IMPL`, so tcc would skip these
/// groups line by line in every unit: about two thirds of the shared
/// header bytes (the runtime bodies and the Unicode tables). Cutting
/// them here, once, cuts every unit's C bytes and the work tcc does
/// to skip them. Groups this cannot decide pass through untouched.
fn strip_impl_blocks(src: &str) -> String {
    let mut out = String::with_capacity(src.len() / 2);
    let mut stack: Vec<ImplFrame> = Vec::new();
    let dropping = |stack: &[ImplFrame]| stack.iter().any(|f| matches!(f, ImplFrame::Dropped | ImplFrame::Impl { active: false, .. }));
    for line in src.split_inclusive('\n') {
        let trimmed = line.trim_start();
        if !trimmed.starts_with('#') {
            if !dropping(&stack) {
                out.push_str(line);
            }
            continue;
        }
        let after = trimmed[1..].trim_start();
        let word_end = after.find(|c: char| !c.is_ascii_alphabetic()).unwrap_or(after.len());
        let (word, rest) = (&after[..word_end], after[word_end..].trim());
        match word {
            "if" | "ifdef" | "ifndef" => {
                if dropping(&stack) {
                    stack.push(ImplFrame::Dropped);
                } else if let Some(v) = impl_cond(word, rest) {
                    stack.push(ImplFrame::Impl { active: v, taken: v });
                } else {
                    stack.push(ImplFrame::Other);
                    out.push_str(line);
                }
            }
            "elif" => {
                // Decide from a shared borrow first: the undecidable
                // case rewrites the frame itself.
                enum Act {
                    Decided(bool),
                    ToOther,
                    Off,
                    Emit,
                    Skip,
                }
                let act = match stack.last() {
                    Some(ImplFrame::Impl { taken, .. }) => match impl_cond(word, rest) {
                        Some(v) => Act::Decided(v),
                        // No earlier branch was kept, so this `elif` is
                        // an `if`: hand the rest of the group to the
                        // preprocessor as one.
                        None if !taken => Act::ToOther,
                        None => Act::Off,
                    },
                    Some(ImplFrame::Other) => Act::Emit,
                    _ => Act::Skip,
                };
                match act {
                    Act::Decided(v) => {
                        if let Some(ImplFrame::Impl { active, taken }) = stack.last_mut() {
                            *active = v && !*taken;
                            *taken |= *active;
                        }
                    }
                    Act::ToOther => {
                        *stack.last_mut().unwrap() = ImplFrame::Other;
                        out.push_str(&format!("#if {rest}\n"));
                    }
                    Act::Off => {
                        if let Some(ImplFrame::Impl { active, .. }) = stack.last_mut() {
                            *active = false;
                        }
                    }
                    Act::Emit => out.push_str(line),
                    Act::Skip => {}
                }
            }
            "else" => match stack.last_mut() {
                Some(ImplFrame::Impl { active, taken }) => {
                    *active = !*taken;
                    *taken = true;
                }
                Some(ImplFrame::Other) => out.push_str(line),
                _ => {}
            },
            "endif" => {
                if matches!(stack.pop(), Some(ImplFrame::Other)) {
                    out.push_str(line);
                }
            }
            _ => {
                if !dropping(&stack) {
                    out.push_str(line);
                }
            }
        }
    }
    out
}

/// The runtime without function bodies: `LUST_BODY(...)` regions are cut out once, so units do
/// not make tcc tokenize code that would expand to nothing.
/// The integer and size types units define in place of <stdint.h> and <stddef.h>
/// (`runtime_decls`), from the compiler's predefined types.
const INT_TYPEDEFS: &str = "typedef signed char int8_t; typedef unsigned char uint8_t; typedef short int16_t; typedef unsigned short uint16_t;\ntypedef int int32_t; typedef unsigned int uint32_t;\n#ifdef __INT64_TYPE__\ntypedef __INT64_TYPE__ int64_t; typedef unsigned __INT64_TYPE__ uint64_t;\n#else\ntypedef long long int64_t; typedef unsigned long long uint64_t;\n#endif\n#ifdef __SIZE_TYPE__\ntypedef __SIZE_TYPE__ size_t; typedef __PTRDIFF_TYPE__ ptrdiff_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __INTPTR_TYPE__ intptr_t;\n#else\ntypedef unsigned long size_t; typedef long ptrdiff_t; typedef unsigned long uintptr_t; typedef long intptr_t;\n#endif\n#define INT64_MIN (-9223372036854775807LL-1)\n#ifndef NULL\n#define NULL ((void*)0)\n#endif\n";

fn runtime_decls() -> &'static str {
    static DECLS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    DECLS.get_or_init(|| {
        let src = runtime_source(false);
        let mut out = String::with_capacity(src.len() / 2);
        let mut rest = src.as_str();
        // Skip the macro's own definition lines, which mention LUST_BODY without a body.
        while let Some(i) = rest.find("LUST_BODY(") {
            let line_start = rest[..i].rfind('\n').map_or(0, |n| n + 1);
            if rest[line_start..].starts_with("#define LUST_BODY") {
                let end = rest[i..].find('\n').map_or(rest.len(), |n| i + n);
                out.push_str(&rest[..end]);
                rest = &rest[end..];
                continue;
            }
            out.push_str(&rest[..i]);
            // Find the matching close paren of LUST_BODY( ... ).
            let mut depth = 0;
            let mut end = i;
            for (k, ch) in rest[i..].char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = i + k + 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            out.push(';');
            rest = &rest[end..];
        }
        out.push_str(rest);
        let out = strip_impl_blocks(&out);
        // Units do not include <stdint.h> or <stddef.h>: tcc spends about 1 ms per unit parsing
        // the system headers behind them. The compiler's predefined types define the same names
        // (tcc and gcc both predefine them; on macOS arm64 tcc's __INT64_TYPE__ is long long,
        // which matches Apple's int64_t). The runtime unit keeps the real includes.
        strip_c_comments(&out.replacen("#include <stdint.h>\n#include <stddef.h>\n", INT_TYPEDEFS, 1))
    })
}

/// The hash core text for splicing: hash.h, with hash.c inlined when
/// `with_bodies`. hash.h includes <stddef.h>/<stdint.h> for direct
/// inclusion by test harnesses; spliced copies drop both lines because
/// runtime.h already provided the types, and declaration units must
/// not re-read the system headers (see `runtime_decls`).
fn hash_source(with_bodies: bool) -> String {
    let hash = include_str!("runtime/hash.h").replacen("#include <stddef.h>\n#include <stdint.h>\n", "", 1);
    if with_bodies {
        hash.replacen("#include \"hash.c\"", include_str!("runtime/hash.c"), 1)
    } else {
        hash.replacen("#include \"hash.c\"", "", 1)
    }
}

/// Declarations for the erased hash core, for the header of a unit
/// whose generated code calls it (the std typed layer, when it lands).
/// Not part of the common unit header; see `runtime_source`.
#[allow(dead_code)]
pub fn hash_decls() -> String {
    hash_source(false)
}

/// The unit with the runtime's function definitions. It only changes when lust itself does.
pub fn runtime_unit() -> String {
    format!("#define LUST_IMPL 1\n{}", runtime_source(true))
}

/// The source files panic locations name: every file's path (index 0 is
/// the crate root) and each slot's file index.
pub struct SlotFiles<'a> {
    pub paths: &'a [&'a str],
    pub of_slot: &'a [u32],
}

/// The runtime setup `main_unit` emits for panics (`lust_unw_init`):
/// whether they unwind, the type ids of `&'static str` and `String`
/// (the message payloads' vtables carry them), and the slot of std's
/// hook runner when the program can install a hook (`set_hook`).
pub struct UnwindInit {
    pub unwind: bool,
    /// Unwind tables (`Program::unwind_tables`): runtime mode 2, and main runs under a catch point.
    pub tables: bool,
    pub ids: [u64; 4],
    pub hook_runner: Option<u32>,
}

/// The `main_unit` argument for `p` (`slot_of` maps a fn to its slot).
/// Always given: a `panic_any` payload's text reads the `&str` and
/// `String` type ids even under panic=abort with no hook installed.
pub fn unwind_init(p: &Program, slot_of: impl Fn(LocalDefId) -> u32) -> Option<UnwindInit> {
    let runner = p
        .fns
        .iter()
        .position(|f| {
            p.interner.get(f.name).ends_with("__lust_run_hook")
                && p.std_source_span(f.def(&p.ast).name_span)
                && p.display_path(f.name) == "std::panic::__lust_run_hook"
        })
        .map(|i| slot_of(LocalDefId(i as u32)));
    let (a, b) = crate::check::any::type_id_words(p, &p.tys, REF_STR);
    let (c, d) = crate::check::any::type_id_words(p, &p.tys, STRING);
    Some(UnwindInit { unwind: p.unwind, tables: p.unwind_tables, ids: [a, b, c, d], hook_runner: runner })
}

/// The location unit: the per-slot line and file tables and
/// `lust_loc_init`, which points the runtime at them. Its own unit
/// (see the driver) so a build whose slot lines and files did not
/// change does not re-emit or recompile the arrays: the main unit
/// rebuilds on every build, and the arrays are most of its bytes on
/// a large program. The symbol is not static, so an overlay copy in
/// the executable replaces the base copy, as glue does. It holds data
/// and `lust_loc_init` only, so it declares the four globals that sets
/// and the integer types, not the runtime (`unit_header`).
pub fn loc_unit(files: &SlotFiles, slot_lines: &[u32]) -> String {
    let mut c = format!(
        "{INT_TYPEDEFS}extern const char *lust_file;\nextern const uint32_t *lust_fn_line;\nextern const char *const *lust_files;\nextern const uint32_t *lust_slot_file;\n"
    );
    let lines: Vec<String> = slot_lines.iter().map(|l| l.to_string()).collect();
    let _ = writeln!(c, "static const uint32_t lines[{}] = {{{}}};", lines.len().max(1), lines.join(","));
    let file = files.paths.first().copied().unwrap_or("");
    // A crate of one file needs no per-slot table (`lust_slot_file` NULL).
    let multi = files.of_slot.iter().any(|&f| f != 0);
    if multi {
        let paths: Vec<String> = files.paths.iter().map(|p| c_string_lit(p.as_bytes())).collect();
        let _ = writeln!(c, "static const char *const files[{}] = {{{}}};", paths.len().max(1), paths.join(","));
        let of: Vec<String> = files.of_slot.iter().map(|f| f.to_string()).collect();
        let _ = writeln!(c, "static const uint32_t slot_file[{}] = {{{}}};", of.len().max(1), of.join(","));
    }
    let _ = writeln!(
        c,
        "void lust_loc_init(void) {{\n  lust_file = {};\n  lust_fn_line = lines;{}\n}}",
        c_string_lit(file.as_bytes()),
        if multi { "\n  lust_files = files;\n  lust_slot_file = slot_file;" } else { "\n  lust_files = 0;\n  lust_slot_file = 0;" }
    );
    c
}

/// Unit 0: globals, overlay registration, and `main`. Rebuilt on every
/// build; the per-slot location tables live in `loc_unit`, which is
/// rebuilt only when they change. With `init` (see `unwind_init`) it
/// sets up the runtime's panic payloads and hook runner; under
/// panic=unwind a `main` that ends by a panic exits 101.
pub fn main_unit(main_slot: u32, overlays: &[usize], init: Option<UnwindInit>) -> String {
    let unwind = init.as_ref().is_some_and(|i| i.unwind);
    let tables = init.as_ref().is_some_and(|i| i.unwind && i.tables);
    let runner_slot = init.as_ref().and_then(|i| i.hook_runner);
    let (init, runner) = match init {
        Some(UnwindInit { unwind, tables, ids: [a, b, c, d], hook_runner }) => (
            format!("\n  lust_unw_init({}, {a}ull, {b}ull, {c}ull, {d}ull);", if unwind && tables { 2 } else { unwind as u8 }),
            hook_runner.map_or(String::new(), |s| {
                // Release C names the runner directly (only its address is taken here).
                if names::release() { format!("\n  lust_hook_set_runner((lust_fnptr){});", names::body(s)) } else { format!("\n  lust_hook_set_runner(lust_fns[{s}]);") }
            }),
        ),
        None => (String::new(), String::new()),
    };
    let mut c = unit_header();
    c.push_str("void lust_loc_init(void);\nvoid lust_kstatics_init(void);\n");
    // Release C calls main's body (and passes the hook runner) by name.
    let main_call = if names::release() {
        let _ = writeln!(c, "void {}(void);", names::body(main_slot));
        if let Some(s) = runner_slot.filter(|&s| s != main_slot) {
            let _ = writeln!(c, "void {}(void);", names::body(s));
        }
        format!("{}()", names::body(main_slot))
    } else {
        format!("((void (*)(void))lust_fns[{main_slot}])()")
    };
    for u in overlays {
        let _ = writeln!(c, "void lust_overlay_u{u}(void);");
    }
    if tables {
        // Main runs under a catch point (std's lang_start catches its panic).
        let _ = writeln!(
            c,
            "static void lust_main_thunk(void *rc) {{ if (lust_main_entry_p) *(int *)rc = lust_main_entry_p(); else {main_call}; }}"
        );
    }
    let _ = writeln!(
        c,
        "int main(int argc, char **argv) {{\n  lust_argc = argc;\n  lust_argv = argv;\n  lust_loc_init();{}\n  lust_rt_init();\n  lust_base_init();\n  lust_kstatics_init();",
        init
    );
    for u in overlays {
        let _ = writeln!(c, "  lust_overlay_u{u}();");
    }
    c.push_str(runner.trim_start_matches('\n'));
    if !runner.is_empty() {
        c.push('\n');
    }
    if tables {
        c.push_str("  int rc = 0;\n  if (lust_unw_try(lust_main_thunk, &rc)) rc = lust_unw_main_caught();\n  lust_tls_exit();\n  lust_flush();\n  return rc;\n}\n");
        return c;
    }
    let _ = writeln!(
        c,
        "  if (lust_main_entry_p) {{ int rc = lust_main_entry_p(); {} lust_tls_exit(); lust_flush(); return rc; }}\n  {main_call};\n  {}lust_tls_exit();\n  lust_flush();\n  return {};\n}}",
        if unwind { "if (lust_unw_main_exit()) rc = 101;" } else { "" },
        if unwind { "int rc = lust_unw_main_exit();\n  " } else { "" },
        if unwind { "rc" } else { "0" }
    );
    c
}

/// The function table (with room for `capacity` slots), and `lust_base_init`, which registers
/// every base function unit.
pub fn table_unit(capacity: usize, fn_units: &[usize]) -> String {
    let mut c = unit_header();
    let _ = writeln!(c, "lust_fnptr lust_fns[{}];", capacity.max(1));
    let _ = writeln!(c, "lust_fnptr lust_tramps[{}];", capacity.max(1));
    let _ = writeln!(c, "int (*lust_main_entry_p)(void);");
    for u in fn_units {
        let _ = writeln!(c, "void lust_register_u{u}(void);");
    }
    c.push_str("void lust_base_init(void) {\n");
    for u in fn_units {
        let _ = writeln!(c, "  lust_register_u{u}();");
    }
    c.push_str("}\n");
    c
}

/// The shared glue unit. With a frozen shared set it holds only those keys; the rest of the
/// glue is static in the function units (see `GlueSet`).
pub fn glue_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    if p.unwind_tables {
        c.push_str(noreturn_decls());
    }
    let mut types = HashSet::new();
    for (_, st) in p.statics.iter().enumerate().filter(|&(i, _)| p.static_live(i)) {
        let t = cty(&p.tys, st.ty);
        collect_types(&t, &mut types);
        collect_promoted(p, &st.value, &t, &mut types);
    }
    if let Some(shared) = &g.shared {
        // A stale key (no live body reaches it) may name an Adt or fields that are gone.
        let mut keys: Vec<&(Glue, CTy)> = shared.iter().filter(|k| !g.stale.contains(*k)).collect();
        for k in &keys {
            g.def_types(k, &mut types);
        }
        type_decls(p, &mut c, &types);
        keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
        for k in &keys {
            c.push_str(&g.protos[*k]);
        }
        for k in &keys {
            c.push_str(&g.def_map[*k]);
        }
        c.push_str(&static_defs(p, &g.slots));
        return c;
    }
    for k in g.protos.keys() {
        g.def_types(k, &mut types);
    }
    type_decls(p, &mut c, &types);
    let mut protos: Vec<&String> = g.protos.values().collect();
    protos.sort();
    for proto in protos {
        c.push_str(proto);
    }
    if g.defs_stale {
        g.def_map.values().for_each(|d| c.push_str(d));
    } else {
        c.push_str(&g.defs);
    }
    c.push_str(&static_defs(p, &g.slots));
    c
}

/// `text` with each identifier token that `map` names replaced, outside comments and string
/// and character literals: an in-place parameter's local `l{i}` becomes `(*p{i})` in its body
/// (`FnGen::function`). Whole identifiers only, so `l1` leaves `l10` alone.
fn rename_idents(text: &str, map: &[(String, String)]) -> String {
    let b = text.as_bytes();
    let ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut out = String::with_capacity(text.len() + 64);
    let mut i = 0;
    while i < b.len() {
        let start = i;
        match b[i] {
            b'"' | b'\'' => {
                let q = b[i];
                i += 1;
                while i < b.len() && b[i] != q {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
                i = (i + 1).min(b.len());
                out.push_str(&text[start..i]);
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                i = text[i + 2..].find("*/").map_or(b.len(), |k| i + 2 + k + 2);
                out.push_str(&text[start..i]);
            }
            b'/' if b.get(i + 1) == Some(&b'/') => {
                i = text[i..].find('\n').map_or(b.len(), |k| i + k);
                out.push_str(&text[start..i]);
            }
            c if ident(c) => {
                while i < b.len() && ident(b[i]) {
                    i += 1;
                }
                let w = &text[start..i];
                out.push_str(map.iter().find(|(f, _)| f == w).map_or(w, |(_, t)| t.as_str()));
            }
            _ => {
                let ch = text[i..].chars().next().unwrap_or(' ');
                i += ch.len_utf8().max(1);
                out.push_str(&text[start..i.min(b.len())]);
            }
        }
    }
    out
}

/// One enum or Option value as a compound literal from its field value
/// texts, in field order. Shared by function codegen (`make_variant`)
/// and constant initializers (`const_init`), whose file-scope globals
/// need the same single-designator forms.
fn variant_lit(p: &Program, t: &CTy, variant: usize, vals: &[String]) -> String {
    let ct = ctype(t);
    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
    match c_layout(p, t) {
        None => match t {
            CTy::Option(_) => {
                if vals.is_empty() {
                    format!("(({ct}){{ .tag = 0 }})")
                } else {
                    format!("(({ct}){{ .tag = 1, .v = {} }})", vals[0])
                }
            }
            _ => {
                if fields.is_empty() {
                    format!("(({ct}){{ .tag = {variant} }})")
                } else {
                    format!("(({ct}){{ .tag = {variant}, .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                }
            }
        },
        Some(l) => match l.enum_tag {
            Some(EnumTag::Explicit { size, signed }) => {
                let mut init = format!("._tag = {}", disc_lit(adt_discs(p, t)[variant], size, signed));
                if !fields.is_empty() {
                    init.push_str(", ");
                    init.push_str(&fields.join(", "));
                }
                format!("(({ct}){{ .u = {{ .v{variant} = {{ {init} }} }} }})")
            }
            Some(EnumTag::NicheFilled { variant: niche_variant, niche, first, start, .. }) if variant != niche_variant => {
                // The variant struct carries the niche scalar as its
                // own `_s` member, so one literal sets tag and fields.
                let mut init = format!("._s = {}", scalar_lit(niche_tag_value(niche, first, start, variant), niche.scalar_size, false));
                if !fields.is_empty() {
                    init.push_str(", ");
                    init.push_str(&fields.join(", "));
                }
                format!("(({ct}){{ .u = {{ .v{variant} = {{ {init} }} }} }})")
            }
            _ => {
                if fields.is_empty() {
                    zero_lit(p, t)
                } else {
                    format!("(({ct}){{ .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                }
            }
        },
    }
}

/// The C initializer for one const value at the given C type. Referenced
/// aggregates are promoted to file-scope constants first, written to `pre`.
fn const_init(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, pre: &mut String, cx: &mut kconst::StaticCx, slots: &[u32], pos: Option<&str>) -> String {
    if let (CV::Float(bits, f), CTy::Float(_)) = (v, t) {
        return match f {
            FloatTy::F64 => format!("(((union {{ uint64_t b; double d; }}){{ .b = {}ull }}).d)", bits),
            FloatTy::F32 => format!("(((union {{ uint32_t b; float f; }}){{ .b = {}u }}).f)", *bits as u32),
        };
    }
    use crate::ty::consteval::ConstValue as CV;
    match (v, t) {
        (CV::Int(i), CTy::Int(it)) => {
            if is128(*it) {
                format!("(({}){{{}ULL, {}ULL}})", int_c(*it), *i as u128 as u64, (*i as u128 >> 64) as u64)
            } else if *i < 0 {
                format!("(({})((int64_t){i}))", int_c(*it))
            } else {
                format!("(({})((uint64_t){}ull))", int_c(*it), *i as u128)
            }
        }
        (CV::Bool(b), _) => (*b as u8).to_string(),
        // A Cell's constant is its value's (its C form is the value's).
        (_, CTy::Cell(inner)) => const_init(p, v, inner, pre, cx, slots, pos),
        // An atomic's constant is its value (cgen/sync.rs).
        // `Vec::new()` and `String::new()`: an empty buffer, its pointer
        // dangling at the element's alignment (W-THREADS).
        // `HashMap::with_hasher(s)` / `HashSet::with_hasher(s)`: an
        // empty table around the hasher.
        (CV::Aggregate(vals), CTy::Hash(k, _)) if hash::is_table(*k) && vals.len() == 1 => {
            let s = const_init(p, &vals[0], &hash::builder_cty(t), pre, cx, slots, None);
            hash::const_empty_table(t, &s, pre)
        }
        (CV::Aggregate(vals), CTy::Vec(e)) if vals.is_empty() => format!("{{(void*)(uintptr_t){}, 0, 0}}", c_size_align(p, e).1.max(1)),
        (CV::Aggregate(vals), CTy::String) if vals.is_empty() => "{(uint8_t*)(uintptr_t)1, 0, 0}".into(),
        // A const lock: unlocked and unpoisoned around its value.
        (CV::Aggregate(vals), CTy::Sync(k, e)) if k.is_cell_struct() && vals.len() == 1 => {
            let words = vec!["0"; sync::cell_words(*k).len()].join(", ");
            format!("{{{words}, {}}}", const_init(p, &vals[0], e, pre, cx, slots, None))
        }
        // An empty `OnceLock`, a `Condvar`, a `Barrier::new(n)` (W-THREADS).
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::OnceLock, _)) if vals.is_empty() => "{0}".into(),
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::Condvar, _)) if vals.is_empty() => "0".into(),
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::Barrier, _)) if vals.len() == 1 => {
            format!("{{0, 0, 0, 0, {}}}", const_init(p, &vals[0], &CTy::Int(IntTy::Usize), pre, cx, slots, None))
        }
        (CV::Int(i), CTy::Sync(k, _)) if let Some(crate::ty::sync::AtomicVal::Int(it)) = k.atomic_value() => const_init(p, &CV::Int(*i), &CTy::Int(it), pre, cx, slots, None),
        (CV::Char(c), _) => format!("((uint32_t){})", *c as u32),
        (CV::Unit, _) => "((lust_Unit){})".into(),
        (CV::Str(i), _) => kconst::kstatic_str(cx, pre, p.ast.strings[*i as usize].as_bytes()),
        (CV::StrBytes(b), _) => kconst::kstatic_str(cx, pre, b.as_slice()),
        (CV::StaticRef(idx), CTy::Slice(_)) => {
            let st = &p.statics[*idx as usize];
            let sct = cty(&p.tys, st.ty);
            match sct {
                CTy::Array(_, n) => format!("(({}){{ {}.v, {n} }})", ctype(t), static_sym(p, *idx)),
                _ => zero_lit(p, t),
            }
        }
        (CV::StaticRef(idx), _) => format!("(&{})", static_sym(p, *idx)),
        (CV::StaticPlace(idx, path), _) => match static_place_c(p, *idx, path) {
            Some((e, CTy::Array(_, n))) if matches!(t, CTy::Slice(_)) => format!("(({}){{ {e}.v, {n} }})", ctype(t)),
            Some((e, _)) => format!("(&{e})"),
            // A place cgen cannot name: a promoted copy of its value.
            None => match crate::ty::consteval::value_at(&p.statics[*idx as usize].value, path) {
                Some(x) => const_init(p, &CV::Ref(Box::new(x.clone())), t, pre, cx, slots, None),
                None => panic!("internal: a static place {path:?} outside its static's value"),
            },
        },
        (CV::FnPtr(f), CTy::FnPtr(..)) => {
            // Runtime fn pointer values are `lust_tramps[slot]`, not a
            // constant; this unit gets its own copy of the slot's
            // trampoline (forwarding through `lust_fns`), whose address is.
            let f = LocalDefId(*f);
            let slot = *slots.get(f.0 as usize).expect("internal: a fn pointer in static data has no fn slot");
            let name = format!("stramp{}", names::fn_tag(slot));
            // Once per prelude (`cx` and `pre` live and die together): a scan of `pre`
            // here was quadratic in a 10 MB statics prelude (tsgo).
            if cx.stramps.insert(name.clone()) {
                let tr = trampoline(p, f, slot).replacen(&format!(" {}(", names::tramp(slot)), &format!(" {name}("), 1);
                if names::release() {
                    // Release C: the copy calls the body by name, so it needs the
                    // body's prototype, and it stays local to this unit (statics in parts:
                    // global, so another part points at the same copy).
                    let _ = writeln!(pre, "{};", fn_sig(p, f, slot));
                    if cx.parts {
                        let proto = tr.split_once(" {").map_or(tr.as_str(), |(h, _)| h);
                        cx.decls.push((name.clone(), format!("{proto};\n"), None));
                    } else {
                        pre.push_str("static ");
                    }
                }
                pre.push_str(&tr);
            }
            format!("(({})&{name})", ctype(t))
        }
        (CV::Ref(inner), CTy::Slice(el)) => {
            // A slice over a promoted aggregate or blob; over a zero-sized
            // one (`&[]`, `&[(); 3]`), rustc's pointer is the alignment.
            let n = match &**inner {
                CV::Aggregate(vals) => vals.len() as u64,
                CV::Bytes(b) => b.len() as u64,
                _ => 1,
            };
            if c_size_align(p, &CTy::Array(el.clone(), n)).0 == 0 && matches!(&**inner, CV::Aggregate(_) | CV::Bytes(_)) {
                return format!("(({}){{ ({} *)(uintptr_t){}, {n} }})", ctype(t), ctype(el), c_size_align(p, el).1.max(1));
            }
            match &**inner {
                CV::Aggregate(vals) => {
                    let at = CTy::Array(el.clone(), vals.len() as u64);
                    let name = promoted_name(cx, pos);
                    let init = const_init(p, inner, &at, pre, cx, slots, pos.map(|_| name.as_str()));
                    let name = content_named(p, cx, pos, name, inner, &at, &init);
                    kconst::kdef(p, cx, pre, &name, inner, &at, &init);
                    format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
                }
                CV::Bytes(b) => {
                    let at = CTy::Array(el.clone(), b.len() as u64);
                    let init = const_init(p, inner, &at, pre, cx, slots, None);
                    let name = promoted_name(cx, pos);
                    let name = content_named(p, cx, pos, name, inner, &at, &init);
                    kconst::kdef(p, cx, pre, &name, inner, &at, &init);
                    format!("(({}){{ {name}.v, {} }})", ctype(t), b.len())
                }
                _ => zero_lit(p, t),
            }
        }
        // A zero-sized pointee has no storage in rustc: its address is
        // its alignment (`const U: &() = &();` is 0x1).
        (CV::Ref(_), CTy::Ref(inner_ct)) if c_size_align(p, inner_ct).0 == 0 => {
            format!("(({} *)(uintptr_t){})", ctype(inner_ct), c_size_align(p, inner_ct).1.max(1))
        }
        (CV::Ref(inner), CTy::Ref(inner_ct)) => {
            let name = promoted_name(cx, pos);
            let init = const_init(p, inner, inner_ct, pre, cx, slots, pos.map(|_| name.as_str()));
            let name = content_named(p, cx, pos, name, inner, inner_ct, &init);
            kconst::kdef(p, cx, pre, &name, inner, inner_ct, &init);
            format!("(&{name})")
        }
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> =
                    vals.iter().enumerate().map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &es[i], pre, cx, slots, sub(pos, i).as_deref()))).collect();
                format!("(({}){{ {} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> = vals.iter().enumerate().map(|(i, x)| const_init(p, x, e, pre, cx, slots, sub(pos, i).as_deref())).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Repeat(x, n), CTy::Array(e, _)) => {
            if *n == 0 {
                zero_lit(p, t)
            } else {
                // Every element is the one value: a promoted reference in it is one
                // allocation, named by element 0.
                let one = const_init(p, x, e, pre, cx, slots, sub(pos, 0).as_deref());
                let parts: Vec<String> = (0..*n).map(|_| one.clone()).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &cty(&p.tys, adt.variants[0].fields[i].ty), pre, cx, slots, sub(pos, i).as_deref())))
                    .collect();
                format!("(({}){{ {} }})", names::adt(*a), parts.join(", "))
            }
        }
        (CV::Variant(variant, vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            let inits: Vec<String> = vals
                .iter()
                .enumerate()
                .map(|(i, x)| const_init(p, x, &cty(&p.tys, adt.variants[*variant as usize].fields[i].ty), pre, cx, slots, None))
                .collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Variant(variant, vals), CTy::Option(e)) => {
            let inits: Vec<String> = vals.iter().map(|x| const_init(p, x, e, pre, cx, slots, None)).collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Variant(variant, vals), CTy::Result(a, b)) => {
            let e = if *variant == 0 { a } else { b };
            let inits: Vec<String> = vals.iter().map(|x| const_init(p, x, e, pre, cx, slots, None)).collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Aggregate(vals), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), vals.len() as u64);
            let name = promoted_name(cx, pos);
            let init = const_init(p, v, &at, pre, cx, slots, pos.map(|_| name.as_str()));
            let name = content_named(p, cx, pos, name, v, &at, &init);
            kconst::kdef(p, cx, pre, &name, v, &at, &init);
            format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
        }
        // One C array for the whole blob, at an array type; at a
        // slice type it is the promoted backing array, as an
        // aggregate slice backing is above.
        (CV::Bytes(b), CTy::Array(..)) => bytes_array_lit(p, t, b.as_slice()),
        (CV::Bytes(b), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), b.len() as u64);
            let init = const_init(p, v, &at, pre, cx, slots, None);
            let name = promoted_name(cx, pos);
            let name = content_named(p, cx, pos, name, v, &at, &init);
            kconst::kdef(p, cx, pre, &name, v, &at, &init);
            format!("(({}){{ {name}.v, {} }})", ctype(t), b.len())
        }
        _ => zero_lit(p, t),
    }
}

/// The C name of a promoted value in static data. Inside a static's
/// value (`pos` is the position's name, see `static_pos`) it is named by
/// its path, so a `StaticPlace` in another static can name it
/// (`static_place_c`); elsewhere it gets a cx name.
fn promoted_name(cx: &mut kconst::StaticCx, pos: Option<&str>) -> String {
    match pos {
        Some(at) => format!("{at}_d"),
        None => {
            cx.counter += 1;
            format!("lust_promoted_{}", cx.counter)
        }
    }
}

/// `name` from `promoted_name` once the value's initializer is made: an unnamed pointee of release
/// C statics in parts gets its content's name instead (`kconst::content_name`).
fn content_named(p: &Program, cx: &kconst::StaticCx, pos: Option<&str>, name: String, v: &crate::ty::consteval::ConstValue, ct: &CTy, init: &str) -> String {
    if pos.is_none() && cx.parts { kconst::content_name(p, cx, v, ct, init) } else { name }
}

/// The position name of field or element `i` below position `pos`.
fn sub(pos: Option<&str>, i: usize) -> Option<String> {
    pos.map(|at| format!("{at}_{i}"))
}

/// The position name of static `idx`'s root value: the prefix of the
/// names of the promoted values inside it (`promoted_name`).
fn static_pos(p: &Program, idx: u32) -> String {
    format!("lust_sp{}", &static_sym(p, idx)["lust_static".len()..])
}

/// The C place of a `ConstValue::StaticPlace` and its C type: field and
/// element projections of the static's symbol, and a `Deref` step to the
/// promoted value the static holds there, by its path name. None for a
/// step this shape does not have.
fn static_place_c(p: &Program, idx: u32, path: &[crate::ty::consteval::StaticStep]) -> Option<(String, CTy)> {
    use crate::ty::consteval::{ConstValue as CV, StaticStep, value_at};
    let st = p.statics.get(idx as usize)?;
    // `v` follows the value along (None past a byte blob's element).
    let (mut e, mut pos, mut ct, mut v) = (static_sym(p, idx), static_pos(p, idx), cty(&p.tys, st.ty), Some(&st.value));
    for step in path {
        // A repeat's elements share element 0's promoted values.
        let at = match (step, v) {
            (StaticStep::Field(_) | StaticStep::Elem(_), Some(CV::Repeat(..))) => format!("{pos}_0"),
            (StaticStep::Field(i) | StaticStep::Elem(i), _) => format!("{pos}_{i}"),
            (StaticStep::Deref, _) => format!("{pos}_d"),
        };
        (e, ct) = match (step, ct) {
            (StaticStep::Field(i), CTy::Adt(a)) => (format!("{e}.f{i}"), cty(&p.tys, p.adt(a).variants.first()?.fields.get(*i as usize)?.ty)),
            (StaticStep::Field(i), CTy::Tuple(es)) => (format!("{e}.f{i}"), es.get(*i as usize)?.clone()),
            (StaticStep::Elem(i), CTy::Array(el, _)) => (format!("{e}.v[{i}]"), *el),
            (StaticStep::Deref, CTy::Ref(inner)) => (at.clone(), *inner),
            (StaticStep::Deref, CTy::Slice(el)) => {
                let n = match v? {
                    CV::Ref(inner) => match &**inner {
                        CV::Aggregate(vals) => vals.len() as u64,
                        CV::Bytes(b) => b.len() as u64,
                        _ => return None,
                    },
                    CV::Aggregate(vals) => vals.len() as u64,
                    CV::Bytes(b) => b.len() as u64,
                    _ => return None,
                };
                (at.clone(), CTy::Array(el, n))
            }
            _ => return None,
        };
        pos = at;
        v = v.and_then(|v| value_at(v, std::slice::from_ref(step)));
    }
    Some((e, ct))
}

/// The C symbol of one static. Named by the static's stable def hash,
/// never by its collect-order index: cached function code (a daemon
/// slot's `FnOut`, a disk unit object) names statics by symbol, and an
/// edit that inserts a static earlier in the file shifts every later
/// index. A position-based name would then read the wrong static
/// while every fingerprint still matches (the same reason fn slots
/// key on def identity, section 4.2).
fn static_sym(p: &Program, idx: u32) -> String {
    match p.static_defs.get(idx as usize) {
        Some(def) => format!("lust_static_{}", def.hash.0),
        None => format!("lust_static_{idx}"),
    }
}

/// The array types `const_init` synthesizes for slice values inside a
/// const value (a promoted backing array exists in no written type, so
/// collecting only the static types themselves misses it).
fn collect_promoted(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, out: &mut HashSet<CTy>) {
    use crate::ty::consteval::ConstValue as CV;
    match (v, t) {
        (CV::Ref(inner), CTy::Slice(el)) => {
            match &**inner {
                CV::Aggregate(vals) => {
                    let at = CTy::Array(el.clone(), vals.len() as u64);
                    collect_types(&at, out);
                    collect_promoted(p, inner, &at, out);
                }
                CV::Bytes(b) => {
                    let at = CTy::Array(el.clone(), b.len() as u64);
                    collect_types(&at, out);
                }
                _ => {}
            }
        }
        (CV::Aggregate(vals), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), vals.len() as u64);
            collect_types(&at, out);
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Bytes(b), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), b.len() as u64);
            collect_types(&at, out);
        }
        // A promoted value has its own definition: its type is defined too.
        (CV::Ref(inner), CTy::Ref(inner_ct)) => {
            collect_types(inner_ct, out);
            collect_promoted(p, inner, inner_ct, out)
        }
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            for (x, e) in vals.iter().zip(es) {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Repeat(x, _), CTy::Array(e, _)) => collect_promoted(p, x, e, out),
        (CV::Aggregate(vals), CTy::Adt(a)) => {
            for (i, x) in vals.iter().enumerate() {
                collect_promoted(p, x, &cty(&p.tys, p.adt(*a).variants[0].fields[i].ty), out);
            }
        }
        (CV::Variant(variant, vals), CTy::Adt(a)) => {
            for (i, x) in vals.iter().enumerate() {
                collect_promoted(p, x, &cty(&p.tys, p.adt(*a).variants[*variant as usize].fields[i].ty), out);
            }
        }
        (CV::Variant(_, vals), CTy::Option(e)) => {
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        _ => {}
    }
}

/// Static indices in emission order: by index, or in release C by symbol (a
/// persistent session's static indices carry its history, and its units are a
/// one-shot build's, byte for byte).
fn order_statics(p: &Program, mut v: Vec<usize>) -> Vec<usize> {
    if names::release() {
        v.sort_by_cached_key(|&i| (static_sym(p, i as u32), i));
    } else {
        v.sort_unstable();
    }
    v
}

/// The live statics in emission order (`order_statics`).
fn statics_in_order(p: &Program) -> Vec<usize> {
    order_statics(p, (0..p.statics.len()).filter(|&i| p.static_live(i)).collect())
}

/// Definitions of the program's statics as C globals (ARCH 2.13 static data).
/// The extern declarations come first: statics emit in stable def order,
/// so one static's initializer can name a later static (`static S: &[u8] = &A;`
/// before `A` in hash order), and C needs the name declared before use.
fn static_defs(p: &Program, slots: &[u32]) -> String {
    let mut pre = static_decls(p);
    let mut out = String::new();
    let mut cx = kconst::StaticCx::default();
    // Release C numbers the `thread_local!` keys' slot words 1, 2, .. by symbol:
    // collect numbers them in static order, which a persistent session keeps in
    // history order. Only this unit holds the words (bodies pass a key's address).
    let order = statics_in_order(p);
    let tls_word: HashMap<usize, crate::ty::consteval::ConstValue> = if names::release() {
        order.iter().filter(|&&i| p.statics[i].tls.is_some()).enumerate().map(|(n, &i)| (i, crate::ty::consteval::ConstValue::Int(n as i128 + 1))).collect()
    } else {
        HashMap::new()
    };
    for i in order {
        let st = &p.statics[i];
        if let Some(cell) = native_tls_cell(p, i) {
            out.push_str(&native_tls_def(p, i, &cell));
            continue;
        }
        let ct = cty(&p.tys, st.ty);
        let value = tls_word.get(&i).unwrap_or(&st.value);
        let init = const_init(p, value, &ct, &mut pre, &mut cx, slots, Some(&static_pos(p, i as u32)));
        let _ = writeln!(out, "{} {} = {init};", ctype(&ct), static_sym(p, i as u32));
    }
    // Tentative definitions of the path-named promoted values first: one
    // static's data can point into another's (`static_place_c`), in any order.
    // So do the macros that name a pointee by an equal one (`kconst::kdef`).
    let mut fwd = String::new();
    for line in pre.lines() {
        if line.starts_with("#define lust_sp_") {
            let _ = writeln!(fwd, "{line}");
        } else if let Some(rest) = line.strip_prefix("static const ")
            && let Some((decl, _)) = rest.split_once(" = ")
            && decl.contains(" lust_sp_")
        {
            let _ = writeln!(fwd, "static const {decl};");
        }
    }
    let pre: String = pre.lines().filter(|l| !l.starts_with("#define lust_sp_")).flat_map(|l| [l, "\n"]).collect();
    format!("{fwd}{pre}{out}{}", kconst::kstatics_init(&cx))
}

/// One static of release C statics in parts (`statics_outs`).
pub(crate) struct StaticOut {
    /// Its index in `Program::statics`.
    pub idx: usize,
    pub sym: String,
    /// Its definition, `T sym = init;`.
    pub data: String,
    /// What its value defined first, in `static_defs`' order: pointees, alias macros, str arrays,
    /// and trampolines with their bodies' prototypes.
    pub made: String,
    /// The names `made` defines, as indices into `StaticCx::decls`.
    pub decls: std::ops::Range<usize>,
}

/// `static_defs`' pass for release C statics in parts (`names::statics_parts`): every live
/// static in emission order with what its value defined first, and the pass's context (the
/// pointees to register and each defined name's declaration). The pass defines its pointees,
/// str arrays and trampolines global and names an unnamed pointee by its content
/// (`StaticCx::parts`).
fn statics_outs(p: &Program, slots: &[u32]) -> (Vec<StaticOut>, kconst::StaticCx) {
    let mut cx = kconst::StaticCx::default();
    cx.parts = true;
    let order = statics_in_order(p);
    // The `thread_local!` keys' slot words, numbered over every static as `static_defs` does.
    let tls_word: HashMap<usize, crate::ty::consteval::ConstValue> =
        order.iter().filter(|&&i| p.statics[i].tls.is_some()).enumerate().map(|(n, &i)| (i, crate::ty::consteval::ConstValue::Int(n as i128 + 1))).collect();
    let mut outs = Vec::with_capacity(order.len());
    for i in order {
        let st = &p.statics[i];
        if let Some(cell) = native_tls_cell(p, i) {
            let first = cx.decls.len();
            let sym = static_sym(p, i as u32);
            outs.push(StaticOut { idx: i, data: native_tls_def(p, i, &cell), sym, made: String::new(), decls: first..first });
            continue;
        }
        let ct = cty(&p.tys, st.ty);
        let value = tls_word.get(&i).unwrap_or(&st.value);
        let (mut made, first) = (String::new(), cx.decls.len());
        let init = const_init(p, value, &ct, &mut made, &mut cx, slots, Some(&static_pos(p, i as u32)));
        let sym = static_sym(p, i as u32);
        outs.push(StaticOut { idx: i, data: format!("{} {sym} = {init};\n", ctype(&ct)), sym, made, decls: first..cx.decls.len() });
    }
    (outs, cx)
}

/// Extern declarations of the statics, for function units.
fn static_decls(p: &Program) -> String {
    static_decls_for(p, &HashSet::from_iter(0..p.statics.len()))
}

/// Extern declarations of the statics at `keep` indices, for function units.
fn static_decls_for(p: &Program, keep: &HashSet<usize>) -> String {
    let mut out = String::new();
    // Only the kept statics are ordered: a unit keeps few of the program's.
    for i in order_statics(p, keep.iter().copied().filter(|&i| i < p.statics.len() && p.static_live(i)).collect()) {
        let _ = writeln!(out, "extern {} {};", ctype(&cty(&p.tys, p.statics[i].ty)), static_sym(p, i as u32));
    }
    out
}

/// The indices of the statics whose C symbol any of `texts` names.
/// Generated C names a static only by its symbol, so a text scan is
/// exact: a symbol inside a string literal only keeps one extra
/// declaration. Function units declare (and declare the types of)
/// only the statics they use, instead of every static in the program
/// in every unit.
fn used_statics<'a>(p: &Program, texts: impl Iterator<Item = &'a str>) -> HashSet<usize> {
    let mut syms: HashSet<&'a str> = HashSet::new();
    let rec = record::on();
    for text in texts {
        let mut rest = text;
        while let Some(i) = rest.find("lust_static_") {
            rest = &rest[i..];
            let end = rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
            if rec && !syms.contains(&rest[..end]) {
                record::read(record::Read::Static(rest[..end].to_string()));
            }
            syms.insert(&rest[..end]);
            rest = &rest[end..];
            if rest.is_empty() {
                break;
            }
        }
    }
    (0..p.statics.len()).filter(|&i| p.static_live(i) && syms.contains(static_sym(p, i as u32).as_str())).collect()
}

/// Release C inline definitions (`inline_callees`): the largest plain fn definition (its
/// text alone, not its comment or trampoline) or glue a unit copies, in bytes, and how
/// many call levels it follows from its own fns. Measured on tsgo: depth gains more than
/// size; 1500 bytes and 3 levels cost +36% cold compile for about -27% run time without
/// LTO.
const INLINE_BYTES: usize = 1500;
const INLINE_DEPTH: usize = 3;
/// Past `INLINE_DEPTH`, levels to `INLINE_DEPTH_TINY` copy only tiny fns (an accessor
/// behind an accessor) and `#[inline]` ones.
const INLINE_DEPTH_TINY: usize = 6;
const INLINE_TINY_BYTES: usize = 400;
/// The largest hot callee a copies profile copies (`inline_pick_hot`) when it has no
/// `#[inline]`: on tsgo, 6000 bytes ran no faster and cost 6% more warm build time.
const HOT_COPY_BYTES: usize = 3000;
/// Copy levels with a copies profile: Rust's layers (iterator, closure, hasher, accessor)
/// put hot accessors 7 and more calls below a hot fn.
const HOT_COPY_DEPTH: usize = 12;
/// A fn with an unwind cleanup frame gets hot copies only when the copies profile ran it this
/// many times or more (`CopyHot::frames`). Each frame copy is new code in its caller units: on
/// tsgo, copies of all 1,821 small hot frame fns doubled warm clang time; 372 ran this often.
pub const FRAME_COPY_MIN: u64 = 100_000;
/// The most copies the frame rule (`hot_pick`) adds to one unit, the nearest its own fns
/// first (`FrameWalk`). On tsgo the biggest units took 30 to 60 new copies (frame fns and the
/// callees below them), and some of them compiled 2x slower.
const NEW_COPIES_PER_UNIT: usize = 10;
/// ADTs of this many bytes or more are the big context structs (`CopyHot::big`). A copy only
/// the frame rule adds never reads one (`hot_pick`): an edit of one changes the copies of
/// accessors of it in every unit that holds them (the layout is in their text).
const BIG_LAYOUT_BYTES: u64 = 512;

/// Release C copies from a copies profile (`LUST_PGO_COPIES`, `inline_callees`): the ids of
/// the fns it ran often (`hot`) and of those it ran `FRAME_COPY_MIN` times or more (`frames`),
/// and the C names of the program's ADTs of `BIG_LAYOUT_BYTES` or more (`big`, `big_adts`).
pub struct CopyHot {
    pub hot: HashSet<u64>,
    pub frames: HashSet<u64>,
    pub big: BTreeSet<String>,
}

/// The C names of `p`'s ADTs of `BIG_LAYOUT_BYTES` or more (`CopyHot::big`), on the pool. Call
/// within the release names and a layout phase (each worker takes both).
pub fn big_adts(p: &Program) -> BTreeSet<String> {
    let (cur, tag) = (names::current(), LAYOUT_PHASE.with(std::cell::Cell::get));
    let ids: Vec<u32> = (0..p.adts.len() as u32).collect();
    crate::pool::par_map(&ids, |&a| {
        let a = AdtId(a);
        // A def with no variant (an uninhabited placeholder) has no layout.
        in_layout_phase(tag, || names::with(cur.as_ref(), || (!p.adt(a).variants.is_empty() && c_layout(p, &CTy::Adt(a)).is_some_and(|l| l.size >= BIG_LAYOUT_BYTES)).then(|| names::adt(a))))
    })
    .into_iter()
    .flatten()
    .collect()
}

/// The ADTs whose layout a fn definition's C text bakes in (`FnOut::layout_reads`), by C name:
/// the containers of its byte-offset field reads (a local's or parameter's declared pointer
/// type, or the `T**` cast of a nested offset read) and the ADTs inside the types of its
/// by-value locals and parameters. `code` starts with the definition's head.
fn scan_layout_deps(code: &str) -> BTreeSet<String> {
    fn adts(t: &str, out: &mut BTreeSet<String>) {
        let b = t.as_bytes();
        let mut i = 0;
        while i + 18 <= b.len() {
            if b[i] == b'A' && matches!(b[i + 1], b'd' | b'i' | b'n') && (i == 0 || !(b[i - 1].is_ascii_alphanumeric())) && b[i + 2..i + 18].iter().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()) {
                out.insert(t[i..i + 18].to_string());
                i += 18;
            } else {
                i += 1;
            }
        }
    }
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    // Each local's or parameter's declared type and whether it is a pointer: `T *l3`, `T l4`,
    // `T* p2` (a declaration line lists one type then its declarators).
    let mut ptr_of: HashMap<&str, &str> = HashMap::new();
    let mut out = BTreeSet::new();
    for (n, line) in code.lines().enumerate() {
        let t = line.trim_start();
        if n == 0 {
            // The head: `R f_<id>(T* p1, U p2) {`.
            if let Some(args) = t.split_once('(').map(|x| x.1) {
                for a in args.split(',') {
                    let a = a.trim().trim_end_matches(|c: char| c == ')' || c == '{' || c == ' ');
                    if let Some((ty, var)) = a.rsplit_once(|c: char| c == ' ' || c == '*') {
                        let var = var.trim();
                        if var.starts_with('p') && var[1..].chars().all(|c| c.is_ascii_digit()) && !var[1..].is_empty() {
                            let ty = ty.trim_end();
                            if let Some(base) = ty.strip_suffix('*') {
                                if !base.trim_end().ends_with('*') {
                                    ptr_of.insert(var, base.trim_end());
                                }
                            } else if !a.contains('*') {
                                adts(ty, &mut out);
                            }
                        }
                    }
                }
            }
            continue;
        }
        if !line.starts_with("  ") || !t.ends_with(';') {
            continue;
        }
        let Some((ty, rest)) = t.split_once(' ') else { continue };
        if !ty.chars().all(ident) || matches!(ty, "return" | "goto" | "if" | "else") || ty.starts_with("lust_") && !rest.contains('*') {
            continue;
        }
        // Declarators: `*l3`, `l4`, `*l2 = p2` at the top level of the list.
        let mut depth = 0i32;
        let mut start = true;
        let rb = rest.as_bytes();
        let mut i = 0;
        while i < rb.len() {
            let c = rb[i] as char;
            match c {
                '(' | '{' | '[' => depth += 1,
                ')' | '}' | ']' => depth -= 1,
                ',' if depth == 0 => {
                    start = true;
                    i += 1;
                    continue;
                }
                _ => {}
            }
            if start && depth == 0 && (c == '*' || c == 'l') {
                let stars = rest[i..].chars().take_while(|&c| c == '*' || c == ' ').filter(|&c| c == '*').count();
                let j = i + rest[i..].chars().take_while(|&c| c == '*' || c == ' ').count();
                let var: String = rest[j..].chars().take_while(|&c| ident(c)).collect();
                if var.starts_with('l') && var.len() > 1 && var[1..].chars().all(|c| c.is_ascii_digit()) {
                    let end = j + var.len();
                    if stars == 1 {
                        ptr_of.insert(&rest[j..end], ty);
                    } else if stars == 0 {
                        adts(ty, &mut out);
                    }
                }
                start = false;
            } else if c != ' ' {
                start = false;
            }
            i += 1;
        }
    }
    // Byte-offset reads: `(uint8_t*)(l3) + 312`, `(uint8_t*)((*(T**)(...)))`.
    let mut rest = code;
    while let Some(at) = rest.find("(uint8_t*)(") {
        let tail = &rest[at + 11..];
        let var: String = tail.chars().take_while(|&c| ident(c)).collect();
        if !var.is_empty() && tail[var.len()..].starts_with(')') {
            if let Some(ty) = ptr_of.get(var.as_str()) {
                adts(ty, &mut out);
            }
        } else if let Some(inner) = tail.strip_prefix("(*(") {
            let ty: String = inner.chars().take_while(|&c| ident(c)).collect();
            if inner[ty.len()..].starts_with("**)") {
                adts(&ty, &mut out);
            }
        }
        rest = tail;
    }
    out
}

/// Whether the fn with release C id `id` (16 hex digits) is in a copies profile's hot set.
fn is_hot(hot: &HashSet<u64>, id: &str) -> bool {
    u64::from_str_radix(id, 16).is_ok_and(|id| hot.contains(&id))
}

/// The largest fn definition a unit copies (`inline_callees`), by its `#[inline]`
/// attribute; 0 copies none.
/// The checks a `const_zst_addr` place still runs before its address is used: the
/// place's bounds checks (`[7u8; 0][i]` must panic, rustc's "index out of bounds"),
/// as the C text of the place `e` holds them. Empty for a place with no index.
fn zst_checks(pl: &Place, e: &str) -> String {
    if pl.proj.iter().any(|pr| matches!(pr, Proj::Index(_))) { format!("(void)&({e}), ") } else { String::new() }
}

fn inline_limit(a: InlineAttr) -> usize {
    match a {
        InlineAttr::None => INLINE_BYTES,
        InlineAttr::Hint => 4 * INLINE_BYTES,
        InlineAttr::Always => 8 * INLINE_BYTES,
        InlineAttr::Never => 0,
    }
}

/// Release C with a copies profile: a fn the profile did not see hot keeps its cleanup fn out
/// of line (`unwind::frame_inline`) from this frame cost on; a hot fn keeps it inlined up to
/// `LUST_RELEASE_FRAME_INLINE`. An inlined cleanup is specialized at each unwinding call;
/// in a cold fn with ~1,000 of them (decode_payload, a macro's match over every node kind)
/// that took clang's register coalescer 9 of the unit's 11 s, for code that does not run.
const COLD_FRAME_INLINE: usize = 40_000;

/// `code` (a fn's C) with its cleanup fn out of line when its frame costs more than
/// `COLD_FRAME_INLINE`: its flags (the frame struct's `uint8_t` members) plus one, times its
/// unwind points (the ladder entries it stores before a call or statement that may unwind).
fn cold_cleanup(code: &str, id: &str) -> String {
    let inlined = format!("static inline __attribute__((always_inline)) void cl{id}(");
    let Some(fr) = code.find(&format!("struct fr{id} {{\n")).filter(|_| code.contains(&inlined)) else { return code.to_string() };
    let flags = code[fr..].lines().skip(1).take_while(|l| *l != "};").filter(|l| l.starts_with("  uint8_t ")).count();
    let points = code.matches("L.st = ").count() - code.matches("L.st = 0;").count();
    if (flags + 1) * points <= COLD_FRAME_INLINE {
        return code.to_string();
    }
    code.replace(&inlined, &format!("static void cl{id}("))
}

/// Release C: the bytes of glue definitions a unit copies below the glue its own code calls
/// (`fn_unit_parts`); `LUST_RELEASE_INLINE_GLUE_KB` sets it (0: one level, as before).
fn inline_glue_budget() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("LUST_RELEASE_INLINE_GLUE_KB").ok().and_then(|v| v.parse().ok()).unwrap_or(32) * 1024)
}

/// False when `LUST_RELEASE_INLINE=0`: each release C unit then calls other units' fns and
/// glue (smaller units, less recompiled when a small fn changes).
fn inline_on() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var_os("LUST_RELEASE_INLINE").is_none_or(|v| v != "0"))
}

/// Release C plain fn units declare the Adts only their types hold as blocks
/// (`nested_block`); LUST_RELEASE_BLOCKS=0 defines them in full.
fn blocks_on() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var_os("LUST_RELEASE_BLOCKS").is_none_or(|v| v != "0"))
}

/// The id in a release C prototype of a fn body (`T f_<id>(...);`).
fn proto_body_id(e: &str) -> Option<&str> {
    // A `kdata` constant's guarded definition (cgen/kconst.rs), whose bytes may read as one.
    if e.starts_with('#') {
        return None;
    }
    let i = e.find(" f_").or_else(|| e.find("*f_"))? + 3;
    let id = e.get(i..i + 16)?;
    (e.as_bytes().get(i + 16) == Some(&b'(') && id.bytes().all(|b| b.is_ascii_hexdigit())).then_some(id)
}

/// The attributes and result of an outlined panic fn (`panic_outlined`), as its
/// definition starts in release C.
const PK_ATTRS: &str = "void __attribute__((cold, noinline, noreturn)) ";

/// The fn definition in `code` that a unit can copy as an inline definition.
struct PlainDef<'a> {
    /// The definition's first line, without ` {`.
    head: &'a str,
    def: &'a str,
    /// The headers of the outlined panic fns before it: external in release C, so the
    /// copy's unit declares them.
    pks: Vec<&'a str>,
    /// The definition's size in bytes (not its comment, panic fns or trampoline).
    len: usize,
    /// The bytes of it that make instructions (`code_len`): the hot copy limit reads this.
    code: usize,
    /// It holds kconst's static locals (`kconst_static`): only a hot copy may.
    statics: bool,
    /// Its unwind cleanup frame (`unwind::frame_struct`): the frame's struct, cleanup
    /// prototype and wrapper before the definition, and the `#undef`s and the cleanup fn after
    /// it, all named by the fn's tag; a copy takes them along. Only a hot copy may.
    frame: Option<(&'a str, &'a str)>,
}

/// The bytes of fn definition `def` (first line `head`) that make instructions: its head,
/// then its blocks from `bb0:;` on, without the blocks that only jump (`bbN:;` then
/// `goto bbM;`, which the C compiler folds away). Before the first block are only the
/// locals' declarations and kconst's static data and first-run setup.
fn code_len(def: &str, head: &str) -> usize {
    let Some(at) = def.find("\nbb0:;\n") else { return def.len() };
    let mut lines = def[at + 1..].split_inclusive('\n').peekable();
    let mut n = head.len();
    while let Some(l) = lines.next() {
        let jump = |g: &&str| g.starts_with("  goto bb") && g.ends_with(";\n");
        if l.starts_with("bb") && l.ends_with(":;\n") && lines.peek().is_some_and(jump) {
            lines.next();
        } else {
            n += l.len();
        }
    }
    n
}

/// Whether `line` declares one of kconst's static locals: a constant local `lN`, its slot
/// `lkN` and descriptor `lkdN`, the literal slots `lks` and their flag `lks_ok`.
fn kconst_static(line: &str) -> bool {
    let Some(rest) = line.strip_prefix("  static ") else { return false };
    let decl = rest.split(['=', '[', ';']).next().unwrap_or("");
    let name = decl.trim_end().rsplit([' ', '*']).next().unwrap_or("");
    let num = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    name == "lks" || name == "lks_ok" || name.strip_prefix("lkd").is_some_and(num) || name.strip_prefix("lk").is_some_and(num) || name.strip_prefix('l').is_some_and(num)
}

/// The one fn definition at the start of `code` (after its outlined panics and its
/// comment line): None when the text holds anything an inline definition may not have
/// (static storage other than kconst's, a static helper). An unwind cleanup frame is the
/// one exception (`PlainDef::frame`): its struct, cleanup prototype and wrapper come before
/// the comment line, its variable and member macros are in the definition, and after the
/// definition come only the macros' `#undef`s and the cleanup fn `cl<tag>` (`unwind::cleanup_fn`).
fn plain_fn_def(code: &str) -> Option<PlainDef<'_>> {
    let mut rest = code;
    let mut pks = Vec::new();
    while rest.starts_with(PK_ATTRS) {
        pks.push(&rest[..rest.find(" {\n")?]);
        rest = &rest[rest.find("\n}\n")? + 3..];
    }
    let mut pre = None;
    if let Some(after) = rest.strip_prefix("struct fr") {
        let tag = &after[..after.find(" {\n")?];
        let wrap = rest.find(&format!("\nstatic inline __attribute__((always_inline)) void clw{tag}(struct fr{tag} *Lc) {{"))? + 1;
        let e = rest[wrap..].find('\n')? + wrap + 1;
        pre = Some((tag, &rest[..e]));
        rest = &rest[e..];
    }
    // Then the fn alone: its comment line first (any other prelude holds static helpers
    // the fn calls: vtables, thunks).
    if !rest.starts_with("/* ") {
        return None;
    }
    let start = rest.find(" */\n")? + 4;
    let end = rest[start..].find("\n}\n")? + start + 3;
    let def = &rest[start..end];
    let head = def.split(" {\n").next()?;
    let (frame, body) = match pre {
        Some((tag, pre)) => {
            let after = &rest[end..];
            let undefs = |mut at: usize| -> Option<usize> {
                while after[at..].starts_with("#undef ") {
                    at += after[at..].find('\n')? + 1;
                }
                Some(at)
            };
            let cl = undefs(0)?;
            let line = &after[cl..cl + after[cl..].find('\n')?];
            if !line.starts_with("static ") || !line.ends_with(&format!(" void cl{tag}(struct fr{tag} *Lc) {{")) {
                return None;
            }
            let post = undefs(after[cl..].find("\n}\n")? + cl + 3)?;
            let var = format!("  struct fr{tag} L __attribute__((cleanup(clw{tag})));\n");
            (Some((pre, &after[..post])), std::borrow::Cow::Owned(def.replacen(&var, "", 1)))
        }
        None => (None, std::borrow::Cow::Borrowed(def)),
    };
    // `#define`: an over-aligned local's macro, whose `#undef` follows the fn (a frame's
    // macros too, `post`). Static storage only as kconst's locals (`statics`): each unit's
    // copy then has its own (clang and gcc take them in an inline definition), which only
    // cache the canonical program-wide addresses (cgen/kconst.rs), so identity stays the table's.
    let statics = body.lines().any(kconst_static);
    let other_static = body.matches("static ").count() != body.lines().filter(|l| kconst_static(l)).count();
    (!other_static && !body.contains("__attribute__") && (frame.is_some() || !body.contains("#define")) && !head.contains('\n'))
        .then_some(PlainDef { head, def, pks, len: def.len(), code: code_len(def, head), statics, frame })
}

/// Release C: the small fns that the fns in `slots` call and another unit holds; this
/// unit gets them as C99 inline definitions, so the C compiler can inline them without
/// LTO (their holder keeps the external definition, so calls and addresses are the same).
/// At a `deep` level (past `INLINE_DEPTH`) only tiny and `#[inline]` fns. With a copies
/// profile (`hot`, `LUST_PGO_COPIES`), only the fns it saw hot, by `hot_pick` at every level
/// (`frames`: the frame rule's walk, `FrameWalk`).
fn inline_callees<'a>(fns: &[FnOut], externs: impl Iterator<Item = &'a str>, skip: &HashSet<usize>, deep: bool, hot: Option<&CopyHot>, frames: Option<FrameWalk<'_>>) -> Vec<usize> {
    let mut out = BTreeSet::new();
    let rec = record::on();
    for e in externs {
        let Some(id) = proto_body_id(e) else { continue };
        if rec {
            record::read(record::Read::SlotOf(id.to_string()));
        }
        let Some(c) = names::slot_of_id(id).map(|c| c as usize) else { continue };
        if skip.contains(&c) {
            continue;
        }
        // A copies profile never copies a callee it did not see hot (its sets are part of
        // the unit's identity, so that needs no read).
        if hot.is_some_and(|h| !is_hot(&h.hot, id)) {
            continue;
        }
        let pick = fns.get(c).is_some_and(|f| match hot {
            Some(h) => hot_pick(f, c, id, h, frames.map(|w| w.today)),
            None => inline_pick(f, deep),
        });
        let new = frames.filter(|w| !w.today.contains(&c));
        let pick = pick && new.is_none_or(|w| w.take());
        // B1 (`record`): a copied callee's whole output is read; of one left out, only that.
        // A copy outside `today` also reads its pick, which reads the program's big ADTs.
        if rec {
            if pick {
                record::read(record::Read::Fn(c));
            }
            if !pick || new.is_some() {
                record::read(if hot.is_some() { record::Read::PickHot(c) } else { record::Read::Pick(c, deep) });
            }
        }
        if pick {
            out.insert(c);
        }
    }
    out.into_iter().collect()
}

/// Whether `inline_callees` copies `f` (a callee another unit holds), at a `deep` level or not.
fn inline_pick(f: &FnOut, deep: bool) -> bool {
    f.error.is_none()
        && f.pick_info().is_some_and(|d| {
            !d.statics && !d.frame && d.len <= inline_limit(f.inline) && (!deep || d.len <= INLINE_TINY_BYTES || matches!(f.inline, InlineAttr::Hint | InlineAttr::Always))
        })
}

/// Whether `f`, a callee a copies profile saw hot, is small enough for a copy (`hot_pick`):
/// up to `HOT_COPY_BYTES` of code (or its `#[inline]` limit when larger) at every level,
/// kconst's static locals and an unwind cleanup frame (`PlainDef::frame`) and all. Code, not
/// text (`PlainDef::code`): a match over a parameter that each caller passes as a constant
/// has many one-jump blocks, which fold away.
fn inline_pick_hot(f: &FnOut) -> bool {
    f.error.is_none() && f.inline != InlineAttr::Never && f.pick_info().is_some_and(|d| d.code <= inline_limit(f.inline).max(HOT_COPY_BYTES))
}

/// The hot rule's pick of `f` (slot `c`, release C id `id`), a callee `hot` saw hot. With
/// `today` None, today's rule: `inline_pick_hot`, and no fn with an unwind cleanup frame.
/// Else (`today`: the unit's copies by that rule) the frame rule: a fn with a frame too when
/// `hot.frames` holds it, but a copy outside `today` (a frame fn, or a callee below one) only
/// when its text reads no big ADT (`FnOut::layout_reads`). So the copies the frame rule adds
/// bring no big context struct's layout into a unit, and an edit of one misses no more units.
fn hot_pick(f: &FnOut, c: usize, id: &str, hot: &CopyHot, today: Option<&HashSet<usize>>) -> bool {
    let frame = f.pick_info().is_some_and(|d| d.frame);
    inline_pick_hot(f)
        && match today {
            None => !frame,
            Some(t) => t.contains(&c) || ((!frame || is_hot(&hot.frames, id)) && f.layout_reads().is_disjoint(&hot.big)),
        }
}

/// The frame rule's walk of one unit (`inline_callees`): the unit's copies by today's rule
/// (`hot_pick`), and how many copies the rule may still add (`NEW_COPIES_PER_UNIT`).
#[derive(Clone, Copy)]
struct FrameWalk<'a> {
    today: &'a HashSet<usize>,
    left: &'a std::cell::Cell<usize>,
}

impl FrameWalk<'_> {
    /// Takes one new copy from the unit's allowance; false when none is left.
    fn take(&self) -> bool {
        let n = self.left.get();
        n > 0 && {
            self.left.set(n - 1);
            true
        }
    }
}

/// The deeper copy levels below `frontier` (`fn_unit_parts`): the callees of each level's
/// copies, added to `inl`, until a level adds none; to `INLINE_DEPTH_TINY` levels, or with a
/// copies profile (`hot`, `frames` as `inline_callees`') to `HOT_COPY_DEPTH`.
fn copy_levels(fns: &[FnOut], own: &HashSet<usize>, inl: &mut Vec<usize>, mut frontier: Vec<usize>, hot: Option<&CopyHot>, frames: Option<FrameWalk<'_>>) {
    for level in 1..if hot.is_some() { HOT_COPY_DEPTH } else { INLINE_DEPTH_TINY } {
        let skip: HashSet<usize> = own.iter().chain(inl.iter()).copied().collect();
        let more = inline_callees(fns, frontier.iter().flat_map(|&s| fns[s].externs.iter().map(|e| &**e)), &skip, level >= INLINE_DEPTH, hot, frames);
        if more.is_empty() {
            break;
        }
        inl.extend(&more);
        frontier = more;
    }
}

/// The unit for `slots` (`fns` is indexed by slot; empty slots have no code). Its
/// functions are static; the function `register` stores them in `lust_fns`.
/// `main_slot` is the slot of `p.main` (not its `LocalDefId`: slots are
/// stable across edits, local ids are not).
pub fn fn_unit(p: &Program, fns: &[FnOut], slots: &[usize], g: &GlueSet, register: &str, main_slot: Option<u32>) -> String {
    fn_unit_parts(p, fns, slots, &[], g, register, main_slot, None, None).0
}

/// `fn_unit`, and for the LLVM backend (cgen/ll.rs) the C of the unit's helpers: the same
/// declarations, then each fn's `ll_c` (empty when no fn of the unit has LLVM IR). The fns
/// in `inl` (cross-unit inlining, `ll::ll_inline_set`) add their declarations and helpers.
/// `copy_hot`: release C, what a copies profile ran often (`inline_callees`).
#[allow(clippy::too_many_arguments)]
pub fn fn_unit_parts(
    p: &Program,
    fns: &[FnOut],
    slots: &[usize],
    ll_inl: &[usize],
    g: &GlueSet,
    register: &str,
    main_slot: Option<u32>,
    c_refs: Option<&ll::CRefs>,
    copy_hot: Option<&CopyHot>,
) -> (String, String) {
    // B1 (`record`): every text appended below is one recorded piece; an LLVM-backend unit
    // is never recorded.
    let mut c = unit_header();
    record::piece(record::Kind::Fixed, 0, &c);
    let llvm = slots.iter().any(|&s| !fns[s].ll.is_empty());
    // The LLVM backend's internal ABI returns 16-byte values as this pair (`ll::Pass::Pair`).
    if llvm {
        record::abandon();
        c.push_str(ll::PAIR_TYPEDEF);
    }
    if p.unwind_tables {
        c.push_str(noreturn_decls());
        record::piece(record::Kind::Fixed, 1, noreturn_decls());
    }
    if record::on() {
        slots.iter().for_each(|&s| record::read(record::Read::Fn(s)));
    }
    let mut types = HashSet::new();
    let mut named = HashSet::new();
    let mut seen: crate::intern::FxSet<&(Glue, CTy)> = crate::intern::FxSet::default();
    // Release C: small callees held by other units, as inline definitions here. The LLVM
    // backend calls fns through `fl_<id>` and gets their copies from `ll_inl` instead.
    let own: HashSet<usize> = slots.iter().copied().collect();
    let inline = names::release() && inline_on();
    // With a copies profile, only the unit's hot fns get copies (a cold unit gets none).
    let callers: Vec<usize> = slots.iter().copied().filter(|&s| copy_hot.is_none_or(|h| names::fn_tag_opt(s as u32).is_some_and(|id| is_hot(&h.hot, &id)))).collect();
    let walk = |frames: Option<FrameWalk<'_>>| {
        let mut inl = if inline && !llvm { inline_callees(fns, callers.iter().flat_map(|&s| fns[s].externs.iter().map(|e| &**e)), &own, false, copy_hot, frames) } else { Vec::new() };
        // Deeper levels: the small callees of the inline callees.
        let frontier = inl.clone();
        copy_levels(fns, &own, &mut inl, frontier, copy_hot, frames);
        inl
    };
    // With a copies profile, today's copies first, then the frame rule's (`hot_pick`).
    let mut today: HashSet<usize> = if copy_hot.is_some() { walk(None).into_iter().collect() } else { HashSet::new() };
    let left = std::cell::Cell::new(NEW_COPIES_PER_UNIT);
    let mut inl = walk(copy_hot.is_some().then_some(FrameWalk { today: &today, left: &left }));
    for f in slots.iter().chain(&inl).chain(ll_inl).map(|&s| &fns[s]) {
        types.extend(f.types.iter().cloned());
        named.extend(f.named.iter().cloned());
        seen.extend(f.glue.iter());
    }
    // Release C: small plain glue the unit calls (drop, eq, clone of simple types), as
    // inline definitions, and at every level below the glue those call (a field's drop, a
    // field's default), within `inline_glue_budget` bytes per unit; the glue left out gets
    // its prototype, which takes its types by pointer. The LLVM backend gets the same set
    // through its helpers' C (`cc` links it into the IR).
    let mut inl_glue: crate::intern::FxSet<&(Glue, CTy)> = crate::intern::FxSet::default();
    // What the inline glue reads, one step through pointers (`type_decls_with`'s `deep`).
    // Glue that only copies its fields or passes them on (`GlueSet::passes_fields`: an
    // aggregate's drop, clone, eq, default...) holds its types as the unit's own code does:
    // an Option of an Rc then needs no layout of the Rc's value, so the unit does not change
    // when that value's struct does. A pointer's drop or clone glue holds the block it
    // reads in place (`GlueSet::pointer_block`) and no more: the step from an `Arc<T>`
    // key's `T` defined the count blocks of what `T` points at, with their values' sizes.
    let mut glue_types: HashSet<CTy> = HashSet::new();
    if inline {
        let plain = |k: &(Glue, CTy)| {
            g.def_map.get(k).is_some_and(|d| d.len() <= INLINE_BYTES && !d.contains("static ") && !d.contains("__attribute__") && !d.contains("#define"))
        };
        // Level by level in prototype order, so the budget picks the same glue every build.
        let mut level: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
        level.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
        let mut budget = inline_glue_budget();
        let mut nested = false;
        while !level.is_empty() {
            let mut next: Vec<&(Glue, CTy)> = Vec::new();
            for k in level {
                if !plain(k) {
                    continue;
                }
                if nested {
                    let n = g.def_map[k].len();
                    if n > budget {
                        continue;
                    }
                    budget -= n;
                }
                inl_glue.insert(k);
                if GlueSet::passes_fields(k) {
                    g.held_types(k, &mut types, &mut named);
                } else if let Some(blocks) = GlueSet::pointer_block(k) {
                    types.extend(blocks);
                    g.held_types(k, &mut types, &mut named);
                } else {
                    g.def_types(k, &mut glue_types);
                }
                for d in g.deps.get(k).into_iter().flatten() {
                    collect_types(&d.1, &mut named);
                    if seen.insert(d) {
                        next.push(d);
                    }
                }
            }
            next.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
            level = next;
            nested = true;
        }
        // The small fns the inline glue calls (a written `PartialEq` or `Drop`), inline too.
        let skip: HashSet<usize> = own.iter().chain(&inl).copied().collect();
        let glue_externs = || inl_glue.iter().flat_map(|k| g.externs.get(*k).into_iter().flatten().map(String::as_str));
        // With a copies profile, today's copies below the glue join `today` first.
        if copy_hot.is_some() && !llvm {
            let mut t = inl.clone();
            let m = inline_callees(fns, glue_externs(), &skip, false, copy_hot, None);
            t.extend(&m);
            copy_levels(fns, &own, &mut t, m, copy_hot, None);
            today.extend(t);
        }
        let frames = copy_hot.is_some().then_some(FrameWalk { today: &today, left: &left });
        let more = if llvm { Vec::new() } else { inline_callees(fns, glue_externs(), &skip, false, copy_hot, frames) };
        let start = inl.len();
        inl.extend(&more);
        // With a copies profile, their hot callees too (a hasher's `write` below a hash glue).
        if copy_hot.is_some() {
            copy_levels(fns, &own, &mut inl, more, copy_hot, frames);
        }
        for &s in &inl[start..] {
            types.extend(fns[s].types.iter().cloned());
            named.extend(fns[s].named.iter().cloned());
            seen.extend(fns[s].glue.iter());
        }
    }
    // The inline definitions in fn id order: slot order carries a persistent
    // session's history, and its units are a one-shot build's.
    inl.sort_by_cached_key(|&s| names::fn_tag_opt(s as u32));
    // The termination entry below names main's return type directly.
    // Declare it in this unit even when main's cached `FnOut` predates
    // the return-type edit (a warm unit must not name an undeclared
    // `Result` struct).
    let main_in_unit = main_slot.filter(|&s| slots.contains(&(s as usize)) && fns.get(s as usize).is_some_and(FnOut::has_code));
    let term_main = main_in_unit.and_then(|s| p.main.map(|m| (m, s))).filter(|&(m, _)| {
        let ret = p.fn_info(m).ret;
        p.tys.is_exit_code(ret) || p.tys.result_args(ret).is_some()
    });
    if let Some((m, _)) = term_main {
        let ret = p.fn_info(m).ret;
        if record::on() {
            read_type(&cty(&p.tys, ret));
            if let Some((ok_t, err_t)) = p.tys.result_args(ret) {
                read_type(&cty(&p.tys, ok_t));
                read_type(&cty(&p.tys, err_t));
            }
        }
        collect_types(&cty(&p.tys, ret), &mut types);
    }
    // With a frozen shared set, glue that is not shared is static in this unit: walk its deps
    // too, and stop at shared keys (their deps live in the glue unit). Shared keys still need
    // their prototype, and every reached key needs its C type declared.
    let hybrid = g.shared.is_some();
    if hybrid {
        let mut stack: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
        while let Some(k) = stack.pop() {
            if g.is_shared(k) {
                // Only its prototype is here, which takes its type by pointer: release C
                // needs what a `&T` does (fn pointer typedefs have no forward form) and
                // declares the rest; dev C defines it all.
                if names::release() {
                    let mut held = Vec::new();
                    read_type(&k.1);
                    by_value_deps(&CTy::Ref(Box::new(k.1.clone())), &mut held);
                    types.extend(held);
                    collect_types(&k.1, &mut named);
                } else {
                    collect_types(&k.1, &mut types);
                }
            } else {
                g.def_types(k, &mut types);
                if let Some(deps) = g.deps.get(k) {
                    for dep in deps {
                        if seen.insert(dep) {
                            stack.push(dep);
                        }
                    }
                }
            }
        }
    }
    if record::on() {
        seen.iter().for_each(|k| record::read(record::Read::Glue(k.0, k.1.clone())));
        if main_slot.is_some_and(|m| slots.contains(&(m as usize))) {
            record::read(record::Read::Main);
        }
    }
    // Only the statics this unit's code (and its local glue) names:
    // their types and their extern declarations. Every static in
    // every unit was pure repetition in a program with many statics.
    // The texts this unit prints: its own fns' and its inline copies'.
    let texts: Vec<(usize, std::borrow::Cow<str>)> = slots.iter().chain(&inl).chain(ll_inl).map(|&s| (s, fns[s].code_text())).collect();
    let at: crate::intern::FxMap<usize, usize> = texts.iter().enumerate().map(|(i, t)| (t.0, i)).collect();
    let text_of = |s: usize| at.get(&s).map_or("", |&i| texts[i].1.as_ref());
    let used = used_statics(
        p,
        texts
            .iter()
            .flat_map(|(s, t)| [t.as_ref(), fns[*s].ll_c.as_str()])
            .chain(seen.iter().filter(|k| hybrid && !g.is_shared(k)).map(|k| g.def_map[*k].as_str())),
    );
    for &i in &used {
        collect_types(&cty(&p.tys, p.statics[i].ty), &mut types);
    }
    named.retain(|t| !types.contains(t));
    // Inline glue declares its types as a glue shard declares the same glue
    // (`names::glue_shard_texts`): one step deep only for glue that reads through pointers;
    // the rest of the unit only by value.
    let decls = if names::release() { Decls::ByValue { blocks: !llvm && blocks_on() } } else { Decls::Full };
    named.retain(|t| !glue_types.contains(t));
    type_decls_with(p, &mut c, &types, &named, decls, &glue_types);
    let m = c.len();
    c.push_str(&static_decls_for(p, &used));
    record::piece(record::Kind::Statics, 0, &c[m..]);
    // Release C (`names`): the prototypes and location slots that the code (and its
    // static glue) names outside itself, in one sorted list.
    let mut externs: BTreeSet<&str> = BTreeSet::new();
    for &s in slots.iter().chain(&inl).chain(ll_inl) {
        externs.extend(fns[s].externs.iter().map(|e| &**e));
    }
    // An inline callee's plain prototype would make its definition here external.
    let inl_ids: HashSet<String> = inl.iter().filter_map(|&s| names::fn_tag_opt(s as u32)).collect();
    externs.retain(|e| proto_body_id(e).is_none_or(|id| !inl_ids.contains(id)));
    for k in seen.iter().filter(|k| (hybrid && !g.is_shared(k)) || inl_glue.contains(*k)) {
        externs.extend(g.externs.get(*k).into_iter().flatten().map(String::as_str));
    }
    externs.retain(|e| proto_body_id(e).is_none_or(|id| !inl_ids.contains(id)));
    let m = c.len();
    externs.into_iter().for_each(|e| c.push_str(e));
    record::piece(record::Kind::Externs, 0, &c[m..]);
    // Inline fn definitions: declared before any glue or body can call them.
    let defs: Vec<PlainDef> = inl.iter().filter_map(|&s| plain_fn_def(text_of(s))).collect();
    for d in &defs {
        let m = c.len();
        for pk in &d.pks {
            let _ = writeln!(c, "{pk};");
        }
        if let Some((pre, _)) = d.frame {
            c.push_str(pre);
        }
        let _ = writeln!(c, "inline {};", d.head);
        record::piece(record::Kind::InlineDef, record::key(&d.head), &c[m..]);
    }
    let mut keys: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
    keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
    for k in &keys {
        let m = c.len();
        if hybrid && !g.is_shared(k) {
            c.push_str("static ");
        } else if inl_glue.contains(*k) {
            c.push_str("inline ");
        }
        c.push_str(&g.protos[*k]);
        record::piece(record::Kind::GlueProto, record::key(&g.protos[*k]), &c[m..]);
    }
    for k in keys.iter().filter(|k| inl_glue.contains(**k)) {
        let m = c.len();
        c.push_str("inline ");
        c.push_str(&g.def_map[*k]);
        record::piece(record::Kind::GlueDef, record::key(&g.protos[*k]), &c[m..]);
    }
    if hybrid {
        for k in keys.iter().filter(|k| !g.is_shared(k)) {
            let m = c.len();
            c.push_str("static ");
            c.push_str(&g.def_map[*k]);
            record::piece(record::Kind::GlueDef, record::key(&g.protos[*k]), &c[m..]);
        }
    }
    for d in &defs {
        let m = c.len();
        let _ = write!(c, "inline {}\n", d.def);
        if let Some((_, post)) = d.frame {
            c.push_str(post);
        }
        record::piece(record::Kind::InlineDef, record::key(&d.head), &c[m..]);
    }
    let helpers = if llvm {
        let mut h = c.clone();
        slots.iter().chain(ll_inl).for_each(|&s| h.push_str(&fns[s].ll_c));
        // The plain C of an LLVM unit holds only its fns' C ABI wrappers and trampolines, and
        // cc.rs compiles them after the helpers' C, which declares every type they name
        // (`compile_pair`): nothing comes before the mark (a main entry keeps it all).
        if term_main.is_none() {
            c = ll::BODY_MARK.to_string();
        }
        h
    } else {
        String::new()
    };
    for &s in slots {
        let f = &fns[s];
        let m = c.len();
        // An LLVM fn's C is its C ABI wrapper and trampoline: kept only when a text names them.
        match (c_refs, f.ll.is_empty(), names::fn_tag_opt(s as u32)) {
            (Some(r), false, Some(id)) => c.push_str(&r.c_body(text_of(s), &id)),
            (_, _, Some(id)) if copy_hot.is_some_and(|h| !is_hot(&h.hot, &id)) => c.push_str(&cold_cleanup(text_of(s), &id)),
            _ => c.push_str(text_of(s)),
        }
        record::piece(record::Kind::Body, s as u64, &c[m..]);
    }
    // Termination entry for a `main` returning `ExitCode` or
    // `Result<T, E>` (T `()` or `ExitCode`): call main through the
    // table; on Err print `Error: {err:?}` to stderr and exit 1, as
    // Rust does; an `ExitCode` is the exit status. Registered below
    // in `lust_main_entry_p`, which the main unit prefers over the
    // plain void call. The Debug and Drop glue it calls is wanted
    // by main's own FnOut (see `gen_fn`).
    let entry_at = c.len();
    if let Some((m, idx)) = term_main {
        let ret = p.fn_info(m).ret;
        let rc = cty(&p.tys, ret);
        let rt = ctype(&rc);
        let cast = fn_ptr_cast(p, m);
        // Main's body is in this unit: release C calls it by name.
        let target = if names::release() { names::body(idx) } else { format!("lust_fns[{idx}]") };
        let _ = writeln!(c, "static int lust_main_entry_impl(void) {{");
        if ret_is_large(p, m) {
            let _ = writeln!(c, "  {rt} r; ({cast}{target})(&r);");
        } else {
            let _ = writeln!(c, "  {rt} r = ({cast}{target})();");
        }
        if p.unwind {
            let _ = writeln!(c, "  if (lust_unw_pending && lust_unw_mine()) return 0;");
        }
        match p.tys.result_args(ret) {
            Some((ok_t, err_t)) => {
                let disc = disc_call(p, &rc, "(&r)");
                let field = variant_field(p, &rc, "r", 1, 0);
                let ec = cty(&p.tys, err_t);
                let ok = if p.tys.is_exit_code(ok_t) { format!(" else {{ rc = {}; }}", variant_field(p, &rc, "r", 0, 0)) } else { String::new() };
                let _ = writeln!(c, "  int rc = 0;");
                let _ = writeln!(
                    c,
                    "  if ({disc}) {{ lust_sink k; lust_print_begin(&k, 1); lust_Formatter f; lust_f_init(&f, &k); lust_f_write(&f, \"Error: \", 7); (void)dbg_{}(&f, &{field}); lust_f_write(&f, \"\\n\", 1); lust_print_end(1); rc = 1; }}{ok}",
                    mangle(&ec)
                );
            }
            None => {
                let _ = writeln!(c, "  int rc = r;");
            }
        }
        if needs_drop_c(p, &rc) {
            let _ = writeln!(c, "  drop_{}(&r);", mangle(&rc));
        }
        let _ = writeln!(c, "  return rc;\n}}");
    }
    record::piece(record::Kind::Entry, 0, &c[entry_at..]);
    let register_at = c.len();
    let _ = writeln!(c, "void {register}(void) {{");
    // Release C calls bodies by name: no table to fill.
    for &i in slots.iter().filter(|&&i| fns[i].has_code() && !names::release()) {
        let _ = writeln!(c, "  lust_fns[{i}] = (lust_fnptr)f{i};");
        let _ = writeln!(c, "  lust_tramps[{i}] = (lust_fnptr)tramp{i};");
    }
    if term_main.is_some() {
        let _ = writeln!(c, "  lust_main_entry_p = lust_main_entry_impl;");
    } else if main_in_unit.is_some() {
        // This unit holds main and main now returns `()`: clear an
        // entry a base unit from an earlier build may have registered
        // for a `Result`/`ExitCode` main (overlays register after the
        // base, so this wins).
        let _ = writeln!(c, "  lust_main_entry_p = 0;");
    }
    c.push_str("}\n");
    record::piece(record::Kind::Register, 0, &c[register_at..]);
    (c, helpers)
}

/// The members of one C struct for fields at layout offsets: fields in
/// offset order with explicit padding byte arrays between them, so the
/// C offsets equal the layout offsets no matter what the C compiler
/// would pick on its own. `fields` holds (declaration, field layout,
/// offset) per field; `total` pads to the full size when given.
fn layout_members(fields: &[(String, Layout, u64)], total: Option<u64>, struct_align: u64) -> String {
    let mut order: Vec<usize> = (0..fields.len()).collect();
    order.sort_by(|&a, &b| fields[a].2.cmp(&fields[b].2).then(fields[b].1.align.cmp(&fields[a].1.align)).then(a.cmp(&b)));
    let mut members: Vec<String> = Vec::new();
    let mut cur = 0u64;
    let mut pad = 0u32;
    for &i in &order {
        let (decl, fl, off) = &fields[i];
        if *off > cur {
            members.push(format!("uint8_t _p{pad}[{}]", off - cur));
            pad += 1;
            cur = *off;
        }
        members.push(decl.clone());
        cur = cur.max(off + fl.size);
    }
    if let Some(sz) = total
        && sz > cur
    {
        members.push(format!("uint8_t _p{pad}[{}]", sz - cur));
    }
    let natural = fields.iter().map(|f| f.1.align).max().unwrap_or(1);
    if struct_align > natural && !members.is_empty() {
        members[0] = format!("_Alignas({struct_align}) {}", members[0]);
    }
    members.iter().map(|m| format!("{m}; ")).collect()
}

/// The compile-time layout proof for one emitted type: the C sizeof and
/// _Alignof must equal the layout the type was emitted from.
fn layout_assert(out: &mut String, ct: &str, l: &Layout) {
    let _ = writeln!(out, "_Static_assert(sizeof({ct}) == {} && _Alignof({ct}) == {}, \"layout\");", l.size, l.align);
}

/// One field's layout for `layout_members`, for a parent whose own
/// `c_layout` is already exact. A miss here means the parent check and
/// this one disagree; size 0 keeps the C layout assert as the failure.
fn field_layout(p: &Program, t: &CTy) -> Layout {
    c_layout(p, t).unwrap_or_else(|| plain_layout(0, 1))
}

/// Emits one layout-exact enum type (an Adt enum or an Option) plus its
/// `disc_<mangle>` reader. The shape is one union: a struct per variant
/// with fields at their absolute layout offsets, the tag scalar or a
/// niche view struct, and a size member that pins the total size and
/// alignment. `opener` is the declaration up to the opening brace.
fn emit_enum_decl(p: &Program, out: &mut String, opener: &str, t: &CTy, variants: &[Vec<CTy>], l: &Layout) {
    let ct = ctype(t);
    let _ = write!(out, "{opener} {{ union {{ ");
    // An explicit tag also appears as the first member of every variant
    // struct, so a value can be built with one compound literal that
    // designates a single union member (see `make_variant`).
    let explicit = match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => Some((size, signed)),
        _ => None,
    };
    // A niche tag scalar also appears as a member of every non-niche
    // variant struct (whose fields avoid its bytes by construction),
    // for the same single-designator reason.
    let niche = match l.enum_tag {
        Some(EnumTag::NicheFilled { variant, niche, .. }) => Some((variant, niche)),
        _ => None,
    };
    for (vi, v) in variants.iter().enumerate() {
        let has_synth = explicit.is_some() || niche.is_some_and(|(nv, _)| vi != nv);
        if v.is_empty() && !has_synth {
            continue;
        }
        let mut fields: Vec<(String, Layout, u64)> = Vec::new();
        if let Some((size, signed)) = explicit {
            fields.push((format!("{} _tag", tag_c_type(size, signed)), plain_layout(size, size), 0));
        }
        if let Some((nv, n)) = niche
            && vi != nv
        {
            fields.push((format!("{} _s", tag_c_type(n.scalar_size, false)), plain_layout(n.scalar_size, n.scalar_size), n.offset));
        }
        fields
            .extend(v.iter().enumerate().map(|(fi, ft)| (format!("{} f{fi}", ctype(ft)), field_layout(p, ft), l.variant_offsets[vi][fi])));
        let _ = write!(out, "struct {{ {}}} v{vi}; ", layout_members(&fields, None, 1));
    }
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let _ = write!(out, "{} _tag; ", tag_c_type(size, signed));
        }
        Some(EnumTag::NicheFilled { niche: Niche { offset, scalar_size, .. }, .. }) => {
            let pad = if offset > 0 { format!("uint8_t _p[{offset}]; ") } else { String::new() };
            let _ = write!(out, "struct {{ {pad}{} _s; }} _n; ", tag_c_type(scalar_size, false));
        }
        _ => {}
    }
    if l.size > 0 {
        let al = if l.align > 1 { format!("_Alignas({}) ", l.align) } else { String::new() };
        let _ = write!(out, "{al}uint8_t _size[{}]; ", l.size);
    }
    out.push_str("} u; }");
    if opener.starts_with("typedef") {
        let _ = write!(out, " {ct}");
    }
    out.push_str(";\n");
    layout_assert(out, &ct, l);
    let m = mangle(t);
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let discs = adt_discs(p, t);
            if size >= 16 {
                // A two-word tag cannot switch: compare both words.
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{");
                for (vi, &d) in discs.iter().enumerate() {
                    let bits = d as u128;
                    let _ =
                        write!(out, " if (p->u._tag.lo == {}ULL && p->u._tag.hi == {}ULL) return {vi};", bits as u64, (bits >> 64) as u64);
                }
                let _ = writeln!(out, " return 0; }}");
            } else if !discs_sequential(&discs) {
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{ switch (p->u._tag) {{");
                for (vi, &d) in discs.iter().enumerate() {
                    let _ = write!(out, " case {}: return {vi};", disc_lit(d, size, signed));
                }
                let _ = writeln!(out, " default: return 0; }} }}");
            }
        }
        Some(EnumTag::NicheFilled { variant, niche, first, last, start }) => {
            // Niche value `start + d` is variant `first + d` for `d` up to
            // `last - first`; any other value is the dataful variant.
            let span = last - first + 1;
            if niche.scalar_size >= 16 {
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{");
                for vi in (first..=last).filter(|&i| i != variant) {
                    let bits = niche_tag_value(niche, first, start, vi);
                    let _ = write!(
                        out,
                        " if (p->u._n._s.lo == {}ULL && p->u._n._s.hi == {}ULL) return {vi};",
                        bits as u64,
                        (bits >> 64) as u64
                    );
                }
                let _ = writeln!(out, " return {variant}; }}");
            } else {
                // Wrapping distance from the first niche value: values
                // that wrap past the top of the scalar range read back
                // as small distances.
                let mask: u64 = if niche.scalar_size >= 8 { u64::MAX } else { (1u64 << (niche.scalar_size * 8)) - 1 };
                let _ = writeln!(
                    out,
                    "static inline uint32_t disc_{m}(const {ct} *p) {{ uint64_t s = p->u._n._s; uint64_t d = (s - {}ULL) & {mask}ULL; if (d < {span}ULL) return {first} + (uint32_t)d; return {variant}; }}",
                    start as u64
                );
            }
        }
        _ => {}
    }
}

/// Declares the given types, plus every type they contain (by value or inside a Vec).
/// The C types the definition of `t` holds by value: they must be defined before it.
fn def_deps(p: &Program, t: &CTy) -> Vec<CTy> {
    let mut deps = Vec::new();
    match t {
        CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| by_value_deps(&cty(&p.tys, f.ty), &mut deps)),
        CTy::Option(e) => by_value_deps(e, &mut deps),
        CTy::Result(a, b) => {
            by_value_deps(a, &mut deps);
            by_value_deps(b, &mut deps);
        }
        CTy::Tuple(es) => es.iter().for_each(|e| by_value_deps(e, &mut deps)),
        CTy::Array(e, _) => by_value_deps(e, &mut deps),
        CTy::ArrayIter(e, n) => by_value_deps(&CTy::Array(e.clone(), *n), &mut deps),
        CTy::OptIter(_, e) => by_value_deps(&CTy::Option(e.clone()), &mut deps),
        // A slice holds `e*` only: every struct type has a forward
        // typedef above, so only a fn pointer typedef must come
        // first. Counting `e` itself made a false cycle for a
        // recursive `enum A { P(Arc<[A]>) }`, and the DFS start
        // order (ADT ids, which follow the file name) then decided
        // which side was incomplete.
        CTy::Slice(e) => by_value_deps(&CTy::Ref(e.clone()), &mut deps),
        // Release C's count block holds no value (`rc_head`).
        CTy::Rc(e) if rc_head(p, e).is_some() => {}
        CTy::Rc(e) | CTy::RefCell(e) => by_value_deps(e, &mut deps),
        CTy::Sync(k, e) if k.is_cell_struct() => by_value_deps(e, &mut deps),
        // A fn pointer typedef is a declarator: its parameter and
        // return structs may be incomplete there (C11 6.7.6.3), and
        // each has a forward typedef above. Only another fn pointer
        // typedef must come first. Counting the structs made a false
        // cycle for `struct ByFn<T> { g: Option<fn(ByFn<(T, T)>)> }`
        // that left the Option incomplete inside the struct.
        CTy::FnPtr(ps, r) => {
            ps.iter().for_each(|e| by_value_deps(e, &mut deps));
            by_value_deps(r, &mut deps);
            deps.retain(|d| matches!(d, CTy::FnPtr(..)));
        }
        // A table holds its builder by value, an Entry its key; an
        // iterator holds neither (see `hash::struct_fields`). The
        // elements live behind the table pointer. Counting the key
        // and the `(K, V)` tuple made a false cycle for a recursive
        // `enum Any { Obj(HashMap<String, Any>) }` that left `Any`
        // incomplete inside the tuple.
        CTy::Hash(k, args) if hash::is_table(*k) => {
            if let Some(s) = args.last() {
                by_value_deps(s, &mut deps);
            }
        }
        CTy::Hash(crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::OccupiedEntry | crate::ty::hash::HashTy::VacantEntry, args) => {
            if let Some(k) = args.first() {
                by_value_deps(k, &mut deps);
            }
        }
        _ => {}
    }
    deps
}

/// The named C types the definition of `t` mentions (fields behind pointers too), for
/// `type_decls_with`'s closure.
fn field_types(p: &Program, t: &CTy) -> HashSet<CTy> {
    let mut inner = HashSet::new();
    match t {
        CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| collect_types(&cty(&p.tys, f.ty), &mut inner)),
        CTy::Option(e) => collect_types(e, &mut inner),
        CTy::Result(a, b) => {
            collect_types(a, &mut inner);
            collect_types(b, &mut inner);
        }
        CTy::Tuple(es) => es.iter().for_each(|e| collect_types(e, &mut inner)),
        CTy::Array(e, _) => collect_types(e, &mut inner),
        CTy::ArrayIter(e, n) => collect_types(&CTy::Array(e.clone(), *n), &mut inner),
        CTy::OptIter(_, e) => collect_types(&CTy::Option(e.clone()), &mut inner),
        CTy::Slice(e) => collect_types(e, &mut inner),
        CTy::Rc(e) | CTy::RefCell(e) => collect_types(e, &mut inner),
        CTy::FnPtr(ps, r) => {
            ps.iter().for_each(|e| collect_types(e, &mut inner));
            collect_types(r, &mut inner);
        }
        CTy::Hash(_, args) => {
            args.iter().for_each(|e| collect_types(e, &mut inner));
            collect_types(&hash::elem_cty(t), &mut inner);
        }
        _ => {}
    }
    inner
}

fn type_decls(p: &Program, out: &mut String, roots: &HashSet<CTy>) {
    type_decls_with(p, out, roots, &HashSet::new(), Decls::Full, &HashSet::new())
}

/// Which types `type_decls_with` defines (the rest of what it names gets a forward typedef).
/// With `blocks` (release C plain C units, `blocks_on`), an Adt that only other definitions
/// hold (not a root: no code of the unit reads its fields) is a block of its size and
/// alignment when `nested_block` allows, so the unit does not change with its fields.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Decls {
    /// Every type the roots reach, through pointers too (dev C, the statics unit).
    Full,
    /// What the roots hold by value (release C fn units).
    ByValue { blocks: bool },
    /// That, plus one step through the pointers in it (release C glue shards: a glue
    /// definition reads an `Rc`'s count block or sizes a `Box`'s pointee in place).
    OneStep { blocks: bool },
}

/// The layout of an Adt that a release C unit may declare as a block of bytes when no code
/// in the unit reads its fields (`Decls` `blocks`). Only where every C ABI passes the block
/// and the struct alike: larger than 16 bytes (in memory or by reference on x86-64 SysV,
/// Win64, AAPCS64 and wasm), and not a possible homogeneous float aggregate (AAPCS64 passes
/// up to four floats or doubles in registers: 32 bytes at most). Only the program's own
/// types: builtin code (`call_value`) writes the nested fields of std's types and of lust's
/// builtin ones (`TrySendError<T>`, an instance of a builtin template) by path.
fn nested_block(p: &Program, t: &CTy) -> Option<Layout> {
    let CTy::Adt(a) = t else { return None };
    let builtin = p.gx.adt_info.get(a.0 as usize).is_some_and(|(d, _)| d.krate == crate::ty::BUILTIN_CRATE);
    let path = p.display_path(p.adt(*a).name);
    if builtin || ["std::", "core::", "alloc::"].iter().any(|s| path.starts_with(s)) {
        return None;
    }
    let l = c_layout(p, t)?;
    (l.size > 16 && (l.size > 32 || !may_hold_float(p, t, &mut HashSet::new()))).then_some(l)
}

/// Whether a value of `t` may hold a float by value. Kinds it does not list count as yes.
fn may_hold_float(p: &Program, t: &CTy, seen: &mut HashSet<CTy>) -> bool {
    match t {
        CTy::Float(_) => true,
        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Str | CTy::String | CTy::Vec(_) | CTy::Ref(_) | CTy::Ptr(_) | CTy::FatPtr(_) => false,
        CTy::Slice(_) | CTy::Boxed(_) | CTy::Rc(_) | CTy::Weak(_) | CTy::BoxDyn | CTy::RcDyn | CTy::FnPtr(..) => false,
        _ if !seen.insert(t.clone()) => false,
        CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).any(|f| may_hold_float(p, &cty(&p.tys, f.ty), seen)),
        CTy::Tuple(es) => es.iter().any(|e| may_hold_float(p, e, seen)),
        CTy::Option(e) | CTy::Array(e, _) | CTy::Cell(e) => may_hold_float(p, e, seen),
        CTy::Result(a, b) => may_hold_float(p, a, seen) || may_hold_float(p, b, seen),
        _ => true,
    }
}

/// Release C declares an `Rc`/`Arc` count block (`RcI_T`) with no `T` in it: the two counts,
/// then the value's place as a byte array at `T`'s alignment, which this gives (release C,
/// `T`'s layout known; else the block holds `T`). Value accesses cast that place to `T`
/// (`rc_value`, `rc_ptr`), and allocations size the block from the value's offset
/// (`rc_size`), so a unit that only reads the counts or the value's address declares no `T`
/// and does not change with `T`'s size. The value's offset and the block's size and
/// alignment are the ones of the block that holds `T`, and the same texts read both.
fn rc_head(p: &Program, e: &CTy) -> Option<u64> {
    names::release().then(|| c_layout(p, e)).flatten().map(|l| l.align.max(1))
}

/// The value in the count block `b` points at (C of type `RcI_T*`), as a C lvalue of `T`:
/// either form of the block (`rc_head`). Only a read or write of it needs `T` defined.
fn rc_value(b: &str, e: &CTy) -> String {
    format!("(*{})", rc_ptr(b, e))
}

/// The address of that value, a `T*`.
fn rc_ptr(b: &str, e: &CTy) -> String {
    format!("(({}*)&({b})->v)", ctype(e))
}

/// The allocation size of count block `it` (`RcI_T`): the value's offset and `T`'s size,
/// rounded up to the block's alignment, which is the size of the block that holds `T` with
/// either form (`rc_head`). Needs `T` defined.
fn rc_size(it: &str, e: &CTy) -> String {
    format!("((__builtin_offsetof({it}, v) + sizeof({}) + _Alignof({it}) - 1) & ~(uint64_t)(_Alignof({it}) - 1))", ctype(e))
}

/// A type's forward typedefs (`type_decls_with`): what lets other declarations name it
/// before its definition.
fn decl_forward(t: &CTy, out: &mut String) {
    if let CTy::Adt(a) = t {
        let _ = writeln!(out, "typedef struct {0} {0};", names::adt(*a));
    }
    // Every struct-typed C type too: a closure env holds references
    // (`&(captures..)`, `&Result<..>`) that can sit in a type emitted
    // before the referenced type's own definition.
    if let CTy::Tuple(_) | CTy::Option(_) | CTy::Result(..) | CTy::Array(..) | CTy::Slice(_) | CTy::ArrayIter(..) | CTy::OptIter(..) = t {
        let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
    }
    match t {
        CTy::Rc(e) => {
            let _ = writeln!(out, "typedef struct RcI_{0} RcI_{0};", mangle(e));
        }
        CTy::RefCell(e) => {
            let _ = writeln!(out, "typedef struct RCL_{0} RCL_{0};", mangle(e));
        }
        CTy::Sync(k, _) if k.is_cell_struct() => {
            let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
        }
        _ => {}
    }
    if let CTy::Hash(k, _) = t
        && hash::has_struct(*k)
    {
        let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
    }
}

/// The type definitions of one pass over units of a frozen program (`with_decl_cache`): each
/// type's `decl_own` text, by type and form (in full, as a block), made once and shared by the
/// threads that make the units. A glue shard declares much the same types as the others (tsgo:
/// 118 shards, about 0.55 CPU-s of definitions a build).
#[derive(Default)]
pub struct DeclCache(std::sync::RwLock<crate::intern::FxMap<CTy, [Option<std::sync::Arc<str>>; 2]>>);

impl DeclCache {
    /// `decl_own` of `t`, from the cache when a unit of the pass made it already.
    fn decl(&self, p: &Program, t: &CTy, block: Option<Layout>, out: &mut String) {
        let form = block.is_some() as usize;
        if let Some(s) = self.0.read().unwrap_or_else(|e| e.into_inner()).get(t).and_then(|v| v[form].clone()) {
            out.push_str(&s);
            return;
        }
        let m = out.len();
        decl_own(p, t, block, out);
        self.0.write().unwrap_or_else(|e| e.into_inner()).entry(t.clone()).or_default()[form] = Some(std::sync::Arc::from(&out[m..]));
    }
}

thread_local! {
    /// The pass's `DeclCache` this thread uses (`with_decl_cache`), if any.
    static DECL_CACHE: std::cell::RefCell<Option<std::sync::Arc<DeclCache>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `f` with `cache` as this thread's type definitions (`type_decls_with`), in a codegen
/// phase (`in_layout_phase`), where the program is frozen: a definition depends on the
/// program and the type alone.
pub fn with_decl_cache<R>(cache: &std::sync::Arc<DeclCache>, f: impl FnOnce() -> R) -> R {
    struct Restore(Option<std::sync::Arc<DeclCache>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let prev = self.0.take();
            DECL_CACHE.with(|c| *c.borrow_mut() = prev);
        }
    }
    let _restore = Restore(DECL_CACHE.with(|c| c.borrow_mut().replace(cache.clone())));
    f()
}

/// One type's own definition (its block form, for `block`), after its deps (`type_decls_with`).
fn decl_own(p: &Program, t: &CTy, block: Option<Layout>, out: &mut String) {
    if let (CTy::Adt(a), Some(l)) = (t, block) {
        let an = names::adt(*a);
        let _ = writeln!(out, "/* {} */", p.display_path(p.adt(*a).name));
        let _ = writeln!(out, "struct {an} {{ _Alignas({}) uint8_t b[{}]; }};", l.align, l.size);
        layout_assert(out, &an, &l);
        return;
    }
    if let CTy::Hash(k, _) = t
        && hash::has_struct(*k)
    {
        let _ = writeln!(out, "struct {} {{ {} }};", ctype(t), hash::struct_fields(t));
        return;
    }
    match t {
        CTy::Option(e) => match c_layout(p, t) {
            Some(l) => emit_enum_decl(p, out, &format!("typedef struct {}", ctype(t)), t, &[vec![], vec![(**e).clone()]], &l),
            None => {
                let _ = writeln!(out, "typedef struct {0} {{ uint32_t tag; {1} v; }} {0};", ctype(t), ctype(e));
            }
        },
        CTy::Result(a, b) => match c_layout(p, t) {
            Some(l) => {
                emit_enum_decl(p, out, &format!("typedef struct {}", ctype(t)), t, &[vec![(**a).clone()], vec![(**b).clone()]], &l)
            }
            None => {
                let _ = writeln!(
                    out,
                    "typedef struct {0} {{ uint32_t tag; union {{ struct {{ {1} f0; }} v0; struct {{ {2} f0; }} v1; }} u; }} {0};",
                    ctype(t),
                    ctype(a),
                    ctype(b)
                );
            }
        },
        CTy::Tuple(es) => match c_layout(p, t) {
            Some(l) => {
                let ct = ctype(t);
                if es.is_empty() {
                    let _ = writeln!(out, "typedef struct {ct} {{ }} {ct};");
                } else {
                    let fields: Vec<(String, Layout, u64)> = es
                        .iter()
                        .enumerate()
                        .map(|(i, e)| (format!("{} f{i}", ctype(e)), field_layout(p, e), l.field_offsets[i]))
                        .collect();
                    let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                }
                layout_assert(out, &ct, &l);
            }
            None => {
                let fields: String = es.iter().enumerate().map(|(i, e)| format!("{} f{i}; ", ctype(e))).collect();
                let fields = if fields.is_empty() { "uint8_t unused; ".to_string() } else { fields };
                let _ = writeln!(out, "typedef struct {0} {{ {fields}}} {0};", ctype(t));
            }
        },
        CTy::Array(e, n) => match c_layout(p, t) {
            Some(l) => {
                let ct = ctype(t);
                // tcc and gcc refuse a C array longer than 2^31 - 1 even
                // when its element is zero-sized (`[(); usize::MAX]`); such
                // an array has size 0 either way, so it is declared `v[0]`.
                let n = if l.size == 0 && *n > i32::MAX as u64 { 0 } else { *n };
                let _ = writeln!(out, "typedef struct {ct} {{ {} v[{n}]; }} {ct};", ctype(e));
                layout_assert(out, &ct, &l);
            }
            None => {
                let _ = writeln!(out, "typedef struct {0} {{ {1} v[{2}]; }} {0};", ctype(t), ctype(e), (*n).max(1));
            }
        },
        CTy::ArrayIter(e, n) => {
            let at = CTy::Array(e.clone(), *n);
            let ct = ctype(t);
            match c_layout(p, t) {
                Some(l) => {
                    let es = [at.clone(), CTy::Int(IntTy::Usize), CTy::Int(IntTy::Usize)];
                    let fields: Vec<(String, Layout, u64)> = es
                        .iter()
                        .enumerate()
                        .map(|(i, e)| (format!("{} f{i}", ctype(e)), field_layout(p, e), l.field_offsets[i]))
                        .collect();
                    let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let _ = writeln!(out, "typedef struct {ct} {{ {} f0; uint64_t f1; uint64_t f2; }} {ct};", ctype(&at));
                }
            }
        },
        CTy::OptIter(_, e) => {
            let ot = CTy::Option(e.clone());
            let ct = ctype(t);
            match c_layout(p, t) {
                Some(l) => {
                    let fields = vec![(format!("{} f0", ctype(&ot)), field_layout(p, &ot), l.field_offsets[0])];
                    let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let _ = writeln!(out, "typedef struct {ct} {{ {} f0; }} {ct};", ctype(&ot));
                }
            }
        }
        CTy::Slice(e) => {
            let _ = writeln!(out, "typedef struct {0} {{ {1}* ptr; uint64_t len; }} {0};", ctype(t), ctype(e));
            if let Some(l) = c_layout(p, t) {
                layout_assert(out, &ctype(t), &l);
            }
        }
        CTy::Rc(e) => match rc_head(p, e) {
            Some(align) => {
                let _ = writeln!(out, "typedef struct RcI_{0} {{ uint64_t strong; uint64_t weak; _Alignas({align}) unsigned char v[]; }} RcI_{0};", mangle(e));
            }
            None => {
                let _ = writeln!(out, "typedef struct RcI_{0} {{ uint64_t strong; uint64_t weak; {1} v; }} RcI_{0};", mangle(e), ctype(e));
            }
        },
        CTy::RefCell(e) => {
            let _ = writeln!(out, "typedef struct RCL_{0} {{ int64_t f0; {1} f1; }} RCL_{0};", mangle(e), ctype(e));
        }
        // `Mutex<T>`: the futex word, the poison flag, the value;
        // `RwLock<T>` adds the waiter count (runtime/sync.c).
        CTy::Sync(k, e) if k.is_cell_struct() => {
            // A Mutex has no `wn`: its second word is `poison`.
            let names: &[&str] = if *k == crate::ty::sync::SyncTy::Mutex { &["st", "poison"] } else { &["st", "wn", "poison"] };
            let words: String = names.iter().zip(sync::cell_words(*k)).map(|(n, i)| format!("{} {n}; ", int_c(*i))).collect();
            let _ = writeln!(out, "struct {0} {{ {words}{1} v; }};", ctype(t), ctype(e));
        }
        CTy::FnPtr(ps, r) => {
            let ct = ctype(t);
            let large = ret_by_out(p, r);
            let mut params: Vec<String> = Vec::new();
            if large {
                params.push(format!("{}*", ctype(r)));
            }
            params.extend(ps.iter().filter(|t| !param_dropped(p, t)).map(|t| param_ctype(p, t)));
            let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
            if large {
                let _ = writeln!(out, "typedef void (*{ct})({params});");
            } else {
                let _ = writeln!(out, "typedef {} (*{ct})({params});", ctype(r));
            }
            if let Some(l) = c_layout(p, t) {
                layout_assert(out, &ct, &l);
            }
        }
        CTy::Adt(a) => {
            let adt = p.adt(*a);
            let an = names::adt(*a);
            let _ = writeln!(out, "/* {} */", p.display_path(adt.name));
            let packed = adt.repr.pack;
            if let Some(n) = packed {
                let _ = writeln!(out, "#pragma pack(push, {n})");
            }
            let layout = c_layout(p, t);
            if adt.is_enum {
                match layout {
                    Some(l) => {
                        let variants: Vec<Vec<CTy>> =
                            adt.variants.iter().map(|v| v.fields.iter().map(|f| cty(&p.tys, f.ty)).collect()).collect();
                        emit_enum_decl(p, out, &format!("struct {an}"), t, &variants, &l);
                    }
                    None => {
                        let fields = |v: &Variant| -> String {
                            v.fields.iter().enumerate().map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty)))).collect()
                        };
                        let _ = write!(out, "struct {an} {{ uint32_t tag; ");
                        if adt.variants.iter().any(|v| !v.fields.is_empty()) {
                            out.push_str("union { ");
                            for (vi, v) in adt.variants.iter().enumerate() {
                                if !v.fields.is_empty() {
                                    let _ = write!(out, "struct {{ {}}} v{vi}; ", fields(v));
                                }
                            }
                            out.push_str("} u; ");
                        }
                        out.push_str("};\n");
                    }
                }
            } else {
                match layout {
                    Some(l) => {
                        let v = &adt.variants[0];
                        if v.fields.is_empty() && l.align > 1 {
                            let _ = writeln!(out, "struct {an} {{ _Alignas({}) lust_Unit _z; }};", l.align);
                        } else if v.fields.is_empty() {
                            let _ = writeln!(out, "struct {an} {{ }};");
                        } else {
                            let fields: Vec<(String, Layout, u64)> = v
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, f)| {
                                    let ft = cty(&p.tys, f.ty);
                                    (format!("{} f{i}", ctype(&ft)), field_layout(p, &ft), l.field_offsets[i])
                                })
                                .collect();
                            let _ = writeln!(out, "struct {} {{ {}}};", an.clone(), layout_members(&fields, Some(l.size), l.align));
                        }
                        layout_assert(out, &an.clone(), &l);
                    }
                    None => {
                        let f: String = adt.variants[0]
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty))))
                            .collect();
                        let f = if f.is_empty() { "uint8_t unused; ".to_string() } else { f };
                        let _ = writeln!(out, "struct {an} {{ {f}}};");
                    }
                }
            }
            if packed.is_some() {
                out.push_str("#pragma pack(pop)\n");
            }
        }
        _ => {}
    }
}

/// Records a read of type `t` with its release name (`record::Read::Type`), when a record is
/// open.
fn read_type(t: &CTy) {
    if record::on() {
        record::read(record::Read::Type(t.clone(), mangle(t)));
    }
}

/// Records a read of type `t`'s forward typedef only (`record::Read::TypeFwd`), when a
/// record is open.
fn read_type_fwd(t: &CTy) {
    if record::on() {
        record::read(record::Read::TypeFwd(t.clone(), mangle(t)));
    }
}

/// What every release C fn unit's text reads besides its `record::Read`s (B1): the unwind
/// tables switch (the noreturn prototypes), whether the glue set is frozen (static glue), and
/// release names. The fixed texts and limits are the compiler's own (its build hash), the
/// knobs LUST_* variables (both in the driver's unit identity). A program-wide input of
/// `fn_unit_parts` that no read names goes here. Call within the release names.
pub fn unit_switches(p: &Program, g: &GlueSet) -> String {
    format!("unwind_tables={} frozen_glue={} release={}", p.unwind_tables, g.shared.is_some(), names::release())
}

/// Each live static's declaration by its symbol (`read_fp`'s `statics`), made once a build.
pub fn static_decl_map(p: &Program) -> HashMap<String, String> {
    (0..p.statics.len()).filter(|&i| p.static_live(i)).map(|i| (static_sym(p, i as u32), static_decls_for(p, &HashSet::from([i])))).collect()
}

/// The fingerprint of what a recorded read of a release C fn unit saw (B1, `record::Read`),
/// from this program, its fns' outputs and its glue set: an equal fingerprint means the read
/// sees the same now. `copy_hot`: the build's copies profile, as `fn_unit_parts`'. Call within
/// the release names (`names::with`).
pub fn read_fp(p: &Program, fns: &[FnOut], g: &GlueSet, statics: &HashMap<String, String>, copy_hot: Option<&CopyHot>, r: &record::Read) -> (u64, u64) {
    use record::Read;
    let h = |parts: &[&[u8]]| crate::driver::cache::hash128(parts, 11);
    // A read of the last build can name an Adt id this program no longer has, or has for
    // another Adt: changed, before anything lays it out.
    let known = |t: &CTy| {
        let d = format!("{t:?}");
        d.split("AdtId(").skip(1).all(|rest| {
            rest.split(')').next().and_then(|n| n.parse::<usize>().ok()).is_some_and(|n| {
                n < p.adts.len() && (p.adts[n].is_enum || !p.adts[n].variants.is_empty())
            })
        })
    };
    match r {
        Read::Type(t, _) | Read::TypeFwd(t, _) | Read::Glue(_, t) if !known(t) => return (u64::MAX, u64::MAX),
        Read::Type(t, name) | Read::TypeFwd(t, name) if mangle(t) != *name => return (u64::MAX, u64::MAX),
        _ => {}
    }
    let sorted = |mut v: Vec<String>| {
        v.sort();
        v.join("\n")
    };
    match r {
        Read::Fn(s) => match fns.get(*s) {
            None => (0, 1),
            Some(f) => {
                let types = sorted(f.types.iter().map(mangle).collect());
                let named = sorted(f.named.iter().map(mangle).collect());
                let glue = sorted(f.glue.iter().map(|(k, t)| format!("{k:?} {}", mangle(t))).collect());
                let externs: Vec<&str> = f.externs.iter().map(|e| &**e).collect();
                let tag = names::fn_tag_opt(*s as u32).unwrap_or_default();
                let flags = format!("{:?} {}", f.inline, f.error.is_some());
                let (a, b) = f.text_fp();
                let texts = [a.to_le_bytes(), b.to_le_bytes()].concat();
                h(&[&texts, externs.join("\n").as_bytes(), types.as_bytes(), named.as_bytes(), glue.as_bytes(), flags.as_bytes(), tag.as_bytes()])
            }
        },
        Read::SlotOf(id) => names::slot_of_id(id).map_or((0, 2), |s| h(&[&s.to_le_bytes()])),
        Read::Pick(s, deep) => fns.get(*s).map_or((0, 3), |f| h(&[&[inline_pick(f, *deep) as u8]])),
        // What `hot_pick` reads, but the unit's own `today` (its other reads cover that).
        Read::PickHot(s) => fns.get(*s).map_or((0, 3), |f| {
            let hot = copy_hot.filter(|_| inline_pick_hot(f));
            let frame = f.pick_info().is_some_and(|d| d.frame);
            let frame_ok = hot.is_some_and(|h| !frame || names::fn_tag_opt(*s as u32).is_some_and(|id| is_hot(&h.frames, &id)));
            let small = frame_ok && hot.is_some_and(|h| f.layout_reads().is_disjoint(&h.big));
            h(&[&[hot.is_some() as u8, frame as u8, frame_ok as u8, small as u8]])
        }),
        Read::Glue(k, t) => {
            let key = (*k, t.clone());
            let deps = g.deps.get(&key).map(|d| d.iter().map(|(a, b)| format!("{a:?} {}", mangle(b))).collect::<Vec<_>>().join("\n")).unwrap_or_default();
            let externs = g.externs.get(&key).map(|e| e.iter().cloned().collect::<Vec<_>>().join("\n")).unwrap_or_default();
            let types = g.types.get(&key).map(|v| v.iter().map(mangle).collect::<Vec<_>>().join("\n")).unwrap_or_default();
            let none = b"-".as_slice();
            h(&[
                g.protos.get(&key).map_or(none, |s| s.as_bytes()),
                g.def_map.get(&key).map_or(none, |s| s.as_bytes()),
                deps.as_bytes(),
                externs.as_bytes(),
                types.as_bytes(),
                &[g.is_shared(&key) as u8],
            ])
        }
        Read::Type(t, _) => {
            let (mut fwd, mut full, mut blk) = (String::new(), String::new(), String::new());
            decl_forward(t, &mut fwd);
            decl_own(p, t, None, &mut full);
            if let (CTy::Adt(_), Some(l)) = (t, nested_block(p, t)) {
                decl_own(p, t, Some(l), &mut blk);
            }
            let deps: Vec<String> = def_deps(p, t).iter().map(mangle).collect();
            let fields = sorted(field_types(p, t).iter().map(mangle).collect());
            let elem = if let CTy::Hash(..) = t { mangle(&hash::elem_cty(t)) } else { String::new() };
            h(&[mangle(t).as_bytes(), fwd.as_bytes(), full.as_bytes(), blk.as_bytes(), deps.join(" ").as_bytes(), fields.as_bytes(), elem.as_bytes()])
        }
        Read::TypeFwd(t, _) => {
            let mut fwd = String::new();
            decl_forward(t, &mut fwd);
            h(&[mangle(t).as_bytes(), fwd.as_bytes()])
        }
        Read::Static(sym) => h(&[statics.get(sym).map_or(b"-".as_slice(), |d| d.as_bytes())]),
        Read::Main => {
            let ret = p.main.map(|m| mangle(&cty(&p.tys, p.fn_info(m).ret))).unwrap_or_default();
            h(&[format!("{} {} {}", p.main.is_some(), p.unwind, p.unwind_tables).as_bytes(), ret.as_bytes()])
        }
        // On all cores: read it where the pool is free to run it (not from a pool job).
        Read::Statics => names::statics_content_fp(p, &g.slots),
    }
}

/// `type_decls`, plus forward declarations of `named` (release C: types the code only
/// points at). `deep` (with `ByValue`): roots defined one step deep as `OneStep` does,
/// for inline glue in a release C fn unit, which reads through pointers as a shard does. With `by_value` (release C fn units), define only what the roots hold by
/// value; a type reached only through a pointer gets its forward typedef, so a unit does
/// not change when a struct it only points at does. Glue and static data reach through
/// pointers (a drop through an `Rc` reads its count block), so their units keep the
/// whole closure. With `blocks` (`Decls`), the roots (and `deep`, for its own walk) are the
/// types whose fields the code reads: the Adts they only hold may be blocks.
fn type_decls_with(p: &Program, out: &mut String, roots: &HashSet<CTy>, named: &HashSet<CTy>, decls: Decls, deep: &HashSet<CTy>) {
    // With `open` (`blocks`), an Adt that `open` does not hold and `nested_block`
    // allows goes to `blocks`, and its fields are not walked.
    // B1 (`record`): every type whose facts a walk below reads is a read of the unit.
    let rec = record::on();
    let by_value = |roots: Vec<CTy>, open: Option<&HashSet<CTy>>, blocks: &mut HashSet<CTy>| {
        let mut defined = HashSet::new();
        let mut stack = roots;
        while let Some(t) = stack.pop() {
            if rec {
                read_type(&t);
            }
            if open.is_some_and(|o| !o.contains(&t)) && nested_block(p, &t).is_some() {
                blocks.insert(t);
            } else if defined.insert(t.clone()) {
                stack.extend(def_deps(p, &t));
                // Table code and initializers size the elements (`sizeof`).
                if let CTy::Hash(..) = t {
                    stack.push(hash::elem_cty(&t));
                }
            }
        }
        defined
    };
    // One pointer step from the roots themselves (a glue key and its recorded types): the
    // Box, `&`, Vec and Rc fields of a root point at what its glue reads in place. A struct
    // the roots hold by value is read by its own glue, through a prototype; stepping from
    // every such struct too defined the pointees of the whole by-value closure, and a glue
    // shard or a unit with inline glue recompiled for most edits of a central struct.
    // A glue definition reads the fields of its own types (`open`), and only addresses or
    // sizes the types they hold.
    let one_step = |roots: &HashSet<CTy>, open: Option<&HashSet<CTy>>, blocks: &mut HashSet<CTy>| {
        if rec {
            roots.iter().for_each(read_type);
        }
        let step: Vec<CTy> = roots.iter().flat_map(|t| field_types(p, t)).chain(roots.iter().cloned()).collect();
        by_value(step, open, blocks)
    };
    // The types declared as blocks: also in `defined`.
    let mut blocks: HashSet<CTy> = HashSet::new();
    let defined: Option<HashSet<CTy>> = match decls {
        Decls::Full => None,
        Decls::ByValue { blocks: b } | Decls::OneStep { blocks: b } => {
            let mut d = if let Decls::OneStep { .. } = decls {
                one_step(roots, b.then_some(roots), &mut blocks)
            } else {
                by_value(roots.iter().cloned().collect(), b.then_some(roots), &mut blocks)
            };
            if !deep.is_empty() {
                d.extend(one_step(deep, b.then_some(deep), &mut blocks));
            }
            // A type one walk reads stays defined in full.
            blocks.retain(|t| !d.contains(t));
            d.extend(blocks.iter().cloned());
            Some(d)
        }
    };
    // Close over field types (release C: one step out of each defined type).
    let mut wanted: HashSet<CTy> = HashSet::new();
    let mut stack: Vec<CTy> = defined.as_ref().map_or_else(|| roots.iter().cloned().collect(), |d| d.iter().chain(named).cloned().collect());
    while let Some(t) = stack.pop() {
        if !wanted.insert(t.clone()) {
            continue;
        }
        // A type no walk defines gets its forward typedef only, and that is all the unit
        // reads of it (the walks above read every type they define).
        let fwd_only = defined.as_ref().is_some_and(|d| !d.contains(&t));
        if rec {
            if fwd_only { read_type_fwd(&t) } else { read_type(&t) }
        }
        if fwd_only || blocks.contains(&t) {
            continue;
        }
        stack.extend(field_types(p, &t));
    }
    // The hash core's declarations, only in units that name a hash type
    // (see `runtime_source`).
    // B1 (`record`): each type's typedefs and definition are one piece of a recorded unit.
    if wanted.iter().any(|t| matches!(t, CTy::Hash(..))) {
        let m = out.len();
        out.push_str(&hash_decls());
        record::piece(record::Kind::Fixed, 2, &out[m..]);
    }
    let mut list: Vec<CTy> = wanted.into_iter().collect();
    list.sort_by_cached_key(mangle);
    for t in &list {
        let m = out.len();
        decl_forward(t, out);
        if rec && out.len() > m {
            record::piece(record::Kind::TypeDecl, record::key(&format!("fwd {}", mangle(t))), &out[m..]);
        }
    }
    // Each definition comes after the types it holds by value; from the pass's definitions
    // (`with_decl_cache`) in a codegen phase.
    let cache = DECL_CACHE.with(|c| c.borrow().clone()).filter(|_| phase_tag() != 0);
    fn emit(p: &Program, t: &CTy, blocks: &HashSet<CTy>, emitted: &mut HashSet<CTy>, out: &mut String, rec: bool, cache: Option<&DeclCache>) {
        if !emitted.insert(t.clone()) {
            return;
        }
        let block = if blocks.contains(t) { nested_block(p, t).filter(|_| matches!(t, CTy::Adt(_))) } else { None };
        if block.is_none() {
            for d in &def_deps(p, t) {
                emit(p, d, blocks, emitted, out, rec, cache);
            }
        }
        let m = out.len();
        match cache {
            Some(c) => c.decl(p, t, block, out),
            None => decl_own(p, t, block, out),
        }
        if rec {
            record::piece(record::Kind::TypeDecl, record::key(&mangle(t)), &out[m..]);
        }
    }
    let mut emitted = HashSet::new();
    for t in list.iter().filter(|t| defined.as_ref().is_none_or(|d| d.contains(*t))) {
        emit(p, t, &blocks, &mut emitted, out, rec, cache.as_deref());
    }
    out.push('\n');
    record::piece(record::Kind::Fixed, 3, "\n");
}

/// The body of a glue fn that returns what written impl method `f`
/// returns for `args` (the method's C arguments, comma separated),
/// called through the fn table with the large-return out pointer
/// when the method uses one (see `FnGen::call_value`).
fn written_glue_call(p: &Program, slots: &Slots, f: LocalDefId, args: &str, types: &mut Vec<CTy>) -> String {
    let callee = glue_callee(p, slots, f, types);
    let mut pre = String::new();
    let args = if args.is_empty() { String::new() } else { glue_args(p, f, &args.split(", ").collect::<Vec<_>>(), &mut pre).join(", ") };
    if ret_is_large(p, f) {
        let ret = ctype(&cty(&p.tys, p.fn_info(f).ret));
        let rest = if args.is_empty() { String::new() } else { format!(", {args}") };
        format!("{pre}  {ret} r; {callee}(&r{rest});\n  return r;\n")
    } else {
        format!("{pre}  return {callee}({args});\n")
    }
}

/// The C arguments of a call from glue (C text with fixed signatures) to written fn `f`, from
/// `args`, its value expressions in the order of the parameters its C signature keeps (not
/// `param_dropped`): one whose parameter goes by pointer (`param_by_ptr`) becomes the address
/// of a fresh copy, declared in `pre`, which goes before the call in the same block.
fn glue_args(p: &Program, f: LocalDefId, args: &[&str], pre: &mut String) -> Vec<String> {
    let ps: Vec<CTy> = p.fn_info(f).params.iter().map(|&t| cty(&p.tys, t)).filter(|t| !param_dropped(p, t)).collect();
    args.iter()
        .enumerate()
        .map(|(i, a)| match ps.get(i) {
            Some(t) if param_by_ptr(p, t) => {
                let _ = writeln!(pre, "  {} ga{i} = {a};", ctype(t));
                format!("&ga{i}")
            }
            _ => a.to_string(),
        })
        .collect()
}

/// `(CAST lust_fns[SLOT])`, the callee text for glue that calls written fn `f`. Adds the C
/// types of `f`'s signature to `types` (see `GlueSet::types`): the glue can be a static copy
/// in a unit whose own fns never name them.
fn glue_callee(p: &Program, slots: &Slots, f: LocalDefId, types: &mut Vec<CTy>) -> String {
    let info = p.fn_info(f);
    types.push(cty(&p.tys, info.ret));
    types.extend(info.params.iter().map(|&t| cty(&p.tys, t)));
    slots.callee(p, f)
}

/// Generates the prototype and definition of glue `g` for `t`. Pushes the glue keys the
/// definition calls to `more` and the extra C types it names to `types`.
#[allow(clippy::too_many_arguments)]
/// The drop glue step under panic=unwind (`lust_unw_dstep`): after a
/// call that may panic, the first exception moves into the glue's `ex`.
const UNW_DSTEP: &str = "  if (lust_unw_pending) lust_unw_dstep(&ex, &u);\n";

fn glue_def(
    p: &Program,
    slots: &Slots,
    g: &Glue,
    t: &CTy,
    protos: &mut String,
    defs: &mut String,
    more: &mut Vec<(Glue, CTy)>,
    types: &mut Vec<CTy>,
) {
    if matches!(g, Glue::Default | Glue::Clone) && c_size_align(p, t).0 == 0 && ret_by_out(p, t) {
        let (mut proto, mut def) = (String::new(), String::new());
        glue_def_value(p, slots, g, t, &mut proto, &mut def, more, types);
        zst_out_glue(g, t, &def, protos, defs);
        return;
    }
    glue_def_value(p, slots, g, t, protos, defs, more, types);
}

/// The `default` or `clone` glue of a zero-sized type that tcc cannot
/// return by value (`ret_by_out`), from its by-value definition `def`:
/// a function that writes through an out-pointer (each `return X;`
/// becomes `*o = X;`), and a macro of the glue's name, so every call
/// stays an expression.
fn zst_out_glue(g: &Glue, t: &CTy, def: &str, protos: &mut String, defs: &mut String) {
    let (m, ct) = (mangle(t), ctype(t));
    let (name, head, params, call) = match g {
        Glue::Default => (format!("default_{m}"), format!("{ct} default_{m}(void) {{"), format!("{ct} *o"), "&r_".to_string()),
        _ => (format!("clone_{m}"), format!("{ct} clone_{m}({ct} *p) {{"), format!("{ct} *o, {ct} *p"), "&r_, (p)".to_string()),
    };
    let arg = if matches!(g, Glue::Default) { "" } else { "p" };
    let _ = writeln!(protos, "void {name}_o({params});\n#define {name}({arg}) ({{ {ct} r_; {name}_o({call}); r_; }})");
    let mut body = def.replacen(&head, &format!("void {name}_o({params}) {{"), 1);
    while let Some(i) = body.find("return ") {
        let end = i + body[i..].find(';').unwrap_or(body.len() - i);
        let e = body[i + "return ".len()..end].to_string();
        body.replace_range(i..=end, &format!("{{ *o = {e}; return; }}"));
    }
    defs.push_str(&body);
}

/// `glue_def` for every glue whose value C returns directly.
#[allow(clippy::too_many_arguments)]
fn glue_def_value(
    p: &Program,
    slots: &Slots,
    g: &Glue,
    t: &CTy,
    protos: &mut String,
    defs: &mut String,
    more: &mut Vec<(Glue, CTy)>,
    types: &mut Vec<CTy>,
) {
    let m = mangle(t);
    let ct = ctype(t);
    let mut need = |g: Glue, t: &CTy| more.push((g, t.clone()));
    let mut body = String::new();
    // Discriminant reads and the Option payload access for the enum
    // shaped glue arms below (unused strings for other shapes).
    let disc_p = disc_call(p, t, "p");
    let pf = variant_field(p, t, "(*p)", 1, 0);
    // The `clonefrom` glue handles every shape itself (an owning
    // fat pointer takes the default body there).
    if matches!(g, Glue::CloneFrom) {
        clonefrom::clonefrom_glue(p, slots, t, protos, defs, &mut need, types);
        return;
    }
    // Owning fat pointers' glue (cgen/own.rs).
    if let CTy::Own(k, x) = t {
        own::own_glue_def(p, *g, *k, x, protos, defs, &mut need);
        return;
    }
    if let CTy::WeakDyn(arc) = t {
        own::weak_dyn_glue_def(*g, *arc, protos, defs);
        return;
    }
    if let CTy::WeakOwn(arc, x) = t {
        own::weak_own_glue_def(*g, *arc, x, protos, defs);
        return;
    }
    if let (Glue::Drop, CTy::DynGuard(_) | CTy::DynLock(true)) = (g, t) {
        own::dyn_guard_drop(t, protos, defs);
        return;
    }
    // The sync types' glue (cgen/sync.rs).
    if let CTy::Sync(k, e) = t {
        sync::sync_glue_def(p, *g, *k, e, protos, defs, &mut need, types);
        return;
    }
    match g {
        Glue::CloneFrom => unreachable!("clonefrom glue returns above"),
        Glue::Drop => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            match t {
                CTy::String => body.push_str("  lust_string_drop(p);\n"),
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::drop_body(p, t, &mut need)),
                CTy::Hash(k, _) if k.is_owning_iter() || k.is_drain() => body.push_str(&hash::iter_drop_body(p, t, &mut need)),
                // An occupied Entry dropped its key at `entry()`; a
                // VacantEntry owns its key until `insert`.
                CTy::Hash(crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::VacantEntry, a) => {
                    need(Glue::Drop, &a[0]);
                    let _ = writeln!(body, "  if (!p->slot) drop_{}(&p->key);", mangle(&a[0]));
                }
                CTy::Vec(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) drop_{}(&(({}*)p->ptr)[i]);", mangle(e), ctype(e));
                    }
                    // An empty Vec never allocates; its pointer is the
                    // dangling aligned address, not a heap block. A
                    // zero-sized element never allocates either, so that
                    // case is decided here, not at run time.
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        body.push_str("  if (p->cap) free(p->ptr);\n");
                    }
                }
                // Through the vtable: the drop entry (0 when none), then
                // the allocation by the size and align words.
                CTy::BoxDyn => {
                    body.push_str("  if (p->vt[0]) ((void (*)(void *))p->vt[0])(p->data);\n");
                    body.push_str(UNW_DSTEP);
                    body.push_str("  lust_dealloc(p->data, (uint64_t)(uintptr_t)p->vt[1], (uint64_t)(uintptr_t)p->vt[2]);\n");
                }
                CTy::RcDyn => {
                    // The two counts start the allocation (`RcI_T`).
                    let _ = writeln!(body, "  uint64_t *h = {};", own::counts(&CTy::Dyn, "(*p)"));
                    // The strong refs hold one implicit weak ref, as for `Rc<T>`.
                    let _ = writeln!(
                        body,
                        "  if (--h[0] == 0) {{ if (p->vt[0]) ((void (*)(void *))p->vt[0])(p->data); UNW_DSTEP if (--h[1] == 0) lust_dealloc((void *)h, {} + (uint64_t)(uintptr_t)p->vt[1], (uint64_t)(uintptr_t)p->vt[2]); }}",
                        own::counts_off(&CTy::Dyn, "(*p)")
                    );
                }
                CTy::Boxed(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(*p);", mangle(e));
                    }
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_dealloc((void*)*p, sizeof({et}), _Alignof({et}));");
                }
                CTy::BoxSlice(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) drop_{}(&p->ptr[i]);", mangle(e));
                    }
                    // An empty boxed slice holds a dangling pointer.
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_dealloc((void*)p->ptr, p->len * sizeof({et}), _Alignof({et}));");
                }
                CTy::VecIter(e) => {
                    // What `next` has not moved out yet: `front..len`,
                    // in order, then the buffer (as `vec::IntoIter`).
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->front; i < p->len; i++) drop_{}(&(({}*)p->ptr)[i]);", mangle(e), ctype(e));
                    }
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        body.push_str("  if (p->cap) free(p->ptr);\n");
                    }
                }
                CTy::VecDrain(e) => {
                    // What `next` has not moved out yet drops in
                    // order, then the tail moves down to the drain
                    // start and the Vec takes its new length (as
                    // `vec::Drain`'s drop).
                    body.push_str("  lust_Vec *dv = (lust_Vec *)p->vec;\n");
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->front; i < p->back; i++) drop_{}(&(({}*)dv->ptr)[i]);", mangle(e), ctype(e));
                    }
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        let et = ctype(e);
                        let _ = writeln!(body, "  lust_copy_small((({et}*)dv->ptr) + p->start, (({et}*)dv->ptr) + p->tail_start, p->tail_len * sizeof({et}));");
                    }
                    body.push_str("  dv->len = p->start + p->tail_len;\n");
                }
                CTy::StrDrain => {
                    // The bytes not yielded are removed: the tail
                    // moves down to the drain start.
                    body.push_str("  lust_String *dv = (lust_String *)p->vec;\n");
                    body.push_str("  lust_copy_small(dv->ptr + p->start, dv->ptr + p->tail_start, p->tail_len);\n");
                    body.push_str("  dv->len = p->start + p->tail_len;\n");
                }
                CTy::Rc(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let inner = if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        format!("drop_{}({}); ", mangle(e), rc_ptr("*p", e))
                    } else {
                        String::new()
                    };
                    // The strong refs together hold one implicit weak ref
                    // (Rust's RcInner): the header outlives the value
                    // drop while any Weak remains.
                    let _ = writeln!(body, "  if (--(*p)->strong == 0) {{ {inner}if (--(*p)->weak == 0) lust_rc_free(*p, _Alignof({it})); }}");
                }
                CTy::Weak(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let _ = writeln!(body, "  if (*p != ({it}*)~(uint64_t)0 && --(*p)->weak == 0) lust_rc_free(*p, _Alignof({it}));");
                }
                CTy::RefCell(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(&p->f1);", mangle(e));
                    }
                }
                CTy::Cell(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(p);", mangle(e));
                    }
                }
                // A guard gives its borrow back: `Ref` counts down, a
                // `RefMut` (flag -1) counts back up to 0.
                CTy::Guard(_, m) => {
                    let _ = writeln!(body, "  (*p)->f0 {}= 1;", if *m { "+" } else { "-" });
                }
                CTy::Option(e) => {
                    need(Glue::Drop, e);
                    let _ = writeln!(body, "  if ({disc_p}) drop_{}(&{pf});", mangle(e));
                }
                CTy::Result(a, b) => {
                    if needs_drop_c(p, a) {
                        need(Glue::Drop, a);
                        let f0 = variant_field(p, t, "(*p)", 0, 0);
                        let _ = writeln!(body, "  if (!{disc_p}) drop_{}(&{f0});", mangle(a));
                    }
                    if needs_drop_c(p, b) {
                        need(Glue::Drop, b);
                        let f1 = variant_field(p, t, "(*p)", 1, 0);
                        let _ = writeln!(body, "  if ({disc_p}) drop_{}(&{f1});", mangle(b));
                    }
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        if needs_drop_c(p, ft) {
                            need(Glue::Drop, ft);
                            let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(ft));
                        }
                    }
                }
                CTy::Array(e, n) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) drop_{}(&p->v[i]);", mangle(e));
                    }
                }
                // `array::IntoIter` (fx-array-iter): what `next` and
                // `next_back` have not moved out yet, `front..back` in
                // order, as core's drop runs `for _ in self {}`.
                CTy::ArrayIter(e, _) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->f1; i < p->f2; i++) drop_{}(&p->f0.v[i]);", mangle(e));
                    }
                }
                CTy::OptIter(_, e) => {
                    let ot = CTy::Option(e.clone());
                    if needs_drop_c(p, &ot) {
                        need(Glue::Drop, &ot);
                        let _ = writeln!(body, "  drop_{}(&p->f0);", mangle(&ot));
                    }
                }
                CTy::Adt(a) => {
                    // A user `Drop` impl runs before the fields drop
                    // (W-TRAITS-CORE through W-CGEN: the glue reads
                    // the instance from `Program::gx.drop_methods`).
                    if let Some(&drop_fn) = p.gx.drop_methods.get(a) {
                        // Glue has no error channel: a drop fn with an
                        // empty slot fails the C build instead.
                        if !has_generated_body(p, drop_fn) {
                            let _ = writeln!(body, "#error \"internal: drop glue calls a fn with no generated body\"");
                        }
                        let _ = writeln!(body, "  {}(p);", glue_callee(p, slots, drop_fn, types));
                        body.push_str(UNW_DSTEP);
                    }
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if needs_drop_c(p, &ft) {
                                    need(Glue::Drop, &ft);
                                    let _ = write!(body, " drop_{}(&p->u.v{vi}.f{fi});", mangle(&ft));
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if needs_drop_c(p, &ft) {
                                need(Glue::Drop, &ft);
                                let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(&ft));
                            }
                        }
                    }
                }
                _ => {}
            }
            // panic=unwind: a panicking drop leaves the rest to drop as
            // cleanup, and the glue passes the exception on at its end.
            // With unwind tables, glue whose type can reach a user Drop
            // or a dyn drop runs its drops under catch points
            // (`lust_unw_dtry`) and re-raises; other glue has no unwind code.
            if p.unwind_tables {
                body = body.replace(UNW_DSTEP, "").replace("UNW_DSTEP ", "");
                if unwind::drop_may_unwind(p, t, &mut HashSet::new()) {
                    // One frame for the whole glue (no catch per drop), or else catch points.
                    if let Some(def) = unwind::frame_glue(&m, &ct, &body) {
                        defs.push_str(&def);
                        defs.push('\n');
                        return;
                    }
                    let (text, any) = unwind::dtry_calls(&body);
                    if any {
                        body = format!("  void *ux = 0;\n{text}  if (ux) lust_unw_reraise(ux);\n");
                    }
                }
            } else if p.unwind && body.contains('(') {
                let dstep = UNW_DSTEP.trim();
                body = unwind::wrap_calls(&body.replace("UNW_DSTEP ", UNW_DSTEP.trim_start()), dstep);
                body = format!("  lust_exc ex; int32_t u = 0;\n{body}  if (u) lust_unw_resume(&ex);\n");
            } else {
                body = body.replace(UNW_DSTEP, "").replace("UNW_DSTEP ", "");
            }
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Clone => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            // A field type with a written `Clone` impl clones through
            // that impl even when it is `Copy` (rustc's derived bodies
            // call `Clone::clone` on each field).
            let written = |t: &CTy| matches!(t, CTy::Adt(a) if p.gx.glue_methods.contains_key(&(*a, p.gx.lang.clone)));
            let clone_of = |t: &CTy, e: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                if is_copy_c(p, t) && !written(t) {
                    e.to_string()
                } else {
                    need(Glue::Clone, t);
                    format!("clone_{}(&{e})", mangle(t))
                }
            };
            if let CTy::Adt(a) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*a, p.gx.lang.clone))
            {
                let call = written_glue_call(p, slots, f, "p", types);
                let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n{call}}}\n");
                return;
            }
            match t {
                CTy::String => body.push_str("  return lust_string_clone(p);\n"),
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::clone_body(p, t, &mut need)),
                CTy::Boxed(e) => {
                    let et = ctype(e);
                    let c = clone_of(e, "(**p)", &mut need);
                    let _ = writeln!(body, "  {et} *r = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *r = {c}; return r;");
                }
                CTy::RcDyn => {
                    let _ = writeln!(body, "  {}[0]++; return *p;", own::counts(&CTy::Dyn, "(*p)"));
                }
                CTy::BoxSlice(e) => {
                    let et = ctype(e);
                    let c = clone_of(e, "p->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  {ct} r; r.len = p->len; r.ptr = ({et}*)lust_alloc(p->len * sizeof({et}), _Alignof({et}));\n  for (uint64_t i = 0; i < p->len; i++) r.ptr[i] = {c};\n  return r;"
                    );
                }
                CTy::Rc(_) => {
                    body.push_str("  (*p)->strong++; return *p;\n");
                }
                CTy::Weak(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let _ = writeln!(body, "  if (*p != ({it}*)~(uint64_t)0) (*p)->weak++; return *p;");
                }
                // `Cell<T>: Clone` needs `T: Copy`: a copy of the value.
                CTy::Cell(_) => body.push_str("  return *p;\n"),
                // `RefCell::clone` borrows (and panics as `borrow` does).
                CTy::RefCell(e) => {
                    let c = clone_of(e, "p->f1", &mut need);
                    let _ = writeln!(
                        body,
                        "  if (p->f0 < 0) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", 0);\n  {ct} r; r.f0 = 0; r.f1 = {c}; return r;"
                    );
                }
                CTy::Option(e) => {
                    let c = clone_of(e, &pf, &mut need);
                    let rf = variant_field(p, t, "r", 1, 0);
                    let _ = writeln!(body, "  {ct} r = *p;\n  if ({disc_p}) {rf} = {c};\n  return r;");
                }
                CTy::Result(a, b) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, a) {
                        let c = clone_of(a, &variant_field(p, t, "(*p)", 0, 0), &mut need);
                        let rf = variant_field(p, t, "r", 0, 0);
                        let _ = writeln!(body, "  if (!{disc_p}) {rf} = {c};");
                    }
                    if !is_copy_c(p, b) {
                        let c = clone_of(b, &variant_field(p, t, "(*p)", 1, 0), &mut need);
                        let rf = variant_field(p, t, "r", 1, 0);
                        let _ = writeln!(body, "  if ({disc_p}) {rf} = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Tuple(es) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    for (fi, ft) in es.iter().enumerate() {
                        if !is_copy_c(p, ft) {
                            let c = clone_of(ft, &format!("p->f{fi}"), &mut need);
                            let _ = writeln!(body, "  r.f{fi} = {c};");
                        }
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Array(e, n) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, e) {
                        let c = clone_of(e, "p->v[i]", &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) r.v[i] = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                // `array::IntoIter`'s Clone clones only the elements
                // it still owns; the moved-out slots keep stale bytes
                // the clone's own range never drops.
                // core's derived Clone of `option::IntoIter` and
                // `result::IntoIter`: a clone of the stored Option.
                CTy::OptIter(_, e) => {
                    let ot = CTy::Option(e.clone());
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, &ot) || written(e) {
                        let c = clone_of(&ot, "p->f0", &mut need);
                        let _ = writeln!(body, "  r.f0 = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                CTy::ArrayIter(e, _) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, e) || written(e) {
                        let c = clone_of(e, "p->f0.v[i]", &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = p->f1; i < p->f2; i++) r.f0.v[i] = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                // `vec::IntoIter::clone`: std's `as_slice().to_vec()` into
                // a new IntoIter, so only `front..len` is cloned, into a
                // fresh buffer of exactly that length.
                CTy::VecIter(e) => {
                    let et = ctype(e);
                    let c = clone_of(e, &format!("(({et}*)p->ptr)[p->front + i]"), &mut need);
                    let _ = writeln!(
                        body,
                        "  uint64_t n = p->len - p->front;\n  lust_Vec v = lust_vec_with_capacity(n, sizeof({et}), _Alignof({et}));\n  for (uint64_t i = 0; i < n; i++) (({et}*)v.ptr)[i] = {c};\n  lust_VecIter r; r.ptr = v.ptr; r.len = n; r.cap = v.cap; r.front = 0;\n  return r;"
                    );
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_Vec r = lust_vec_with_capacity(p->len, sizeof({et}), _Alignof({et}));");
                    if is_copy_c(p, e) && !written(e) {
                        // std's TrivialClone path: one byte copy, free for
                        // zero-sized elements.
                        let _ = writeln!(body, "  lust_copy_small(r.ptr, p->ptr, p->len * sizeof({et}));\n  r.len = p->len;\n  return r;");
                    } else {
                        let c = clone_of(e, &format!("(({et}*)p->ptr)[i]"), &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) (({et}*)r.ptr)[i] = {c};\n  r.len = p->len;\n  return r;");
                    }
                }
                // `MaybeUninit::clone` is a byte copy in core
                // (no clone of the possibly-uninit value).
                CTy::Adt(a) if p.def_of_adt(*a) == crate::ty::maybe_uninit_def() => {
                    body.push_str("  return *p;\n");
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if !is_copy_c(p, &ft) {
                                    let c = clone_of(&ft, &format!("p->u.v{vi}.f{fi}"), &mut need);
                                    let _ = write!(body, " r.u.v{vi}.f{fi} = {c};");
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if !is_copy_c(p, &ft) {
                                let c = clone_of(&ft, &format!("p->f{fi}"), &mut need);
                                let _ = writeln!(body, "  r.f{fi} = {c};");
                            }
                        }
                    }
                    body.push_str("  return r;\n");
                }
                _ => body.push_str("  return *p;\n"),
            }
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Eq => {
            let _ = writeln!(protos, "uint8_t eq_{m}({ct} *a, {ct} *b);");
            if let CTy::Adt(adt_id) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*adt_id, p.gx.lang.partial_eq))
            {
                let call = written_glue_call(p, slots, f, "a, b", types);
                let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{call}}}\n");
                return;
            }
            // An unsized newtype's `&self` is its fat value (W-SHIM).
            if let CTy::Unsized(adt_id, _) = t {
                let f = p.gx.glue_methods.get(&(*adt_id, p.gx.lang.partial_eq)).copied().expect("an unsized newtype compared by == has a written PartialEq");
                let call = written_glue_call(p, slots, f, "*a, *b", types);
                let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{call}}}\n");
                return;
            }
            let eq_of = |t: &CTy, x: &str, y: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit | CTy::AccessError => "1".into(),
                    CTy::Int(i) if is128(*i) => format!("(({x}).lo == ({y}).lo && ({x}).hi == ({y}).hi)"),
                    CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) | CTy::FnPtr(..) | CTy::ExitCode | CTy::Ptr(_) => format!("({x} == {y})"),
                    // A fat raw pointer: address and metadata (check
                    // rejects `==` on dyn pointers, whose vtable addresses
                    // rustc does not fix).
                    CTy::FatPtr(e) if **e == CTy::Dyn => format!("(({x}).data == ({y}).data && ({x}).vt == ({y}).vt)"),
                    CTy::FatPtr(_) => format!("((void*)({x}).ptr == (void*)({y}).ptr && ({x}).len == ({y}).len)"),
                    _ => {
                        need(Glue::Eq, t);
                        format!("eq_{}(&{x}, &{y})", mangle(t))
                    }
                }
            };
            let cow = (fmt::cow_view(p, t, "a", "va"), fmt::cow_view(p, t, "b", "vb"));
            match t {
                CTy::ExitCode => body.push_str("  return *a == *b;\n"),
                CTy::AccessError => body.push_str("  return 1;\n"),
                // HashMap and HashSet (W-STD-B, cgen/hash.rs).
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::table_eq_body(p, t, &mut need)),
                // `Cow<B>` compares the `B` views (W-STD-B).
                _ if cow.0.is_some() => {
                    let ((rb, da), (_, db)) = (cow.0.clone().unwrap(), cow.1.clone().unwrap());
                    let c = eq_of(&rb, "va", "vb", &mut need);
                    let _ = writeln!(body, "  {da}\n  {db}\n  return {c};");
                }
                // A fat raw pointer: address and metadata (tf-fatptr).
                CTy::FatPtr(_) => {
                    let c = eq_of(t, "(*a)", "(*b)", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                CTy::String => body.push_str("  return lust_str_eq(lust_string_as_str(a), lust_string_as_str(b));\n"),
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  return lust_str_eq(*a, *b);\n"),
                CTy::Option(e) => {
                    let (af, bf) = (variant_field(p, t, "(*a)", 1, 0), variant_field(p, t, "(*b)", 1, 0));
                    let c = eq_of(e, &af, &bf, &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  return {da} == {db} && (!{da} || {c});");
                }
                CTy::Result(x, y) => {
                    let ca = eq_of(x, &variant_field(p, t, "(*a)", 0, 0), &variant_field(p, t, "(*b)", 0, 0), &mut need);
                    let cb = eq_of(y, &variant_field(p, t, "(*a)", 1, 0), &variant_field(p, t, "(*b)", 1, 0), &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  return {da} == {db} && ({da} ? {cb} : {ca});");
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        let c = eq_of(ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                        let _ = writeln!(body, "  if (!{c}) return 0;");
                    }
                    body.push_str("  return 1;\n");
                }
                CTy::Array(e, n) => {
                    let c = eq_of(e, "a->v[i]", "b->v[i]", &mut need);
                    let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) if (!{c}) return 0;\n  return 1;");
                }
                CTy::Slice(e) | CTy::BoxSlice(e) => {
                    let c = eq_of(e, "a->ptr[i]", "b->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
                }
                CTy::Ref(inner) | CTy::Boxed(inner) => {
                    let e = eq_of(inner, "(**a)", "(**b)", &mut need);
                    let _ = writeln!(body, "  return {e};");
                }
                CTy::Rc(inner) => {
                    let e = eq_of(inner, &rc_value("*a", inner), &rc_value("*b", inner), &mut need);
                    let _ = writeln!(body, "  return {e};");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let c = eq_of(e, &format!("(({et}*)a->ptr)[i]"), &format!("(({et}*)b->ptr)[i]"), &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
                }
                // An enum with no fields: equal discriminants (no switch over the variants).
                CTy::Adt(_) if fieldless_enum(p, t) => {
                    let _ = writeln!(body, "  return {} == {};", disc_call(p, t, "a"), disc_call(p, t, "b"));
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                        let _ = writeln!(body, "  if ({da} != {db}) return 0;\n  switch ({da}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                let c = eq_of(&ft, &format!("a->u.v{vi}.f{fi}"), &format!("b->u.v{vi}.f{fi}"), &mut need);
                                let _ = write!(body, " if (!{c}) return 0;");
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n  return 1;\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            let c = eq_of(&ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                            let _ = writeln!(body, "  if (!{c}) return 0;");
                        }
                        body.push_str("  return 1;\n");
                    }
                }
                _ => body.push_str("  return *a == *b;\n"),
            }
            let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
        }
        Glue::Cmp | Glue::PCmp => {
            // `PCmp` is this same body with `PartialOrd` order:
            // a written `partial_cmp` from `pcmp_methods` (an `Ord`
            // impl may also exist) and `PCmp` field compares, except
            // where a derive rule below sends fields to `Ord`.
            let partial = *g == Glue::PCmp;
            let pre = if partial { "pcmp" } else { "cmp" };
            let _ = writeln!(protos, "int8_t {pre}_{m}({ct} *a, {ct} *b);");
            // A written `partial_cmp` (see `glue_methods`): its
            // `Option<Ordering>` becomes the glue's code.
            let written = if partial { p.gx.pcmp_methods.as_map() } else { p.gx.glue_methods.as_map() };
            if let CTy::Adt(adt_id) | CTy::Unsized(adt_id, _) = t
                && let Some(&f) = written.get(&(*adt_id, p.gx.lang.partial_ord))
                && let Some(ord) = p.tys.local_adt_of(crate::check::generics::ordering_def())
            {
                // An unsized newtype's `&self` is its fat value (W-SHIM).
                let (a, b) = if matches!(t, CTy::Unsized(..)) { ("*a", "*b") } else { ("a", "b") };
                let opt = CTy::Option(Box::new(CTy::Adt(ord)));
                let callee = glue_callee(p, slots, f, types);
                let ot = ctype(&opt);
                let (a, b) = match &glue_args(p, f, &[a, b], &mut body)[..] {
                    [a, b] => (a.clone(), b.clone()),
                    _ => unreachable!("two arguments"),
                };
                if ret_is_large(p, f) {
                    let _ = writeln!(body, "  {ot} r; {callee}(&r, {a}, {b});");
                } else {
                    let _ = writeln!(body, "  {ot} r = {callee}({a}, {b});");
                }
                let some = disc_call(p, &opt, "(&r)");
                let pay = variant_field(p, &opt, "r", 1, 0);
                let ord_ct = ctype(&CTy::Adt(ord));
                let idx = disc_call(p, &CTy::Adt(ord), "(&o)");
                let _ = writeln!(body, "  if (!{some}) return 2;\n  {ord_ct} o = {pay};\n  return (int8_t)((int)({idx}) - 1);");
                let _ = writeln!(defs, "int8_t {pre}_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
                return;
            }
            // rustc's derived `partial_cmp` on a non-generic type
            // that also derives `Ord` is `Some(self.cmp(other))`
            // (collect.rs `glue_cmp_mode`): the `PCmp` glue of such
            // a type is its `Cmp` glue, field `Ord` compares included.
            if partial
                && let CTy::Adt(adt_id) = t
                && p.derives_of(*adt_id).partial_ord
                && p.derives_of(*adt_id).ord
                && !p.gx.adt_instance_of.get(adt_id.0 as usize).is_some_and(|o| o.is_some())
                && !p.gx.adt_generics.get(adt_id.0 as usize).is_some_and(|g| !g.params.is_empty())
            {
                need(Glue::Cmp, t);
                let _ = writeln!(defs, "int8_t pcmp_{m}({ct} *a, {ct} *b) {{\n  return cmp_{m}(a, b);\n}}\n");
                return;
            }
            // One field pair `x`, `y` (C lvalues): scalars inline, the
            // rest through their own glue.
            let cmp_of = |t: &CTy, x: &str, y: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit => "0".into(),
                    CTy::Int(i) if is128(*i) => {
                        let f = int_fn(*i);
                        format!("((int8_t)((lust_{f}_cmp({x}, {y}) > 0) - (lust_{f}_cmp({x}, {y}) < 0)))")
                    }
                    CTy::Bool | CTy::Char | CTy::Int(_) => format!("((int8_t)(({x}) < ({y}) ? -1 : ({x}) > ({y})))"),
                    // Raw pointers order by address (w-cinterop).
                    CTy::Ptr(_) => format!("((int8_t)(((uintptr_t)({x})) < ((uintptr_t)({y})) ? -1 : ((uintptr_t)({x})) > ((uintptr_t)({y}))))"),
                    CTy::Float(_) => format!("((int8_t)(({x}) < ({y}) ? -1 : ({x}) > ({y}) ? 1 : ({x}) == ({y}) ? 0 : 2))"),
                    _ => {
                        need(if partial { Glue::PCmp } else { Glue::Cmp }, t);
                        format!("{pre}_{}(&{x}, &{y})", mangle(t))
                    }
                }
            };
            // Elements in order; the first one that is not equal (or
            // is unordered) decides. `len` compares last, as slices do.
            let seq = |e: &CTy, x: &str, y: &str, n: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                let c = cmp_of(e, x, y, need);
                format!("  for (uint64_t i = 0; i < {n}; i++) {{ int8_t c = {c}; if (c) return c; }}\n")
            };
            let cow = (fmt::cow_view(p, t, "a", "va"), fmt::cow_view(p, t, "b", "vb"));
            match t {
                // std's `Reverse<T>` orders its `T` with the operands
                // swapped, as its written methods do (library/core/src/cmp.rs).
                CTy::Adt(adt_id) if p.is_reverse_adt(*adt_id) => {
                    let ft = cty(&p.tys, p.adt(*adt_id).variants[0].fields[0].ty);
                    let c = cmp_of(&ft, "b->f0", "a->f0", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                // `Cow<B>` orders the `B` views (W-STD-B).
                _ if cow.0.is_some() => {
                    let ((rb, da), (_, db)) = (cow.0.clone().unwrap(), cow.1.clone().unwrap());
                    let c = cmp_of(&rb, "va", "vb", &mut need);
                    let _ = writeln!(body, "  {da}\n  {db}\n  return {c};");
                }
                CTy::String => body.push_str("  int c = lust_str_cmp(lust_string_as_str(a), lust_string_as_str(b));\n  return c < 0 ? -1 : c > 0;\n"),
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  int c = lust_str_cmp(*a, *b);\n  return c < 0 ? -1 : c > 0;\n"),
                CTy::Option(e) => {
                    let (af, bf) = (variant_field(p, t, "(*a)", 1, 0), variant_field(p, t, "(*b)", 1, 0));
                    let c = cmp_of(e, &af, &bf, &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;\n  if (!{da}) return 0;\n  return {c};");
                }
                CTy::Result(x, y) => {
                    let ca = cmp_of(x, &variant_field(p, t, "(*a)", 0, 0), &variant_field(p, t, "(*b)", 0, 0), &mut need);
                    let cb = cmp_of(y, &variant_field(p, t, "(*a)", 1, 0), &variant_field(p, t, "(*b)", 1, 0), &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;\n  return {da} ? {cb} : {ca};");
                }
                CTy::Tuple(es) => {
                    body.push_str("  int8_t c;\n");
                    for (fi, ft) in es.iter().enumerate() {
                        let c = cmp_of(ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                        let _ = writeln!(body, "  c = {c}; if (c) return c;");
                    }
                    body.push_str("  return 0;\n");
                }
                CTy::Array(e, n) => {
                    body.push_str(&seq(e, "a->v[i]", "b->v[i]", &n.to_string(), &mut need));
                    body.push_str("  return 0;\n");
                }
                // A `Box<[T]>` orders as its slice (same fat form).
                CTy::Slice(e) | CTy::BoxSlice(e) => {
                    body.push_str("  uint64_t n = a->len < b->len ? a->len : b->len;\n");
                    body.push_str(&seq(e, "a->ptr[i]", "b->ptr[i]", "n", &mut need));
                    body.push_str("  return a->len < b->len ? -1 : a->len > b->len;\n");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    body.push_str("  uint64_t n = a->len < b->len ? a->len : b->len;\n");
                    body.push_str(&seq(e, &format!("(({et}*)a->ptr)[i]"), &format!("(({et}*)b->ptr)[i]"), "n", &mut need));
                    body.push_str("  return a->len < b->len ? -1 : a->len > b->len;\n");
                }
                CTy::Ref(inner) | CTy::Boxed(inner) => {
                    let c = cmp_of(inner, "(**a)", "(**b)", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                CTy::Rc(inner) => {
                    let c = cmp_of(inner, &rc_value("*a", inner), &rc_value("*b", inner), &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                CTy::Adt(adt_id) => {
                    let adt = p.adt(*adt_id);
                    let fields_cmp = |body: &mut String, v: &Variant, pre: &str, need: &mut dyn FnMut(Glue, &CTy)| {
                        for (fi, f) in v.fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            let c = cmp_of(&ft, &format!("a->{pre}f{fi}"), &format!("b->{pre}f{fi}"), need);
                            let _ = write!(body, " c = {c}; if (c) return c;");
                        }
                    };
                    body.push_str("  int8_t c;\n");
                    if adt.is_enum {
                        // Variants order by discriminant value, then
                        // fields (derived `PartialOrd`). `rk` maps a
                        // variant index to its rank when the values
                        // are not increasing in variant order.
                        let discs: Vec<i128> = adt.variants.iter().map(|v| v.disc).collect();
                        let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                        if discs.windows(2).all(|w| w[0] < w[1]) {
                            let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;");
                        } else {
                            let mut order: Vec<usize> = (0..discs.len()).collect();
                            order.sort_by_key(|&i| discs[i]);
                            let mut rank = vec![0usize; discs.len()];
                            for (r, &i) in order.iter().enumerate() {
                                rank[i] = r;
                            }
                            let list: Vec<String> = rank.iter().map(|r| r.to_string()).collect();
                            let _ = writeln!(body, "  static const uint32_t rk[] = {{ {} }};", list.join(", "));
                            let _ = writeln!(body, "  if ({da} != {db}) return rk[{da}] < rk[{db}] ? -1 : 1;");
                        }
                        let _ = writeln!(body, "  switch ({da}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            fields_cmp(&mut body, v, &format!("u.v{vi}."), &mut need);
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n  return 0;\n");
                    } else {
                        fields_cmp(&mut body, &adt.variants[0], "", &mut need);
                        body.push_str("\n  return 0;\n");
                    }
                }
                _ => {
                    let c = cmp_of(t, "(*a)", "(*b)", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
            }
            let _ = writeln!(defs, "int8_t {pre}_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
        }
        Glue::Default => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            if let CTy::Adt(a) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*a, p.gx.lang.default))
            {
                let call = written_glue_call(p, slots, f, "", types);
                let _ = writeln!(defs, "{ct} default_{m}(void) {{\n{call}}}\n");
                return;
            }
            // A written `impl Default for &'static A` (check
            // `collect::ref_default`).
            if let CTy::Ref(inner) = t
                && let CTy::Adt(a) = &**inner
                && let Some(&f) = p.gx.ref_default_methods.get(a)
            {
                let call = written_glue_call(p, slots, f, "", types);
                let _ = writeln!(defs, "{ct} default_{m}(void) {{\n{call}}}\n");
                return;
            }
            let def_of = |t: &CTy, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(p, t),
                    _ => {
                        need(Glue::Default, t);
                        format!("default_{}()", mangle(t))
                    }
                }
            };
            match t {
                CTy::Hash(..) => body.push_str(&hash::default_body(p, t, &mut need)),
                CTy::String => body.push_str("  return lust_string_new();\n"),
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  return lust_vec_with_capacity(0, sizeof({et}), _Alignof({et}));");
                }
                // alloc's `IntoIter::default()`: the iterator of an empty Vec.
                CTy::VecIter(e) => {
                    let et = ctype(e);
                    let _ = writeln!(
                        body,
                        "  lust_Vec v = lust_vec_with_capacity(0, sizeof({et}), _Alignof({et}));\n  lust_VecIter r; r.ptr = v.ptr; r.len = 0; r.cap = v.cap; r.front = 0;\n  return r;"
                    );
                }
                CTy::Option(_) => {
                    let _ = writeln!(body, "  return {};", variant_lit(p, t, 0, &[]));
                }
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  return ((lust_str){(uint8_t*)\"\", 0});\n"),
                // An empty slice view, or alloc's empty `Box<[T]>`:
                // a dangling aligned pointer at length 0 (the drop
                // glue frees nothing at size 0).
                CTy::Slice(e) | CTy::BoxSlice(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  {ct} r; r.ptr = ({et}*)(uintptr_t)_Alignof({et}); r.len = 0;\n  return r;");
                }
                CTy::Tuple(es) => {
                    let vals: Vec<String> = es.iter().enumerate().map(|(i, e)| format!(".f{i} = {}", def_of(e, &mut need))).collect();
                    let _ = writeln!(body, "  return (({ct}){{ {} }});", vals.join(", "));
                }
                CTy::Array(e, n) => {
                    if *n == 0 {
                        let _ = writeln!(body, "  return {};", zero_lit(p, t));
                    } else {
                        let d = def_of(e, &mut need);
                        let _ = writeln!(body, "  {ct} r;\n  for (uint64_t i = 0; i < {n}; i++) r.v[i] = {d};\n  return r;");
                    }
                }
                CTy::Boxed(e) => {
                    let et = ctype(e);
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {et} *r = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *r = {d};\n  return r;");
                }
                // An unborrowed RefCell around `T::default()`; a Cell is
                // its value in C (W-STD-B).
                CTy::RefCell(e) => {
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {ct} r; r.f0 = 0; r.f1 = {d};\n  return r;");
                }
                CTy::Cell(e) => {
                    let _ = writeln!(body, "  return {};", def_of(e, &mut need));
                }
                // alloc's `Weak::default()` is `Weak::new()`: the dangling pointer.
                CTy::Weak(_) => body.push_str("  return (void*)~(uint64_t)0;\n"),
                CTy::Rc(e) => {
                    // The header as `Rc::new` builds it: one implicit weak ref.
                    let it = format!("RcI_{}", mangle(e));
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {it} *r = ({it}*)lust_alloc({}, _Alignof({it})); r->strong = 1; r->weak = 1; {} = {d};\n  return r;", rc_size(&it, e), rc_value("r", e));
                }
                // `Cow<B>` defaults to `Owned(Owned::default())`.
                CTy::Adt(adt_id) if p.gx.adt_instance_of.get(adt_id.0 as usize).copied().flatten().is_some_and(|(d, _)| d == crate::check::generics::cow_def()) => {
                    let owned = cty(&p.tys, p.adt(*adt_id).variants[1].fields[0].ty);
                    let d = def_of(&owned, &mut need);
                    let _ = writeln!(body, "  return {};", variant_lit(p, t, 1, &[d]));
                }
                CTy::Adt(adt_id) => {
                    let adt = p.adt(*adt_id);
                    if adt.is_enum {
                        let vi = p.derives_of(*adt_id).default_variant.unwrap_or(0) as usize;
                        let _ = writeln!(body, "  return {};", variant_lit(p, t, vi, &[]));
                    } else if adt.variants[0].fields.is_empty() {
                        let _ = writeln!(body, "  return {};", zero_lit(p, t));
                    } else {
                        let vals: Vec<String> = adt.variants[0]
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, f)| format!(".f{i} = {}", def_of(&cty(&p.tys, f.ty), &mut need)))
                            .collect();
                        let _ = writeln!(body, "  return (({ct}){{ {} }});", vals.join(", "));
                    }
                }
                _ => {
                    let _ = writeln!(body, "  return {};", def_of(t, &mut need));
                }
            }
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n{body}}}\n");
        }
        Glue::TlsInit | Glue::TlsDtor => tls_glue(p, g, t, protos, defs, &mut need),
        Glue::Debug => {
            let _ = writeln!(protos, "int dbg_{m}(lust_Formatter *f, {ct} *p);");
            let body = fmt::debug_glue_body(p, t, slots, &mut need, types);
            let _ = writeln!(defs, "int dbg_{m}(lust_Formatter *f, {ct} *p) {{\n{body}}}\n");
        }
        Glue::Display => {
            let _ = writeln!(protos, "int disp_{m}(lust_Formatter *f, {ct} *p);");
            let body = fmt::display_glue_body(p, t, slots, &mut need, types);
            let _ = writeln!(defs, "int disp_{m}(lust_Formatter *f, {ct} *p) {{\n{body}}}\n");
        }
        Glue::HashValue
        | Glue::HashKey
        | Glue::HashOf
        | Glue::HashEq
        | Glue::HashClone
        | Glue::HashKeyQ
        | Glue::HashEqQ
        | Glue::HashEqEntry
        | Glue::HashDrop
        | Glue::HashOne => {
            types.extend(hash::glue_hasher(p, g, t));
            // A glue body that hashes through `Hasher::write` (a
            // `str` or byte key) declares a `&[u8]` local; its slice
            // type is in no signature the unit otherwise needs.
            types.extend([CTy::Slice(Box::new(CTy::Int(crate::ty::IntTy::U8)))]);
            let (sig, body) = hash::glue(p, slots, g, t, &mut need);
            let _ = writeln!(protos, "{sig};");
            let _ = writeln!(defs, "{sig} {{\n{body}}}\n");
        }
    }
}

fn place_mentions(p: &Place, l: Local) -> bool {
    p.local == l || p.proj.iter().any(|x| matches!(x, Proj::Index(i) if *i == l))
}

fn operand_mentions(o: &Operand, l: Local) -> bool {
    matches!(o, Operand::Copy(p) | Operand::Move(p) if place_mentions(p, l))
}

fn rvalue_mentions(rv: &Rvalue, l: Local) -> bool {
    let (mut op_hit, mut pl_hit) = (false, false);
    visit_rvalue_reads(rv, &mut |o| op_hit |= operand_mentions(o, l), &mut |p| pl_hit |= place_mentions(p, l));
    op_hit || pl_hit
}


#[cfg(test)]
mod tests {
    use super::*;

    /// A cold fn's cleanup goes out of line past `COLD_FRAME_INLINE` (flags plus one, times
    /// the nonzero ladder stores), in its prototype and its definition; under it, as it was.
    #[test]
    fn cold_cleanup_moves_a_costly_frame_out_of_line() {
        let id = "00000000000000aa";
        let fn_with = |flags: usize, points: usize| {
            let members: String = (0..flags).map(|k| format!("  uint8_t d{k};\n")).collect();
            let stores: String = (1..=points).map(|k| format!("  L.st = {k};\n  f_00000000000000bb();\n")).collect();
            format!(
                "struct fr{id} {{\n  int32_t st;\n{members}}};\nstatic inline __attribute__((always_inline)) void cl{id}(struct fr{id} *Lc);\n/* f */\nvoid f_{id}(void) {{\n  L.st = 0;\n{stores}  L.st = 0;\n  return;\n}}\nstatic inline __attribute__((always_inline)) void cl{id}(struct fr{id} *Lc) {{\n}}\n"
            )
        };
        let small = fn_with(3, 100);
        assert_eq!(cold_cleanup(&small, id), small);
        let big = fn_with(99, 401);
        let out = cold_cleanup(&big, id);
        assert_eq!(out.matches(&format!("static void cl{id}(")).count(), 2);
        assert!(!out.contains("always_inline)) void cl"));
        assert_eq!(out.replace(&format!("static void cl{id}("), &format!("static inline __attribute__((always_inline)) void cl{id}(")), big);
    }

    /// A copy's code size counts the head and the blocks, not the declarations and kconst
    /// setup before `bb0:;`, nor a block that only jumps; a jump that ends a block counts.
    #[test]
    fn code_len_counts_what_makes_instructions() {
        let head = "uint32_t f_0000000000000001(uint32_t p1)";
        let blocks = "bb0:;\n  l1 = p1;\n  if (l1) goto bb1; else goto bb2;\nbb1:;\n  goto bb3;\nbb2:;\n  l1 = 7;\n  goto bb3;\nbb3:;\n  return l1;\n}\n";
        let def = format!("{head} {{\n  uint32_t l1;\n  static int32_t lks_ok;\n  if (!lks_ok) {{\n    lks_ok = 1;\n  }}\n{blocks}");
        let jump_only = "bb1:;\n  goto bb3;\n".len();
        assert_eq!(code_len(&def, head), head.len() + blocks.len() - jump_only);
        let code = format!("/* f */\n{def}");
        let d = plain_fn_def(&code).expect("plain");
        assert_eq!((d.len, d.code), (def.len(), code_len(&def, head)));
        assert!(d.statics);
        // No blocks (no `bb0:;`): all of it.
        assert_eq!(code_len("void f(void) {\n}\n", "void f(void)"), "void f(void) {\n}\n".len());
    }

    /// A fn with an unwind cleanup frame is copyable by a hot copy only: the copy takes the
    /// frame's struct, cleanup prototype and wrapper before it, and the `#undef`s and the
    /// cleanup fn after it, not the trampoline that follows.
    #[test]
    fn a_hot_copy_takes_a_cleanup_frame_along() {
        let id = "1234567890abcdef";
        let pre = format!(
            "struct fr{id} {{\n  int32_t st;\n  T *pl2;\n  uint8_t d2;\n}};\nstatic inline __attribute__((always_inline)) void cl{id}(struct fr{id} *Lc);\nstatic inline __attribute__((always_inline)) void clw{id}(struct fr{id} *Lc) {{ if (__builtin_expect(Lc->st != 0, 0)) cl{id}(Lc); }}\n"
        );
        let def = format!(
            "lust_Unit f_{id}(T* p1, T* p2) {{\n  lust_Unit l0;\n  struct fr{id} L __attribute__((cleanup(clw{id})));\n  L.st = 0;\n  L.pl2 = &(*p2);\n  L.d2 = 1;\n#define d2 (L.d2)\nbb0:;\n  d2 = 0;\n  l0 = ((lust_Unit){{}});\n  L.st = 0;\n  return l0;\n}}\n"
        );
        let post = format!(
            "#undef l2\n#undef d2\nstatic inline __attribute__((always_inline)) void cl{id}(struct fr{id} *Lc) {{\n#define l2 (*Lc->pl2)\n#define d2 (Lc->d2)\n  switch (Lc->st) {{\n  case 0: return;\n  default: return;\n  }}\n}}\n#undef l2\n#undef d2\n"
        );
        let code = format!("{pre}/* push */\n{def}{post}lust_Unit tramp_{id}(T* p1, T* p2) {{ return f_{id}(p1, p2); }}\n");
        let d = plain_fn_def(&code).expect("a frame fn is plain for a hot copy");
        assert_eq!((d.def, d.frame), (def.as_str(), Some((pre.as_str(), post.as_str()))));
        // Another attribute in the definition still refuses it.
        let cold = code.replace("  d2 = 0;\n", "  d2 = 0;\n  __attribute__((unused)) int x;\n");
        assert!(plain_fn_def(&cold).is_none());
        // The default copy rule never takes a frame.
        let f = FnOut { text: CText::Plain(code), ..Default::default() };
        assert!(!inline_pick(&f, false) && inline_pick_hot(&f));
    }

    /// A fn's layout reads: the ADTs it reads by byte offset (through a pointer local or
    /// parameter, or a nested `T**` read) or holds by value, not one it only points to.
    #[test]
    fn layout_reads_are_offset_reads_and_values() {
        let (a, b, c, d) = ("Ad00000000000000a1", "Ad00000000000000b2", "Ad00000000000000c3", "Ad00000000000000d4");
        let code = format!(
            "uint64_t f_0000000000000001({a}* p1, {c}* p2) {{\n  uint64_t l0;\n  {b} l3;\n  {c} *l4 = p2;\n  l0 = *(uint64_t*)((uint8_t*)(p1) + 640);\n  l0 += *(uint64_t*)((uint8_t*)((*({d}**)((uint8_t*)(p1) + 8))) + 16);\n  f_0000000000000002(l4);\n  return l0;\n}}\n"
        );
        assert_eq!(scan_layout_deps(&code), BTreeSet::from([a, b, d].map(String::from)));
    }

    /// `hot_pick`: today's rule copies no fn with a cleanup frame; the frame rule copies one
    /// that `frames` holds, and a copy outside the unit's copies by today's rule (`today`)
    /// only when it reads no big ADT.
    #[test]
    fn the_frame_rule_adds_no_big_struct_reader() {
        let fid = "1234567890abcdef";
        let framed = FnOut {
            text: CText::Plain(format!(
                "struct fr{fid} {{\n  int32_t st;\n}};\nstatic inline __attribute__((always_inline)) void cl{fid}(struct fr{fid} *Lc);\nstatic inline __attribute__((always_inline)) void clw{fid}(struct fr{fid} *Lc) {{ if (__builtin_expect(Lc->st != 0, 0)) cl{fid}(Lc); }}\n/* f */\nlust_Unit f_{fid}(T* p1) {{\n  lust_Unit l0;\n  struct fr{fid} L __attribute__((cleanup(clw{fid})));\n  L.st = 0;\nbb0:;\n  l0 = ((lust_Unit){{}});\n  return l0;\n}}\nstatic inline __attribute__((always_inline)) void cl{fid}(struct fr{fid} *Lc) {{\n  switch (Lc->st) {{\n  default: return;\n  }}\n}}\n"
            )),
            ..Default::default()
        };
        let (rid, big) = ("00000000000000aa", "Ad00000000000000a1");
        let reader = FnOut {
            text: CText::Plain(format!("/* g */\nuint64_t f_{rid}({big}* p1) {{\n  uint64_t l0;\nbb0:;\n  l0 = *(uint64_t*)((uint8_t*)(p1) + 640);\n  return l0;\n}}\n")),
            ..Default::default()
        };
        let hot = |frames: &[&str], big: &[&str]| CopyHot {
            hot: HashSet::new(),
            frames: frames.iter().map(|i| u64::from_str_radix(i, 16).unwrap()).collect(),
            big: big.iter().map(|s| s.to_string()).collect(),
        };
        let (none, today) = (HashSet::new(), HashSet::from([7]));
        // Today's rule.
        assert!(!hot_pick(&framed, 1, fid, &hot(&[fid], &[]), None));
        assert!(hot_pick(&reader, 7, rid, &hot(&[], &[big]), None));
        // The frame rule: a frame fn when `frames` holds it.
        assert!(!hot_pick(&framed, 1, fid, &hot(&[], &[]), Some(&none)));
        assert!(hot_pick(&framed, 1, fid, &hot(&[fid], &[]), Some(&none)));
        // A big ADT's reader only as one of today's copies.
        assert!(!hot_pick(&reader, 7, rid, &hot(&[], &[big]), Some(&none)));
        assert!(hot_pick(&reader, 7, rid, &hot(&[], &[big]), Some(&today)));
        assert!(hot_pick(&reader, 7, rid, &hot(&[], &[]), Some(&none)));
    }

    /// Byte grouping: groups fill to the target, an over-target slot
    /// stands alone, empty input gives no groups, and every slot is
    /// in exactly one group, in order.
    #[test]
    fn group_fns_by_bytes_fills_to_target() {
        assert_eq!(group_fns_by_bytes(&[], 100), Vec::<std::ops::Range<usize>>::new());
        assert_eq!(group_fns_by_bytes(&[10, 20, 30, 40], 60), vec![0..3, 3..4]);
        assert_eq!(group_fns_by_bytes(&[10, 500, 10], 100), vec![0..1, 1..2, 2..3]);
        assert_eq!(group_fns_by_bytes(&[0, 0, 5], 4), vec![0..2, 2..3]);
        let sizes = [7usize; 5000];
        let groups = group_fns_by_bytes(&sizes, 1_000_000);
        assert_eq!(groups.len(), 2, "the 4096-slot cap splits a run of small slots");
        assert_eq!(groups[0], 0..4096);
    }

    /// `LUST_IMPL` groups leave the declaration header; `#else`
    /// branches, nested other conditionals, and undecidable groups
    /// stay. The runtime's own tables and bodies are impl-only, so
    /// the built header names none of them but keeps prototypes.
    #[test]
    fn strip_impl_blocks_keeps_decl_branches() {
        let src = "a\n#ifdef LUST_IMPL\nimpl\n#ifdef __APPLE__\nimpl2\n#else\nimpl3\n#endif\n#else\ndecl\n#endif\nb\n\
                   #ifndef LUST_IMPL\nnodef\n#endif\n#ifdef __x86_64__\narch\n#endif\n\
                   #if defined(LUST_IMPL) && defined(__linux__)\nguard\n#elif defined(LUST_IMPL)\nempty\n#endif\nc\n";
        assert_eq!(strip_impl_blocks(src), "a\ndecl\nb\nnodef\n#ifdef __x86_64__\narch\n#endif\nc\n");
        let decls = runtime_decls();
        assert!(decls.contains("void lust_rt_init(void)"), "prototypes stay");
        assert!(!decls.contains("lust_uni_alphabetic_ranges"), "impl-only Unicode tables go");
        assert!(!decls.contains("lust_alt_stack"), "impl-only bodies go");
        assert!(decls.len() < runtime_source(false).len() / 2, "the header shrinks: {} bytes", decls.len());
    }

    use crate::check::check_fn;
    use crate::check::collect;
    use crate::diag::{FileId, SourceMap, Span};
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// End to end over hand-built IR for the forms the front end does
    /// not produce yet (float values, fn pointer values and indirect
    /// calls, 128-bit literals): collect and lower a plain program,
    /// rewrite `main` by hand to use the new IR, generate all units,
    /// compile them with the system C compiler, run, and compare
    /// output. This is the verification for the float and fn pointer
    /// codegen until W-CORELANG wires the front end (L0602, L0641).
    #[test]
    fn float_and_fnptr_ir_runs() {
        let src = "fn add1(x: i64) -> i64 { x + 1 }\nfn main() { println!(\"{}\", add1(41)); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let add1 = program.fn_names[&interner.intern("add1")];
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();

        let mut outs: Vec<FnOut> = Vec::new();
        for i in 0..n {
            let fid = LocalDefId(i as u32);
            let (ck, errs) = check_fn(&program, fid);
            assert!(errs.is_empty(), "{errs:?}");
            let mut body = crate::lower::lower(&program, fid, ck);
            if fid == main {
                rewrite_main(&mut body, add1);
            }
            outs.push(gen_fn(&program, &body, &map, 1, &slots));
        }
        let mut glue = GlueSet::default();
        glue.add(&program, &slots, outs.iter().flat_map(|o| o.glue.iter()));
        let units = [
            main_unit(slots[main.0 as usize], &[], None),
            glue_unit(&program, &glue),
            runtime_unit(),
            table_unit(n, &[5]),
            loc_unit(&SlotFiles { paths: &["test.rs"], of_slot: &[] }, &vec![1; n]),
            fn_unit(&program, &outs, &(0..n).collect::<Vec<_>>(), &glue, "lust_register_u5", Some(slots[main.0 as usize])),
        ];
        let dir = std::env::temp_dir().join(format!("lust-cgen-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut files = Vec::new();
        for (i, u) in units.iter().enumerate() {
            let f = dir.join(format!("u{i}.c"));
            std::fs::write(&f, u).unwrap();
            files.push(f);
        }
        let exe = dir.join("prog");
        let cc = std::process::Command::new("cc").arg("-O0").arg("-w").arg("-o").arg(&exe).args(&files).output().unwrap();
        assert!(cc.status.success(), "cc failed: {}", String::from_utf8_lossy(&cc.stderr));
        let run = std::process::Command::new(&exe).output().unwrap();
        assert!(run.status.success(), "run failed: {}", String::from_utf8_lossy(&run.stderr));
        assert_eq!(String::from_utf8(run.stdout).unwrap(), "42\n3\n1.75\n1267650600228229401496703205381\n");
    }

    /// A move out of part of a drop-needing local through a deref
    /// has no move path drop elaboration can track. The borrow
    /// checker rejects such a move before code generation, so no
    /// lowered body from source reaches this: hand-build one and
    /// check `gen_fn` reports it in `FnOut::error` instead of
    /// panicking or silently dropping the rest twice.
    #[test]
    fn bad_move_path_is_an_error_not_a_panic() {
        let src = "fn main() { println!(\"hi\"); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let slots: Vec<u32> = (0..program.fns.len() as u32).collect();
        let (ck, errs) = check_fn(&program, main);
        assert!(errs.is_empty(), "{errs:?}");
        let mut body = crate::lower::lower(&program, main, ck);
        assert!(gen_fn(&program, &body, &map, 1, &slots).error.is_none(), "the lowered body is fine");
        let span = Span::new(FileId(0), 0, 0);
        let elems = body.tys.intern_tys(&[STRING, int(IntTy::U8)]);
        let tuple_ty = body.tys.intern(TyKind::Tuple(elems));
        let local = |ty: Ty| LocalDecl { ty, mutable: false, name: None };
        body.locals = vec![local(UNIT), local(tuple_ty), local(STRING)];
        body.blocks = vec![BlockData {
            stmts: vec![Stmt {
                kind: StmtKind::Assign(
                    Place::local(2),
                    Rvalue::Use(Operand::Move(Place { local: 1, proj: vec![Proj::Deref, Proj::Field(0)] })),
                ),
                span,
            }],
            term: Terminator::Return,
            term_span: span,
        }];
        let out = gen_fn(&program, &body, &map, 1, &slots);
        assert!(!out.has_code(), "no code is emitted for a bad move body");
        let err = out.error.expect("a deref part move is a code generation error");
        assert!(err.contains("drop elaboration cannot track"), "{err}");
    }

    /// `pack_texts` packs the C texts into frames that read back the same, packs a changed fn's
    /// new text into a new frame, and packs a frame again once less than half of it is in use.
    #[test]
    fn packed_texts_read_back() {
        if !crate::image::packs() {
            return;
        }
        let text = |i: usize| format!("/* m::f{i} */\nvoid f{i}(void) {{\n  g({i});\n}}\n");
        let fresh = |t: String| FnOut { text: CText::Plain(t), ..Default::default() };
        let frame = |f: &FnOut| match &f.text {
            CText::Packed { frame, .. } => Some(frame.clone()),
            CText::Plain(_) => None,
        };
        let same = |a: &FnOut, b: &FnOut| frame(a).zip(frame(b)).is_some_and(|(a, b)| std::sync::Arc::ptr_eq(&a, &b));
        let mut out: Vec<FnOut> = (0..4).map(|i| fresh(if i == 2 { String::new() } else { text(i) })).collect();
        pack_texts(&mut out);
        assert!(same(&out[0], &out[1]) && same(&out[1], &out[3]) && frame(&out[2]).is_none(), "one frame, no text for no code");
        for i in [0, 1, 3] {
            assert_eq!(out[i].code_text(), text(i));
            assert_eq!(out[i].text_fp(), fresh(text(i)).text_fp());
        }
        let first = frame(&out[1]).unwrap();
        out[0] = fresh(text(10));
        pack_texts(&mut out);
        assert!(!same(&out[0], &out[1]) && same(&out[1], &out[3]), "a new frame for the changed text; 2/3 of the old one is in use");
        out[1] = fresh(text(11));
        pack_texts(&mut out);
        assert!(same(&out[1], &out[3]) && !std::sync::Arc::ptr_eq(&frame(&out[3]).unwrap(), &first), "the old frame is packed again");
        for (i, t) in [(0, 10), (1, 11), (3, 3)] {
            assert_eq!(out[i].code_text(), text(t));
        }
    }

    /// A trait method stub and a template are never generated, so
    /// their fn slots stay empty. A call into one (here hand-built:
    /// check routes no call there) is an internal error in
    /// `FnOut::error`, never C that calls an empty slot. Generating
    /// the stub itself is the same error.
    #[test]
    fn call_to_fn_without_body_is_an_error() {
        let src = "trait Tr { fn go(&self) -> i32; fn dflt(&self) -> i32 { 100 } }\nstruct A;\n\
                   impl Tr for A { fn go(&self) -> i32 { 1 } }\nfn main() { println!(\"{}\", A.go()); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let slots: Vec<u32> = (0..program.fns.len() as u32).collect();
        let named = |class: crate::check::generics::FnClass, name: &str| {
            (0..program.fns.len() as u32)
                .map(LocalDefId)
                .find(|&f| program.gx.fn_class[f.0 as usize] == class && interner.get(program.fn_info(f).name) == name)
                .unwrap()
        };
        let stub = named(crate::check::generics::FnClass::Stub, "go");
        let template = named(crate::check::generics::FnClass::Template, "dflt");
        let lowered = || {
            let (ck, errs) = check_fn(&program, main);
            assert!(errs.is_empty(), "{errs:?}");
            crate::lower::lower(&program, main, ck)
        };
        assert!(gen_fn(&program, &lowered(), &map, 1, &slots).error.is_none(), "the lowered body is fine");
        for callee in [stub, template] {
            let mut bad = lowered();
            let mut calls = 0;
            for b in &mut bad.blocks {
                if let Terminator::Call { target: CallTarget::Fn(f), .. } = &mut b.term {
                    *f = callee;
                    calls += 1;
                }
            }
            assert_eq!(calls, 1, "main calls `go` once");
            let out = gen_fn(&program, &bad, &map, 1, &slots);
            assert!(!out.has_code(), "no code is emitted for the caller");
            let err = out.error.expect("a call to a fn without a body is a code generation error");
            assert!(err.starts_with("internal:") && err.contains("has no generated body"), "{err}");
        }
        let mut own = lowered();
        own.fn_id = stub;
        let err = gen_fn(&program, &own, &map, 1, &slots).error.expect("a stub is never generated");
        assert!(err.contains("has no generated body"), "{err}");
    }

    /// In release C, a body that a thread makes after another body asked the same layout
    /// in one codegen phase still takes the `Layout` read (`c_layout`, `phase_tag`). A
    /// front image build kept the old field offsets of such a body when the layout moved.
    #[test]
    fn release_layout_reads_hold_in_a_layout_phase() {
        let src = "struct T { a: u64 }\nstruct S { t: T, y: u64 }\nfn get(p: &S) -> u64 { p.y }\nfn main() { let s = S { t: T { a: 1 }, y: 2 }; println!(\"{}\", get(&s) + s.t.a); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let p = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let a = p.type_names[&interner.intern("S")];
        let names = std::sync::Arc::new(names::Names { fns: Vec::new(), adts: Vec::new(), by_id: Default::default() });
        let reads = names::with(Some(&names), || {
            in_layout_phase(layout_phase(), || {
                (0..2).map(|_| crate::check::derive_delta::scoped(true, || c_layout(&p, &CTy::Adt(a))).1).collect::<Vec<_>>()
            })
        });
        let def = p.def_of_adt(a);
        for (body, r) in reads.iter().enumerate() {
            assert!(r.iter().any(|&(d, bits)| d == def && bits & crate::check::derive_delta::bit::LAYOUT != 0), "body {body} reads S's layout: {r:?}");
        }
    }

    /// Derived glue regenerates when a field type changes under the
    /// same Adt id: `refresh` on the edited program reports the
    /// regeneration and the glue text moves; on the same program it
    /// is a no-op. (Review B3/C3: `add` alone kept the old Debug body.)
    #[test]
    fn glue_refresh_regenerates_on_field_type_edit() {
        fn with_program<R>(src: &str, f: impl FnOnce(&Interner, &crate::check::collect::Program) -> R) -> R {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            f(&interner, &program)
        }
        let v1 = "#[derive(Debug)]\nstruct S { b: u8 }\nfn main() { let s = S { b: 0 }; println!(\"{:?}\", s); }\n";
        let v2 = "#[derive(Debug)]\nstruct S { b: bool }\nfn main() { let s = S { b: false }; println!(\"{:?}\", s); }\n";
        let mut glue = GlueSet::default();
        // The Adt id is collect order; both programs declare S first,
        // so one key names it in both, as in one daemon session.
        let (key, text1) = with_program(v1, |interner, p| {
            let a = p.type_names[&interner.intern("S")];
            let key = (Glue::Debug, CTy::Adt(a));
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            glue.add(p, &slots, [&key].into_iter());
            (key, glue_unit(p, &glue))
        });
        let regen_same = with_program(v1, |_interner, p| {
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            glue.refresh(p, &slots, [&key].into_iter()).1
        });
        assert!(!regen_same, "same program: nothing regenerates");
        let text1_again = with_program(v1, |_interner, p| glue_unit(p, &glue));
        assert_eq!(text1_again, text1, "same program: same glue text");
        let (regen, text2) = with_program(v2, |_interner, p| {
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            let regen = glue.refresh(p, &slots, [&key].into_iter()).1;
            (regen, glue_unit(p, &glue))
        });
        assert!(regen, "field type edit regenerates the Debug glue");
        assert_ne!(text2, text1, "regenerated glue text differs");
    }

    /// The release C unit of fn `root` alone (`fn_unit`, its small callees and glue inline), of
    /// one-file program `src` with unwind tables, given to `check` inside the release names,
    /// with a lookup of the program's Adts by name.
    fn with_release_unit(src: &str, root: &str, check: impl FnOnce(&str, &dyn Fn(&str) -> CTy)) {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        (program.unwind, program.unwind_tables) = (true, true);
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let f = program.fn_names[&interner.intern(root)];
        names::with(Some(&names), || {
            let outs: Vec<FnOut> = (0..n)
                .map(|i| {
                    let (ck, errs) = check_fn(&program, LocalDefId(i as u32));
                    assert!(errs.is_empty(), "{errs:?}");
                    gen_fn(&program, &crate::lower::lower(&program, LocalDefId(i as u32), ck), &map, 1, &slots)
                })
                .collect();
            let mut glue = GlueSet::default();
            glue.add(&program, &slots, outs.iter().flat_map(|o| o.glue.iter()));
            let unit = fn_unit(&program, &outs, &[f.0 as usize], &glue, "lust_register_t", None);
            check(&unit, &|name| CTy::Adt(program.type_names[&interner.intern(name)]));
        });
    }

    /// Release C with unwind tables: a fn that drops an enum through `&mut` gets the enum's
    /// one-arm drop glue inline, and that glue only passes its `Rc` field to the Rc's own glue
    /// (a call: dropping `Big` can panic, so it keeps its cleanup frame). The unit defines the
    /// enum, but neither the Rc's counted block nor `Big`: holding `Big`'s size made every
    /// unit that dropped such an enum change with `Big` (tsgo's merges 9 and 11).
    #[test]
    fn inline_drop_glue_defines_no_type_behind_a_field() {
        let src = "use std::rc::Rc;\nstruct D;\nimpl Drop for D { fn drop(&mut self) {} }\nstruct Big { a: u64, d: D }\n\
                   enum E { A, B(Rc<Big>) }\nfn clear(e: &mut E) { *e = E::A; }\n\
                   fn main() { let mut e = E::B(Rc::new(Big { a: 1, d: D })); clear(&mut e); }\n";
        with_release_unit(src, "clear", |unit, adt| {
            let (big, e) = (ctype(&adt("Big")), ctype(&adt("E")));
            assert!(unit.contains(&format!("inline void drop_{e}_(")), "the enum's drop glue is inline:\n{unit}");
            assert!(!unit.contains(&format!("struct {big} {{")) && !unit.contains(&format!("sizeof({big})")), "the unit defines no {big}:\n{unit}");
        });
    }

    /// A local with alignment over 16 is a plain declaration in release C (the C compiler
    /// realigns the frame) and an aligned spot in a char buffer in dev C (tcc does not).
    #[test]
    fn overaligned_local_is_plain_in_release_c() {
        let src = "#[derive(Clone, Copy)]\n#[repr(align(64))]\nstruct Wide { a: u64, b: u64 }\n\
                   #[inline(never)]\nfn twice(w: Wide) -> Wide { let v = w; Wide { a: v.a * 2, b: v.b } }\n\
                   fn main() { println!(\"{}\", twice(Wide { a: 1, b: 2 }).a); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let twice = program.fn_names[&interner.intern("twice")];
        let code = || {
            let (ck, errs) = check_fn(&program, twice);
            assert!(errs.is_empty(), "{errs:?}");
            gen_fn(&program, &crate::lower::lower(&program, twice, ck), &map, 1, &slots).code_text().into_owned()
        };
        let release = names::with(Some(&names), code);
        assert!(!release.contains("_b[sizeof(") && !release.contains("#define l"), "release C declares it plainly:\n{release}");
        let dev = names::with(None, code);
        assert!(dev.contains("_b[sizeof(") && dev.contains("#undef l"), "dev C keeps the aligned buffer:\n{dev}");
    }

    /// Release C: a fn whose constants all have compile-time values names them by content
    /// (`kconst::kdata_ok`): each is a guarded weak definition among its externs, read in
    /// place, with no first-run test, and equal content in two fns has one name. A float
    /// constant keeps run-time interning.
    #[test]
    fn compile_time_constants_are_named_data_in_release_c() {
        let src = "#[inline(never)]\nfn a() -> (&'static str, &'static (u32, u32)) { (\"hi\", &(7, 9)) }\n\
                   #[inline(never)]\nfn b() -> &'static (u32, u32) { &(7, 9) }\n\
                   #[inline(never)]\nfn f() -> &'static f64 { &1.5 }\n\
                   fn main() { println!(\"{:?} {:?} {}\", a(), b(), f()); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let out = |name: &str| {
            let f = program.fn_names[&interner.intern(name)];
            let (ck, errs) = check_fn(&program, f);
            assert!(errs.is_empty(), "{errs:?}");
            names::with(Some(&names), || gen_fn(&program, &crate::lower::lower(&program, f, ck), &map, 1, &slots))
        };
        let (a, b, f) = (out("a"), out("b"), out("f"));
        let defs = |o: &FnOut| o.externs.iter().filter(|e| e.contains("LUST_KDATA")).map(|e| e.to_string()).collect::<Vec<_>>();
        let (ac, bc, fc) = (a.code_text(), b.code_text(), f.code_text());
        assert!(!ac.contains("lks_ok") && !ac.contains("lust_kintern"), "no run-time interning:\n{ac}");
        assert_eq!(defs(&a).len(), 2, "the str and the tuple are named data:\n{:?}", a.externs);
        let name = bc.split("&lust_kc").nth(1).map(|s| &s[..32]).expect("b reads its tuple by name");
        assert!(defs(&a).iter().any(|d| d.contains(&format!("lust_kc{name} "))), "equal content, one name:\n{:?}", a.externs);
        assert!(fc.contains("lust_kintern") && defs(&f).is_empty(), "a float constant keeps run-time interning:\n{fc}");
    }

    /// Inline clone glue of a struct copies its reference field and passes its String to the
    /// String's own glue: the unit defines the struct, but not `Big` behind the reference.
    #[test]
    fn inline_clone_glue_defines_no_type_behind_a_field() {
        let src = "struct Big { a: u64, b: u64, c: u64 }\n#[derive(Clone)]\nstruct S<'a> { r: &'a Big, n: String }\n\
                   fn dup<'a>(s: &S<'a>) -> S<'a> { s.clone() }\n\
                   fn main() { let b = Big { a: 1, b: 2, c: 3 }; let s = S { r: &b, n: String::new() }; let _t = dup(&s); }\n";
        with_release_unit(src, "dup", |unit, adt| {
            let (big, s) = (ctype(&adt("Big")), adt("S"));
            assert!(unit.contains(&format!("inline {} clone_{}(", ctype(&s), mangle(&s))), "the struct's clone glue is inline:\n{unit}");
            assert!(!unit.contains(&format!("struct {big} {{")), "the unit defines no {big}:\n{unit}");
        });
    }

    /// What a Vec's drop or clone glue holds in place is its element as held by value: a
    /// `Box<[S]>` element is its slice struct (a glue shard that held only such a Vec's drop
    /// declared the slice by its forward typedef, and its loop indexed it), and an `Rc<S>`
    /// element is a pointer, with no count block to define. An Rc's own glue holds the block.
    #[test]
    fn vec_glue_holds_its_element_by_value() {
        let s = CTy::Adt(AdtId(0));
        let vec_of = |e: CTy| (Glue::Drop, CTy::Vec(Box::new(e)));
        assert_eq!(GlueSet::pointer_block(&vec_of(CTy::BoxSlice(Box::new(s.clone())))), Some(vec![CTy::Slice(Box::new(s.clone()))]));
        assert_eq!(GlueSet::pointer_block(&vec_of(CTy::Rc(Box::new(s.clone())))), Some(vec![]));
        assert_eq!(GlueSet::pointer_block(&vec_of(s.clone())), Some(vec![s.clone()]));
        assert_eq!(GlueSet::pointer_block(&(Glue::Clone, CTy::Rc(Box::new(s.clone())))), Some(vec![CTy::Rc(Box::new(s))]));
    }

    /// Release C's count block holds no value (`rc_head`): a fn that clones an `Rc<Big>`,
    /// passes `&Big` on (to a fn of another unit) and drops the clone, with the Rc's clone and
    /// drop glue inline, defines the block as its two counts and a byte array at Big's
    /// alignment, frees it with no size of Big, and defines no Big (the block that held Big
    /// defined it as a block of its size).
    #[test]
    fn rc_glue_defines_no_value_in_the_count_block() {
        let src = "use std::rc::Rc;\nstruct Big { a: u64, b: u64, c: u64, d: [u64; 4] }\n\
                   #[inline(never)]\nfn look(b: &Big) -> u64 { b.a + b.d[1] }\n\
                   fn pass(r: &Rc<Big>) -> u64 { let k = r.clone(); let n = look(&k); drop(k); n }\n\
                   fn main() { let r = Rc::new(Big { a: 1, b: 2, c: 3, d: [4; 4] }); let _n = pass(&r); }\n";
        with_release_unit(src, "pass", |unit, adt| {
            let big = adt("Big");
            let (m, ct) = (mangle(&big), ctype(&big));
            assert!(unit.contains(&format!("typedef struct RcI_{m} {{ uint64_t strong; uint64_t weak; _Alignas(8) unsigned char v[]; }} RcI_{m};")), "the block holds no Big:\n{unit}");
            assert!(unit.contains(&format!("lust_rc_free(*p, _Alignof(RcI_{m}))")), "the drop glue frees the block with no size of Big:\n{unit}");
            assert!(!unit.contains(&format!("struct {ct} {{")), "the unit defines no Big:\n{unit}");
        });
    }

    /// The release location unit: on an ELF target each live fn's word is an element of one
    /// array with an assembler alias by the fn's name (the same symbols and values as the C
    /// constants of other targets), ranked by id; the unit declares only the runtime's
    /// location globals, not the runtime.
    #[test]
    fn loc_unit_aliases_one_array_on_elf() {
        let names = std::sync::Arc::new(names::Names {
            fns: vec![Some("00000000000000b2".to_string()), Some("00000000000000a1".to_string())],
            adts: Vec::new(),
            by_id: Default::default(),
        });
        let files = SlotFiles { paths: &["a.rs"], of_slot: &[0, 0] };
        names::with(Some(&names), || {
            let elf = names::loc_unit(&[0, 1], &files, &[3, 7], true);
            assert!(elf.contains("const uint64_t lust_so_tab[2] __attribute__((aligned(8))) = {0ull,1099511627776ull};"), "{elf}");
            assert!(elf.contains(".set lust_so_00000000000000a1, lust_so_tab+0\\n") && elf.contains(".set lust_so_00000000000000b2, lust_so_tab+8\\n"), "{elf}");
            assert!(elf.contains("static const uint32_t lines[2] = {7,3};"), "lines by rank:\n{elf}");
            assert!(!elf.contains("const uint64_t lust_so_0") && !elf.contains("lust_string_new"), "{elf}");
            let c = names::loc_unit(&[0, 1], &files, &[3, 7], false);
            assert!(c.contains("const uint64_t lust_so_00000000000000a1 = 0ull;") && c.contains("const uint64_t lust_so_00000000000000b2 = 1099511627776ull;"), "{c}");
        });
    }

    /// A fn that borrows a RefCell of `Option<Rc<Rc<Big>>>` (tsgo's FileVersion behind a cache
    /// cell) reads the cell's flag and takes its value's address: through the guard's deref and
    /// its inline drop glue the unit defines the cell, but neither `Big` nor its count block.
    #[test]
    fn guard_borrow_defines_only_the_cell() {
        let src = "use std::cell::RefCell;\nuse std::rc::Rc;\nstruct Big { a: u64, b: u64, c: u64 }\n\
                   fn look(o: &Option<Rc<Rc<Big>>>) -> bool { match o { Some(_) => true, None => false } }\n\
                   fn peek(c: &RefCell<Option<Rc<Rc<Big>>>>) -> bool { let b = c.borrow(); look(&*b) }\n\
                   fn main() { let c = RefCell::new(Some(Rc::new(Rc::new(Big { a: 1, b: 2, c: 3 })))); let _p = peek(&c); }\n";
        with_release_unit(src, "peek", |unit, adt| {
            let big = adt("Big");
            assert!(unit.contains("inline void drop_Gd_"), "the guard's drop glue is inline:\n{unit}");
            assert!(!unit.contains(&format!("struct {} {{", ctype(&big))), "the unit defines no {}:\n{unit}", ctype(&big));
            assert!(!unit.contains(&format!("RcI_{} {{", mangle(&big))), "the unit defines no count block of {}:\n{unit}", ctype(&big));
        });
    }

    /// Release C with unwind tables: a by-pointer parameter whose drop the cleanup can run is
    /// used in place, `(*p2)`, with no copy-in, and the frame points at the pointee; one with
    /// nothing to drop (no frame) keeps its copy-in.
    #[test]
    fn frame_held_param_is_used_in_place() {
        let src = "struct Big { s: String, a: u64, b: u64 }\nstruct Plain { a: u64, b: u64, c: u64 }\n\
                   #[inline(never)]\nfn check(n: usize) { if n > 1000 { panic!(\"too many\"); } }\n\
                   #[inline(never)]\nfn keep(v: &mut Vec<Big>, b: Big) { check(v.len()); v.push(b); }\n\
                   #[inline(never)]\nfn sum(b: Plain) -> u64 { b.a ^ b.c }\n\
                   fn main() { let mut v = Vec::new(); keep(&mut v, Big { s: String::new(), a: 1, b: 2 }); println!(\"{}\", sum(Plain { a: 3, b: 4, c: 5 }) + v.len() as u64); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        (program.unwind, program.unwind_tables) = (true, true);
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let [keep, sum] = ["keep", "sum"].map(|f| program.fn_names[&interner.intern(f)]);
        names::with(Some(&names), || {
            let code = |f: LocalDefId| {
                let (ck, errs) = check_fn(&program, f);
                assert!(errs.is_empty(), "{errs:?}");
                gen_fn(&program, &crate::lower::lower(&program, f, ck), &map, 1, &slots).code_text().into_owned()
            };
            let (kc, sc) = (code(keep), code(sum));
            assert!(!kc.contains("l2 = *p2") && kc.contains("L.pl2 = &(*p2);"), "keep uses its parameter in place:\n{kc}");
            assert!(sc.contains("l1 = *p1"), "sum, whose parameter has nothing to drop (no frame), copies it in:\n{sc}");
        });
    }

    /// Release C with unwind tables, `inplace` at its default (both rules): a fn that returns over 32 bytes
    /// builds its value in `(*out)` and copies nothing at its return, and one that returns a
    /// call's result passes its own out storage on (R1); an aggregate of plain operands
    /// assigned to a fresh local with drop glue is written with no temporary (R3).
    #[test]
    fn values_are_built_in_their_final_place() {
        if std::env::var("LUST_RELEASE_INPLACE").is_ok() {
            return;
        }
        let src = "struct Big { a: u64, b: u64, c: u64, d: u64, e: u64 }\nstruct S { v: Vec<u32>, n: u32 }\n\
                   #[inline(never)]\nfn make(n: u64) -> Big { Big { a: n, b: n + 1, c: n + 2, d: n + 3, e: n + 4 } }\n\
                   #[inline(never)]\nfn chain(n: u64) -> Big { make(n * 2) }\n\
                   #[inline(never)]\nfn fresh(v: Vec<u32>, n: u32) -> usize { let s: S; s = S { v, n }; s.v.len() + s.n as usize }\n\
                   fn main() { println!(\"{} {}\", chain(3).e, fresh(vec![1], 2)); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        (program.unwind, program.unwind_tables) = (true, true);
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let [make, chain, fresh] = ["make", "chain", "fresh"].map(|f| program.fn_names[&interner.intern(f)]);
        names::with(Some(&names), || {
            let code = |f: LocalDefId| {
                let (ck, errs) = check_fn(&program, f);
                assert!(errs.is_empty(), "{errs:?}");
                gen_fn(&program, &crate::lower::lower(&program, f, ck), &map, 1, &slots).code_text().into_owned()
            };
            let (mc, cc, fc) = (code(make), code(chain), code(fresh));
            for (name, c) in [("make", &mc), ("chain", &cc)] {
                assert!(!c.contains("*out = l0") && !c.contains(" l0") && c.contains("(*out)"), "{name} builds its value in (*out):\n{c}");
            }
            assert!(cc.contains("&(*out)"), "chain passes its own out storage to make:\n{cc}");
            // A temporary holding the aggregate: `T tN = ((T){ ... });`.
            let temp = fc.lines().any(|l| {
                let w: Vec<&str> = l.split_whitespace().collect();
                w.windows(3).any(|w| w[0].len() > 1 && w[0].starts_with('t') && w[0][1..].bytes().all(|b| b.is_ascii_digit()) && w[1] == "=" && w[2].starts_with("(("))
            });
            assert!(!temp, "fresh writes its new S with no temporary:\n{fc}");
        });
    }

    /// Release C glue shards, one key each: the shard of a struct's drop glue holds the
    /// small glue it calls from other shards (an `Option<Rc<dyn Fn>>` field's drop) as an
    /// inline definition, and every declaration of it there says `inline`. B1 records each
    /// shard whole, with a read of every glue entry it holds or inlines, and does not make a
    /// shard it found clean.
    #[test]
    fn glue_shard_inlines_small_glue_from_other_shards() {
        let src = "use std::rc::Rc;\ntrait Hook { fn run(&self) -> u32; }\nstruct One;\nimpl Hook for One { fn run(&self) -> u32 { 1 } }\n\
                   struct Hooks { a: Option<Rc<dyn Hook>>, b: Option<Rc<dyn Hook>>, n: u32 }\n\
                   fn main() { let r: Rc<dyn Hook> = Rc::new(One); let h = Hooks { a: Some(r), b: None, n: 2 }; println!(\"{}\", h.n); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        (program.unwind, program.unwind_tables) = (true, true);
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();
        let names = std::sync::Arc::new(names::Names {
            fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
            adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
            by_id: Default::default(),
        });
        let hooks = program.type_names[&interner.intern("Hooks")];
        names::with(Some(&names), || {
            let outs: Vec<FnOut> = (0..n)
                .map(|i| {
                    let (ck, errs) = check_fn(&program, LocalDefId(i as u32));
                    assert!(errs.is_empty(), "{errs:?}");
                    gen_fn(&program, &crate::lower::lower(&program, LocalDefId(i as u32), ck), &map, 1, &slots)
                })
                .collect();
            let mut glue = GlueSet::default();
            glue.add(&program, &slots, outs.iter().flat_map(|o| o.glue.iter()));
            let shards = names::glue_shards(&program, &glue, &outs, 1);
            let drop_hooks = format!("void drop_{}_(", ctype(&CTy::Adt(hooks)));
            let shard = shards.iter().find(|s| s.lines().any(|l| l.starts_with(&drop_hooks) && l.ends_with('{'))).expect("a shard defines the struct's drop glue");
            assert!(shard.contains("inline void drop_O_Rcdyn_(O_O_Rcdyn_ *p) {"), "the field's drop is inline there:\n{shard}");
            assert!(shard.lines().all(|l| !l.starts_with("void drop_O_Rcdyn_(")), "no declaration of it without inline:\n{shard}");
            assert_eq!(shards.iter().filter(|s| s.lines().any(|l| l.starts_with("void drop_O_Rcdyn_(O_O_Rcdyn_ *p) {"))).count(), 1, "one external definition");
            let keys = names::glue_shard_keys(&glue, &outs, 1);
            let made = names::glue_shard_texts(&program, &glue, &keys, &[], true);
            assert_eq!(made.iter().map(|(c, _)| c.as_str()).collect::<Vec<_>>(), shards, "a record does not change a shard");
            let glue_read = |k: &(Glue, CTy)| record::Read::Glue(k.0, k.1.clone());
            for ((_, rec), ks) in made.iter().zip(&keys) {
                let (_, reads) = rec.as_ref().expect("every byte of a shard is a piece");
                assert!(ks.iter().all(|k| reads.contains(&glue_read(k))), "a shard reads each key it holds");
            }
            let at = shards.iter().position(|s| s == shard).unwrap();
            let field_drop = glue.protos.iter().find(|(_, p)| p.starts_with("void drop_O_Rcdyn_(")).map(|(k, _)| k).unwrap();
            assert!(made[at].1.as_ref().is_some_and(|(_, reads)| reads.contains(&glue_read(field_drop))), "and each one it inlines");
            let skipped = names::glue_shard_texts(&program, &glue, &keys, &vec![true; keys.len()], true);
            assert!(skipped.iter().all(|(c, rec)| c.is_empty() && rec.is_none()), "a shard B1 found clean is not made");
        });
    }

    /// The unit header compiles, and defines each macro once: units build with -w, so a second
    /// `#define` of a name (an inl.h fast path written twice) would replace the first in
    /// silence, as a duplicate lust_vec_with_capacity once did.
    #[test]
    fn unit_header_defines_each_macro_once() {
        let dir = std::env::temp_dir().join(format!("lust-unit-header-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("h.c");
        std::fs::write(&f, unit_header()).unwrap();
        let cc = std::process::Command::new("cc").args(["-fsyntax-only", "-std=gnu11"]).arg(&f).output().unwrap();
        let err = String::from_utf8_lossy(&cc.stderr);
        assert!(cc.status.success() && !err.contains("redefined"), "{err}");
    }

    /// Release C statics in parts, one static a part (a 1-byte target): a merge that changes one
    /// static's value changes its part and nothing else (the index keeps every registration),
    /// though the statics share pointees across parts (one "hello", one trampoline), and every
    /// part and the index compile on their own declarations. B1's record of the pass leaves its
    /// texts as they are, takes every byte as a piece, and reads the statics' content
    /// (`names::statics_content_fp`), which moves with a static's value and only then.
    #[test]
    fn statics_parts_change_only_where_the_static_is() {
        let src = |a: i64| {
            format!(
                "static A: i64 = {a};\nstatic B: &str = \"hello\";\nstatic C: &[u8] = b\"hello\";\nstatic D: [u32; 4] = [1, 2, 3, 4];\n\
                 static E: &[i64] = &[10, 20, 30];\nstatic F: Option<&str> = Some(\"hello\");\nstatic G: fn() -> i64 = f;\n\
                 static H: &[&str] = &[\"x\", \"hello\"];\nfn f() -> i64 {{ 7 }}\nfn main() {{}}\n"
            )
        };
        type Pass = (String, Vec<String>, names::StaticsRecord, (u64, u64));
        let parts_of = |a: i64| -> Pass {
            let src = src(a);
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(&src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let mut map = SourceMap::default();
            map.add_file("test.rs", &src);
            let n = program.fns.len();
            let slots: Vec<u32> = (0..n as u32).collect();
            let names = std::sync::Arc::new(names::Names {
                fns: (0..n).map(|s| Some(format!("{s:016x}"))).collect(),
                adts: (0..program.adts.len()).map(|a| format!("t{a}")).collect(),
                by_id: Default::default(),
            });
            names::with(Some(&names), || {
                let outs: Vec<FnOut> = (0..n)
                    .map(|i| {
                        let (ck, errs) = check_fn(&program, LocalDefId(i as u32));
                        assert!(errs.is_empty(), "{errs:?}");
                        gen_fn(&program, &crate::lower::lower(&program, LocalDefId(i as u32), ck), &map, 1, &slots)
                    })
                    .collect();
                let mut glue = GlueSet::default();
                glue.add(&program, &slots, outs.iter().flat_map(|o| o.glue.iter()));
                let (index, parts, rec) = names::statics_parts(&program, &glue, 1, true);
                let plain = names::statics_parts(&program, &glue, 1, false);
                assert_eq!((&plain.0, &plain.1, &plain.2), (&index, &parts, &None), "a record leaves the texts as they are");
                (index, parts, rec, names::statics_content_fp(&program, &glue.slots))
            })
        };
        let ((index, parts, rec, fp), (index2, parts2, rec2, fp2)) = (parts_of(5), parts_of(6));
        let (pieces, reads) = rec.expect("every byte of the pass is a piece");
        assert!(reads.contains(&record::Read::Statics), "the pass reads the statics' content");
        assert!(reads.iter().any(|r| matches!(r, record::Read::Type(..))), "and the types it declares");
        assert_ne!(Some(pieces), rec2.map(|(p, _)| p), "a static's value moves the pieces");
        assert_ne!(fp, fp2, "and the content read");
        assert_eq!(fp, parts_of(5).3, "the same program, the same content read");
        assert_eq!(parts.len(), 8, "a part per static");
        assert_eq!(index, index2, "the same registrations");
        let changed: Vec<usize> = (0..parts.len()).filter(|&j| parts[j] != parts2[j]).collect();
        assert_eq!(changed.len(), 1, "only A's part changes");
        assert!(parts2[changed[0]].contains("6") && !parts2[changed[0]].contains("hello"), "the part is A's:\n{}", parts2[changed[0]]);
        let hello = parts.iter().filter(|t| t.contains("\"hello")).count();
        assert_eq!(hello, 1, "one definition of the shared bytes");
        let dir = std::env::temp_dir().join(format!("lust-statics-parts-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        for (k, t) in parts.iter().chain([&index]).enumerate() {
            let f = dir.join(format!("p{k}.c"));
            std::fs::write(&f, t).unwrap();
            let cc = std::process::Command::new("cc").args(["-fsyntax-only", "-w", "-std=gnu11"]).arg(&f).output().unwrap();
            assert!(cc.status.success(), "part {k} compiles:\n{}\n{t}", String::from_utf8_lossy(&cc.stderr));
        }
    }

    /// Replaces `main` with a hand-built body: an indirect call
    /// through a fn pointer value, float add, remainder and a
    /// saturating float-to-int cast, and a 128-bit literal print.
    fn rewrite_main(body: &mut Body, add1: LocalDefId) {
        let span = Span::new(FileId(0), 0, 0);
        let i64_ty = int(IntTy::I64);
        let f64_ty = body.tys.intern(TyKind::Float(FloatTy::F64));
        let u128_ty = int(IntTy::U128);
        let inputs = body.tys.intern_tys(&[i64_ty]);
        let sig = body.tys.intern_sig(Binder::plain(FnSig::plain(inputs, i64_ty)));
        let fnptr_ty = body.tys.intern(TyKind::FnPtr(sig));
        let local = |ty: Ty| LocalDecl { ty, mutable: false, name: None };
        // Print args hold a reference to the value, as lower emits them:
        // locals 8.. hold &l2, &l5, &l6, &l7 for the four prints.
        let ref_i64 = body.tys.mk_ref(false, i64_ty);
        let ref_f64 = body.tys.mk_ref(false, f64_ty);
        let ref_u128 = body.tys.mk_ref(false, u128_ty);
        body.locals = vec![
            local(UNIT),
            local(fnptr_ty),
            local(i64_ty),
            local(f64_ty),
            local(f64_ty),
            local(i64_ty),
            local(f64_ty),
            local(u128_ty),
            local(ref_i64),
            local(ref_i64),
            local(ref_f64),
            local(ref_u128),
        ];
        let assign = |l: Local, rv: Rvalue| Stmt { kind: StmtKind::Assign(Place::local(l), rv), span };
        let print = |l: Local, ty: Ty| Stmt {
            kind: StmtKind::Print {
                stderr: false,
                newline: true,
                parts: vec![FmtPart::Arg { value: Operand::Copy(Place::local(l)), ty, debug: false, spec: FmtSpec::default(), width: None, prec: None }],
            },
            span,
        };
        let fconst = |v: f64| Operand::Const(Const::Float(v.to_bits(), FloatTy::F64));
        body.blocks = vec![
            BlockData {
                stmts: vec![assign(1, Rvalue::FnValue(add1, fnptr_ty))],
                term: Terminator::Call {
                    target: CallTarget::Indirect(1),
                    args: vec![Operand::Const(Const::Int(41, IntTy::I64))],
                    dest: Place::local(2),
                    next: Bb(1),
                    unwind: None,
                },
                term_span: span,
            },
            BlockData {
                stmts: vec![
                    assign(3, Rvalue::Use(fconst(1.5))),
                    assign(4, Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(3)), fconst(2.25))),
                    assign(5, Rvalue::Cast(Operand::Copy(Place::local(4)), i64_ty)),
                    assign(6, Rvalue::Bin(BinOp::Rem, Operand::Copy(Place::local(4)), fconst(2.0))),
                    assign(7, Rvalue::Use(Operand::Const(Const::Int((1u128 << 100) + 5, IntTy::U128)))),
                    assign(8, Rvalue::Ref(false, Place::local(2))),
                    print(8, i64_ty),
                    assign(9, Rvalue::Ref(false, Place::local(5))),
                    print(9, i64_ty),
                    assign(10, Rvalue::Ref(false, Place::local(6))),
                    print(10, f64_ty),
                    assign(11, Rvalue::Ref(false, Place::local(7))),
                    print(11, u128_ty),
                ],
                term: Terminator::Return,
                term_span: span,
            },
        ];
    }
}

/// The `(u8, T)` cell of a `thread_local!` value of C type `t`: the
/// state byte (0 initial, 1 alive, 2 destroyed) and the value.
fn tls_cell(t: &CTy) -> CTy {
    CTy::Tuple(vec![CTy::Int(IntTy::U8), t.clone()])
}

/// Release C: the native cell of `thread_local!` static `i` (its `tls_cell` type). Every
/// thread_local of a release program has one, so every access reaches the same storage:
/// the static's unit defines the cell (`__thread`, zeroed: state 0), a getter of this
/// thread's cell, and the key as the getter's address (`native_tls_def`); a body whose key
/// traces to the static takes the cell's address, any other calls the getter through the
/// key (`tls_builtin`). None outside release C (tcc has no native TLS: the runtime's slots).
pub(crate) fn native_tls_cell(p: &Program, i: usize) -> Option<CTy> {
    let st = &p.statics[i];
    if !names::release() || st.tls.is_none() {
        return None;
    }
    Some(tls_cell(&cty(&p.tys, p.tys.local_key_elem(st.ty)?)))
}

/// `native_tls_cell`'s definitions for static `i` named `sym`: the cell, its getter, the key.
pub(crate) fn native_tls_def(p: &Program, i: usize, cell: &CTy) -> String {
    let sym = static_sym(p, i as u32);
    let h = sym.strip_prefix("lust_static_").unwrap_or(&sym);
    format!(
        "__thread {ct} lust_tlc_{h};\nstatic void *lust_tlg_{h}(void) {{ return &lust_tlc_{h}; }}\n{key} {sym} = ({key})(uintptr_t)lust_tlg_{h};\n",
        ct = ctype(cell),
        key = ctype(&cty(&p.tys, p.statics[i].ty))
    )
}

/// The `TlsInit` and `TlsDtor` glue of the cell type `c` (see `Glue`).
/// Rust's `LazyStorage` order: a value made while the init fn ran (a
/// recursive access) is replaced and dropped; else the cell turns alive
/// and a value that needs drop registers its destructor.
fn tls_glue(p: &Program, g: &Glue, c: &CTy, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let CTy::Tuple(parts) = c else { unreachable!("tls glue keys on the cell tuple") };
    let t = &parts[1];
    let (m, ct, vt) = (mangle(c), ctype(c), ctype(t));
    let drops = needs_drop_c(p, t);
    if drops {
        need(Glue::Drop, t);
    }
    if *g == Glue::TlsDtor {
        let _ = writeln!(protos, "void tlsdtor_{m}(void *p);");
        let drop = if drops { format!("drop_{}(&c->f1); ", mangle(t)) } else { String::new() };
        let _ = writeln!(defs, "void tlsdtor_{m}(void *p) {{
  {ct} *c = ({ct} *)p;
  if (c->f0 == 1) {{ c->f0 = 2; {drop}}}
}}
");
        return;
    }
    let _ = writeln!(protos, "{ct} *tlsinit_{m}({ct} *c, void *init);");
    let make = if ret_by_out(p, t) { format!("((void (*)({vt} *))init)(&v);") } else { format!("v = (({vt} (*)(void))init)();") };
    let (replace, register) = if drops {
        need(Glue::TlsDtor, c);
        (format!(" {vt} old = c->f1; c->f1 = v; drop_{}(&old); ", mangle(t)), format!(" lust_tls_register(c, tlsdtor_{m});"))
    } else {
        (" c->f1 = v; ".to_string(), String::new())
    };
    let _ = writeln!(
        defs,
        "{ct} *tlsinit_{m}({ct} *c, void *init) {{\n  if (c->f0 == 2) return 0;\n  {vt} v; {make}\n  if (c->f0 == 1) {{{replace}}}\n  else {{ c->f1 = v; c->f0 = 1;{register} }}\n  return c;\n}}\n"
    );
}

impl FnGen<'_, '_> {
    /// The static a TLS key operand names. Lowering makes the key a temp assigned once from
    /// the static's address (`StaticRef`), maybe through a reborrow (`&*t`); any other shape,
    /// or a temp assigned twice, gives None (`tls_builtin` then reads the key).
    fn tls_key_static(&self, key: &Operand) -> Option<u32> {
        let mut l = match key {
            Operand::Copy(p) | Operand::Move(p) if p.proj.is_empty() => p.local,
            _ => return None,
        };
        for _ in 0..4 {
            let mut def = None;
            for bb in &self.body.blocks {
                if let Terminator::Call { dest, .. } = &bb.term
                    && dest.local == l
                {
                    return None;
                }
                for st in &bb.stmts {
                    if let StmtKind::Assign(pl, rv) = &st.kind
                        && pl.local == l
                    {
                        if def.is_some() || !pl.proj.is_empty() {
                            return None;
                        }
                        def = Some(rv);
                    }
                }
            }
            match def? {
                Rvalue::StaticRef(i) => return Some(*i),
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.proj.is_empty() => l = p.local,
                Rvalue::Ref(_, p) if p.proj == [Proj::Deref] => l = p.local,
                _ => return None,
            }
        }
        None
    }

    /// `TlsAccess(key, init) -> &T`, `TlsTryAccess(key, init) ->
    /// Option<&T>`, and `TlsInitWith(key, value) -> Option<T>`
    /// (lower/tls.rs), over per-thread cells: release C's native cells
    /// (`native_tls_cell`), else the runtime's. The common access builds no
    /// `Option`: tcc zero-fills each compound literal with a memset call.
    fn tls_builtin(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str, key: &Operand) -> String {
        let t = match b {
            Builtin::TlsAccess | Builtin::TlsTryAccess => match &tys[1] {
                CTy::FnPtr(_, r) => (**r).clone(),
                _ => unreachable!("TlsAccess takes the init fn pointer"),
            },
            _ => tys[1].clone(),
        };
        let cell = tls_cell(&t);
        self.note_held(&cell);
        let (m, ct) = (mangle(&cell), ctype(&cell));
        let c = self.tmp();
        if names::release() {
            // The static's native cell (`native_tls_cell`): by name when the key traces to
            // its static, else through the getter the key holds.
            match self.tls_key_static(key).filter(|&i| native_tls_cell(self.p, i as usize).is_some()) {
                Some(i) => {
                    let sym = static_sym(self.p, i).replacen("lust_static_", "lust_tlc_", 1);
                    let _ = writeln!(self.out, "    extern __thread {ct} {sym};\n    {ct} *{c} = &{sym};");
                }
                None => {
                    let _ = writeln!(self.out, "    {ct} *{c} = ({ct} *)((void *(*)(void))(uintptr_t)*(uint64_t *){})();", vals[0]);
                }
            }
        } else {
            let _ = writeln!(self.out, "    {ct} *{c} = ({ct} *)lust_tls_cell((uint64_t *){}, sizeof({ct}), _Alignof({ct}));", vals[0]);
        }
        if b != Builtin::TlsInitWith {
            self.want(Glue::TlsInit, &cell);
            let _ = writeln!(self.out, "    if ({c}->f0 != 1) {c} = tlsinit_{m}({c}, (void *){});", vals[1]);
        }
        if b == Builtin::TlsAccess {
            let _ = writeln!(self.out, "    if (!{c}) lust_panic_cstr_owned({}, {loc});", c_string_lit(crate::lower::tls::ACCESS_PANIC.as_bytes()));
            return format!("(&{c}->f1)");
        }
        if b == Builtin::TlsTryAccess {
            let opt = CTy::Option(Box::new(CTy::Ref(Box::new(t))));
            self.note_held(&opt);
            let (some, none) = (self.make_variant(&opt, 1, &[format!("&{c}->f1")]), self.make_variant(&opt, 0, &[]));
            return format!("({c} ? {some} : {none})");
        }
        let opt = CTy::Option(Box::new(t.clone()));
        self.note_held(&opt);
        let (r, v) = (self.tmp(), self.tmp());
        let register = if needs_drop_c(self.p, &t) {
            self.want(Glue::TlsDtor, &cell);
            format!(" lust_tls_register({c}, tlsdtor_{m});")
        } else {
            String::new()
        };
        let none = self.make_variant(&opt, 0, &[]);
        let some = self.make_variant(&opt, 1, std::slice::from_ref(&v));
        let _ = writeln!(
            self.out,
            "    {} {v} = {}; {} {r}; if ({c}->f0 == 0) {{ {c}->f1 = {v}; {c}->f0 = 1;{register} {r} = {none}; }} else {r} = {some};",
            ctype(&t),
            vals[1],
            ctype(&opt)
        );
        r
    }
}
