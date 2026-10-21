// The bounded const evaluator (docs/ARCH.md section 2.13, non-generic form).
//
// One evaluator serves `const` and `static` initializers, array repeat
// counts and lengths, enum discriminants (through the scalar entry point in
// collect), inline `const { ... }` blocks, and `const _: () = assert!(...)`
// items. Anything outside the supported forms is an error with the const
// code for "outside the bound"; a call to a function that is not a
// `const fn` gets the non-const-call code instead. No synthetic runtime
// init functions are ever made for statics: a value either evaluates here
// or the program is rejected.
//
// The evaluator is generic over a `ConstCx` that answers name and type
// questions (const items, const fns, struct and variant shapes, layouts),
// so collect and body checking share it. Step cap: 1,000,000 steps per
// const item, plus a per-byte allowance for the largest byte blob the
// item touches (a loop that is linear in its data stays in bound),
// then the same outside-the-bound error.
#![allow(dead_code)] // OffsetOf and aggregate statics land with their callers.

use super::FloatTy;
use super::layout::Layout;
use super::{AdtId, BOOL, CHAR, ERROR, IntTy, REF_STR, Ty, TyIntern, TyKind, UNIT, USIZE};
use crate::ast::{self, Ast, BinOp, Expr, ExprId, MacroKind, Pat, PatId, UnOp};
use crate::diag::{Diag, Span};
use crate::intern::Sym;

/// The code for const input outside the bounded evaluator.
pub const C_OUTSIDE: &str = "L0630";
/// The code for a non-const call in a const context.
pub const C_NONCONST: &str = "L0631";

const STEP_CAP: u64 = 1_000_000;

/// One evaluated const value. Aggregates hold their fields in declaration
/// order; a variant payload carries its variant index.
#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {
    Int(i128),
    /// Float bits (`f32` bits zero-extended into the u64).
    Float(u64, FloatTy),
    Bool(bool),
    Char(char),
    /// A string literal: an index into the AST string table. Its type is `&str`.
    Str(u32),
    /// A `&str` made by evaluation, in no AST string table (a half of
    /// `str::split_at`), as one shared UTF-8 buffer.
    StrBytes(ast::ByteBlob),
    Unit,
    Aggregate(Vec<ConstValue>),
    Variant(u32, Vec<ConstValue>),
    /// A repeated element, from `[value; n]` with a const value.
    Repeat(Box<ConstValue>, u64),
    /// Byte data as one buffer: a byte string literal, an
    /// `include_bytes!` blob, or a slice of one. Its type is
    /// `[u8; N]`, `[u8]`, or (as a slice backing, like an aggregate
    /// at a slice type) `&[u8]`. One value holds every byte, so a
    /// loop over a megabyte blob reads bytes in place and never
    /// clones per element.
    Bytes(ast::ByteBlob),
    /// A promoted reference to a const value (`&EXPR` in const position).
    Ref(Box<ConstValue>),
    /// A reference to a static item, by index into the program's statics.
    StaticRef(u32),
    /// A reference into a static item (`&STATIC.f`, `&TABLE[i]`): the
    /// static's index and a non-empty path from its root. It keeps the
    /// static's storage, as in rustc. A `Deref` step only goes through
    /// a promoted reference inside the root's value (`static T: &[M] =
    /// &[..]`): a step through a reference to another static re-roots
    /// the path there (`static_place`).
    StaticPlace(u32, Box<[StaticStep]>),
    /// A fn item coerced to a fn pointer, by its `LocalDefId` index
    /// (W-STD-C: `static LazyLock` init fns). It can be stored and moved,
    /// never called or compared here, as in rustc.
    FnPtr(u32),
    /// A closure in a const or static value coerced to a fn pointer
    /// (census-10): the hidden fn that holds the value's copy (its
    /// `LocalDefId` index, expand/lazy.rs `hoist_value_closures`) and
    /// the closure's ordinal there. Its body fn exists once that fn is
    /// checked (`Program::value_closure_fn`); used as `FnPtr` is.
    ClosureFn(u32, u32),
}

/// One step of a `ConstValue::StaticPlace` path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StaticStep {
    /// A struct or tuple field, by index.
    Field(u32),
    /// An array or slice element, by index.
    Elem(u32),
    /// Into the promoted value a reference points to.
    Deref,
}

/// The value at `path` inside `v`, a static's value; None when the path
/// leaves the value (a step through a reference to another static, or
/// one the value's shape does not have).
pub fn value_at<'v>(mut v: &'v ConstValue, path: &[StaticStep]) -> Option<&'v ConstValue> {
    for step in path {
        v = match (step, v) {
            (StaticStep::Field(i) | StaticStep::Elem(i), ConstValue::Aggregate(vals)) => vals.get(*i as usize)?,
            (StaticStep::Elem(i), ConstValue::Repeat(x, n)) if u64::from(*i) < *n => x,
            (StaticStep::Deref, ConstValue::Ref(inner)) => inner,
            // A slice reference's value is its backing aggregate.
            (StaticStep::Deref, ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Bytes(_)) => v,
            _ => return None,
        };
    }
    Some(v)
}

/// Follows the reference at `path` inside static `idx`: into its
/// promoted value (a `Deref` step), or to the static it points into
/// (the path re-roots there). False when the value there is no
/// reference the path can follow.
fn static_deref<'a, C: ConstCx<'a>>(cx: &mut C, idx: &mut u32, path: &mut Vec<StaticStep>) -> bool {
    let Some(v) = cx.static_value(*idx).and_then(|v| value_at(v, path)) else { return false };
    match v {
        ConstValue::StaticRef(j) => {
            *idx = *j;
            path.clear();
        }
        ConstValue::StaticPlace(j, p) => {
            *idx = *j;
            *path = p.to_vec();
        }
        ConstValue::Ref(_) | ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Bytes(_) => path.push(StaticStep::Deref),
        _ => return false,
    }
    true
}

/// A copy of the value at `path` inside static `idx`, for a read
/// through a reference into it; a byte blob element reads as its int.
fn read_static<'a, C: ConstCx<'a>>(cx: &mut C, idx: u32, path: &[StaticStep]) -> Option<ConstValue> {
    let root = cx.static_value(idx)?;
    if let [init @ .., StaticStep::Elem(i)] = path
        && let Some(ConstValue::Bytes(b)) = value_at(root, init)
    {
        return b.as_slice().get(*i as usize).map(|&x| ConstValue::Int(x as i128));
    }
    value_at(root, path).cloned()
}

/// A value with its type, as the evaluator produces it.
pub type TypedValue = (ConstValue, Ty);

/// What a call in const position resolves to.
pub enum CallTarget {
    /// A `const fn` or tuple variant constructor the evaluator may run.
    ConstFn(ConstFnBody),
    VariantCtor {
        adt: AdtId,
        variant: u32,
        ty: Ty,
    },
    SizeOf(Ty),
    AlignOf(Ty),
    /// A callable that exists but is not const: the non-const-call error.
    NonConst,
    /// Not a callable the context knows: outside the bound.
    Unknown,
}

/// The parts of a const fn the evaluator runs.
pub struct ConstFnBody {
    /// Parameters as (name, mutable, pattern): a plain `name: Ty` parameter
    /// has no pattern and binds by name. A method's receiver comes
    /// first, as `self` (`param_tys[0]` is `Self` or `&Self`).
    pub params: Vec<(Sym, bool, Option<PatId>)>,
    pub param_tys: Vec<Ty>,
    pub ret: Ty,
    pub body: ast::BlockId,
    /// The flat type name `Self` means inside the body: the impl type of
    /// a method or associated fn, None for a free fn.
    pub owner: Option<Sym>,
    /// Whether the fn is generic, and which bounds its type args need.
    pub generic: ConstGeneric,
    /// The fn's `LocalDefId` index, for `ConstCx::bounds_hold`.
    pub def: u32,
    /// True for a method: `params[0]` is its receiver, named `self`.
    pub has_self: bool,
}

/// A const fn's generics, for a call in const position. The evaluator
/// has no trait solver of its own: a bounded generic fn runs when the
/// context proves its bounds (`ConstCx::bounds_hold`), and std's lazy
/// constructors' one bound it checks itself.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstGeneric {
    /// Not generic.
    No,
    /// Generic, with no bounds and no where clauses.
    Free,
    /// `LazyLock::new` / `LazyCell::new` (std source, W-STD-C): params
    /// `T` (0) and `F` (1), bound `F: FnOnce() -> T`.
    LazyCtor,
    /// Generic with bounds: runs when `ConstCx::bounds_hold` proves them.
    Bounded,
}

/// The questions the evaluator asks its caller.
/// L0652's text for a `size_of` or `align_of` with no layout: it names the
/// innermost type that has none (`layout::last_failure`), when known, or
/// the Adt whose field type did not resolve (that error is reported where
/// the type is written; naming the Adt lets the census charge this one to
/// it as a cascade).
fn layout_fail_text<'a>(cx: &impl ConstCx<'a>, what: &str) -> String {
    match super::layout::last_failure() {
        Some((t, true)) if !matches!(cx.tys_ref().kind(t), TyKind::Error) => {
            format!("unsupported layout form in `{what}`: a field of `{}` has a type that did not resolve", cx.ty_text(t))
        }
        Some((_, true)) => format!("unsupported layout form in `{what}`: a type that did not resolve"),
        Some((t, false)) => format!("unsupported layout form in `{what}`: `{}`", cx.ty_text(t)),
        None => format!("unsupported layout form in `{what}`"),
    }
}

pub trait ConstCx<'a> {
    type Tys: TyIntern;
    fn tys(&mut self) -> &mut Self::Tys;
    fn tys_ref(&self) -> &Self::Tys;
    fn ast(&self) -> &'a Ast;
    /// A const item or immutable static by name, evaluating it if
    /// needed. `at` is the use site: an item declared in a function
    /// body answers only inside its block scope, and shadows a
    /// module item of the same name there.
    fn const_item(&mut self, name: Sym, at: Span) -> Option<TypedValue>;
    /// True when name resolution already made each binding pattern that
    /// names an item in scope a path pattern (the resolver's tables): a
    /// binding pattern can then name only a const of an enclosing block,
    /// which the resolver leaves written (`block_const_item`).
    fn patterns_resolved(&self) -> bool {
        false
    }
    /// A const declared in an enclosing block of `at`, by name.
    fn block_const_item(&mut self, _name: Sym, _at: Span) -> Option<TypedValue> {
        None
    }
    /// `const_item` without the clone, for an item already evaluated:
    /// its value in place. An index into a table item reads one element
    /// through it, so many `static X: &T = &TABLE[i]` items do not copy
    /// the whole table each. None where the context does not keep
    /// values (the caller then takes the `const_item` path).
    fn const_item_ref(&self, _name: Sym, _at: Span) -> Option<(&ConstValue, Ty)> {
        None
    }
    /// An inherent associated const by its path (`Type::CONST`,
    /// module segments may lead), evaluating it if needed.
    fn assoc_const_item(&mut self, _segs: &[ast::PathSeg]) -> Option<TypedValue> {
        None
    }
    /// A trait associated const through a qualified path
    /// (`<S as Tr>::C`), evaluating it if needed.
    fn qpath_const(&mut self, _self_ty: ast::TyId, _trait_path: &[ast::PathSeg], _name: Sym) -> Option<TypedValue> {
        None
    }
    /// A call target for a callee expression already known to be a path.
    fn call_target(&mut self, callee: ExprId) -> CallTarget;
    /// The inherent method `name` of type `recv` (references peeled),
    /// for a method call in const position: a `ConstFn` with the
    /// receiver as its first parameter, `NonConst` for a method that
    /// is not `const`, `Unknown` when the type has no such inherent
    /// method (the primitive methods answer then).
    fn method_target(&mut self, _recv: Ty, _name: Sym) -> CallTarget {
        CallTarget::Unknown
    }
    /// True when the inherent method `name` of `recv` is private to
    /// the module whose const expression the evaluator runs (asked
    /// only outside a called const fn's body, like
    /// `named_field_private`).
    fn method_private(&mut self, _recv: Ty, _name: Sym) -> bool {
        false
    }
    /// Whether every where-clause of generic const fn `def` holds with
    /// its type params bound to `binds` (by param index), for the call
    /// at `span`. None when the context cannot prove them: the call is
    /// then outside the bound. A context may defer a closed trait goal
    /// to a later proof that reports at `span`.
    fn bounds_hold(&mut self, _def: u32, _binds: &[Option<Ty>], _span: Span) -> Option<bool> {
        None
    }
    /// The instance of generic Adt `adt` whose type params are `binds`
    /// (by param index), for a constructor call with no expected type.
    /// None when a param is unbound or not a type param.
    fn adt_instance(&mut self, _adt: AdtId, _binds: &[Option<Ty>]) -> Option<Ty> {
        None
    }
    /// False when `name` (the head of a `Type::item` path) names no
    /// type, alias, trait, or primitive here: the path's error is then
    /// the unknown type (rustc E0433). Contexts that cannot tell say
    /// true.
    /// The primitive a non-generic type alias names (`type IdCell =
    /// u32;` gives "u32"), so `IdCell::MAX` reads `u32::MAX`.
    fn alias_primitive(&self, _name: Sym) -> Option<&'static str> {
        None
    }
    /// The hashed collection a type alias names (`FxHashMap<K, V>` is a
    /// `HashMap`), for `Alias::with_hasher(s)` in const position.
    fn alias_hash(&self, _name: Sym) -> Option<super::hash::HashTy> {
        None
    }
    fn names_type(&mut self, _name: Sym) -> bool {
        true
    }
    /// A path used as a value: a unit variant, if it names one.
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)>;
    /// A static item by name at a use site: its index and type.
    fn static_item(&mut self, name: Sym, at: Span) -> Option<(u32, Ty)>;
    /// The evaluated value of the static at index `idx`, for a read
    /// through a reference into it (`StaticRef`, `StaticPlace`). None
    /// when the context cannot read it.
    fn static_value(&mut self, _idx: u32) -> Option<&ConstValue> {
        None
    }
    /// A safe, non-generic free fn named by a path, as a fn pointer
    /// value with its `fn(..) -> R` type.
    fn fn_item(&mut self, _segs: &[ast::PathSeg], _at: Span) -> Option<TypedValue> {
        None
    }
    /// A closure in a const or static value, as a fn pointer value of
    /// the `fn(..) -> R` type `expected`: one that captures nothing and
    /// has a hidden fn copy (`ConstValue::ClosureFn`).
    fn closure_value(&mut self, _closure: ExprId, _expected: Ty) -> Option<TypedValue> {
        None
    }
    /// The struct or variant a struct literal names.
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)>;
    /// Called around a const fn body the evaluator runs: `Self` inside
    /// it means `owner` (the fn's impl type), not the caller's. Contexts
    /// that resolve `Self` some other way keep these no-ops.
    fn enter_const_fn(&mut self, _owner: Option<Sym>) {}
    fn exit_const_fn(&mut self) {}
    /// Field names and types of one variant, in declaration order. Tuple
    /// fields answer with a dummy name; position is what matters there.
    fn variant_fields(&self, adt: AdtId, variant: u32) -> Vec<(Sym, Ty)>;
    /// The number of variants of an Adt (1 for a struct).
    fn variant_count(&self, adt: AdtId) -> u32;
    /// The pattern target (Adt, variant) a path pattern names.
    fn pattern_variant(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)>;
    /// Resolves a written type (casts, `size_of` arguments).
    fn resolve_ty(&mut self, t: ast::TyId) -> Ty;
    /// The layout of a type, for `size_of` and `align_of`.
    fn layout(&mut self, t: Ty) -> Option<Layout>;
    /// The text of an interned name.
    fn sym_text(&self, s: Sym) -> &str;
    /// The `repr` of an Adt, for `offset_of!` rules.
    fn adt_repr(&self, adt: AdtId) -> super::layout::Repr;
    /// The discriminant of one variant of an enum type.
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128;
    /// True when the Adt is an enum (a struct literal for it builds a variant).
    fn is_enum(&self, adt: AdtId) -> bool;
    /// True when a named field is private to the module whose const
    /// expression the evaluator runs. The evaluator asks only outside
    /// a called const fn's body: that body is checked in its own
    /// module by the body checker. The default answers false, for
    /// contexts with no module table.
    fn named_field_private(&mut self, _adt: AdtId, _field: Sym) -> bool {
        false
    }
    /// True when a tuple field is private, like `named_field_private`.
    fn tuple_field_private(&mut self, _adt: AdtId, _index: u32) -> bool {
        false
    }
    /// What a struct literal of this variant may not build under
    /// `#[non_exhaustive]` from this const expression's crate
    /// ("struct" or "variant"), like `named_field_private`.
    fn ne_lit_what(&mut self, _adt: AdtId, _variant: u32) -> Option<&'static str> {
        None
    }
    /// What a tuple or unit constructor use may not name under
    /// `#[non_exhaustive]`, like `ne_lit_what`.
    fn ne_ctor_what(&mut self, _adt: AdtId, _variant: u32) -> Option<&'static str> {
        None
    }
    /// What a named-field pattern may not match under
    /// `#[non_exhaustive]` (`rest` says it ends with `..`).
    fn ne_pat_what(&mut self, _adt: AdtId, _variant: u32, _rest: bool) -> Option<&'static str> {
        None
    }
    /// True when destroying a value of this type would run a
    /// destructor (rustc E0493 in a const context). Exact for
    /// concrete types; unresolved generic types answer false (the
    /// static const-fn check judges those under template rules).
    fn needs_drop(&self, _t: Ty) -> bool {
        false
    }
    /// True when values of this type can be mutated through a
    /// shared reference (rustc E0492 for a promoted temporary).
    fn interior_mut(&self, _t: Ty) -> bool {
        false
    }
    /// The promotion qualifs of the const item `name` names here
    /// (`constqual`), None when this context does not track them.
    fn const_item_qualif(&mut self, _name: Sym, _at: Span) -> Option<super::constqual::Qualif> {
        None
    }
    /// True when the Adt has a written `Drop` impl (`constqual`).
    fn adt_has_drop(&self, _adt: AdtId) -> bool {
        true
    }
    /// A short display name of a type, for drop diagnostics.
    fn ty_text(&self, _t: Ty) -> String {
        "this type".to_string()
    }
    /// True when values of this type are `Copy` (an array repeat
    /// above length 1 duplicates its operand).
    fn is_copy(&self, _t: Ty) -> bool {
        false
    }
}

/// Why evaluation left a block early.
enum Flow {
    Val(TypedValue),
    Break(Option<TypedValue>, Option<Sym>),
    Continue(Option<Sym>),
    Return(TypedValue),
}

/// One local: its name, value, `mut`, and whether it was moved out
/// (the E0493 drop check reads the last one at scope end).
type Env = Vec<(Sym, TypedValue, bool, bool)>;

/// The value of a local `e` names (a one-segment path bound in `env`), by
/// reference.
fn local_value<'e, 'a, C: ConstCx<'a>>(cx: &C, env: &'e Env, e: ExprId) -> Option<&'e TypedValue> {
    let Expr::Path(segs) = cx.ast().expr(e) else { return None };
    if segs.len() != 1 || segs[0].has_args() {
        return None;
    }
    env.iter().rev().find(|(n, _, _, _)| *n == segs[0].name).map(|(_, v, _, _)| v)
}

/// True when a pattern looks inside its value (a tuple, struct,
/// variant, or slice shape), as opposed to binding or comparing
/// the whole value.
fn pat_destructures(ast: &Ast, p: PatId) -> bool {
    match ast.pat(p) {
        Pat::TupleStruct { .. } | Pat::Struct { .. } | Pat::Tuple(_) | Pat::Slice { .. } => true,
        Pat::Or(alts) => alts.iter().any(|&a| pat_destructures(ast, a)),
        Pat::Ref { inner, .. } | Pat::At { inner, .. } | Pat::Paren(inner) => pat_destructures(ast, *inner),
        _ => false,
    }
}

/// True when a pattern binds its whole value to one name (so a
/// drop value moves into the binding instead of being destroyed
/// by the destructuring).
pub fn pat_is_whole_binding(ast: &Ast, p: PatId) -> bool {
    match ast.pat(p) {
        Pat::Binding { by_ref, .. } => !by_ref,
        Pat::Paren(inner) => pat_is_whole_binding(ast, *inner),
        Pat::At { inner, by_ref, .. } => !by_ref && (matches!(ast.pat(*inner), Pat::Wild) || pat_is_whole_binding(ast, *inner)),
        _ => false,
    }
}

/// True when `e` reads an existing place instead of making a new
/// value. The drop check uses it to tell a temporary (dropped at
/// the end of its statement) from a local (dropped at scope end,
/// judged there).
fn is_place_expr(ast: &Ast, e: ExprId) -> bool {
    matches!(
        ast.expr(e),
        Expr::Path(_) | Expr::SelfValue | Expr::Field { .. } | Expr::TupleField { .. } | Expr::Deref(_) | Expr::Index { .. } | Expr::QPath { .. }
    )
}

/// The value a borrowed place projects from: `&C.1` borrows into
/// the temporary `C`, `&(D(1), 4).1` into the tuple temporary.
fn projection_root(ast: &Ast, mut e: ExprId) -> ExprId {
    while let Expr::Field { base, .. } | Expr::TupleField { base, .. } = ast.expr(e) {
        e = *base;
    }
    e
}

/// A written path as text (`Type::f`), for diagnostics: the census
/// and readers find the item an error names by its backticked path.
fn path_text<'a, C: ConstCx<'a>>(cx: &C, segs: &[ast::PathSeg]) -> String {
    segs.iter().map(|s| crate::intern::source_name(cx.sym_text(s.name))).collect::<Vec<_>>().join("::")
}

/// The L0102 for a `Type::item` path whose head names no type.
fn unknown_type<'a, C: ConstCx<'a>>(cx: &C, head: &ast::PathSeg, span: Span) -> Diag {
    let n = crate::intern::source_name(cx.sym_text(head.name));
    Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type.")
}

/// Std fns this evaluator does not run that are no `const fn` in std:
/// a call is rustc E0015, also in a dead branch (a dead branch scan
/// keeps only that error). Any other std call it cannot run stays
/// outside the evaluator.
const STD_NONCONST: &[&str] = &[
    "std::process::exit",
    "std::process::abort",
    "std::process::id",
    "std::thread::spawn",
    "std::thread::sleep",
    "std::thread::yield_now",
    "std::thread::current",
    "std::thread::park",
    "std::env::var",
    "std::env::vars",
    "std::env::args",
    "std::env::current_dir",
    "std::fs::read",
    "std::fs::read_to_string",
    "std::fs::write",
    "std::io::stdin",
    "std::io::stdout",
    "std::io::stderr",
    "std::time::Instant::now",
    "std::time::SystemTime::now",
    "std::mem::drop",
    "std::mem::take",
];

fn outside(span: Span, what: &str) -> Diag {
    Diag::new(
        C_OUTSIDE,
        span,
        format!("{what} is outside the bounded const evaluator"),
        "Use literals, const items, and const fn calls only.",
    )
}

fn nonconst(span: Span, what: &str) -> Diag {
    Diag::new(
        C_NONCONST,
        span,
        format!("cannot call non-const function `{what}` in a const context"),
        "Mark the function `const fn`, or move the call out of the const item.",
    )
}

/// The L0510 for a private field named in a const expression, with
/// the same text as the body checker's field privacy errors.
fn private_field(span: Span, label: &str) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("field `{label}` is private"),
        "Make the field `pub(crate)` (the smallest widening that works).",
    )
}

/// The L0510 for a tuple struct constructor with a private field,
/// in call or pattern position.
fn private_ctor(span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        "tuple struct constructor is private".to_string(),
        "Make every field `pub(crate)`, or add a public constructor function.",
    )
}

/// Wraps `v` to the range of an integer type, as an `as` cast does.
pub fn truncate_to_int(v: i128, it: IntTy) -> i128 {
    let bits = it.bits();
    if bits >= 128 {
        return v;
    }
    let mask: i128 = (1i128 << bits) - 1;
    let u = v & mask;
    if it.signed() && (u >> (bits - 1)) & 1 == 1 { u - (1i128 << bits) } else { u }
}

/// True when a value produced as `vt` may stand where `ty` is required in a
/// const item: the types are equal, or they differ only by unsized coercions
/// rustc applies at a reference (`&[T; N]` to `&[T]`), possibly nested inside
/// tuples, arrays, or generic arguments. The operand of `&` is not a
/// coercion site, so a reference right behind a reference never unsizes
/// (`&&[1]` is no `&&[u8]` in rustc; `&(&[1],)` is a `&(&[u8],)`). An
/// `ERROR` on either side passes: that error was already reported where
/// the type was formed.
pub fn const_ty_compatible<T: TyIntern>(tys: &T, vt: Ty, ty: Ty) -> bool {
    const_ty_fits(tys, vt, ty, true)
}

/// `const_ty_compatible`; `site` is false right behind a reference.
fn const_ty_fits<T: TyIntern>(tys: &T, vt: Ty, ty: Ty, site: bool) -> bool {
    if vt == ty || vt == ERROR || ty == ERROR {
        return true;
    }
    match (tys.kind(vt), tys.kind(ty)) {
        (TyKind::Ref(_, m1, a), TyKind::Ref(_, m2, b)) => {
            (!m2.is_mut() || m1.is_mut())
                && (const_ty_fits(tys, a, b, false)
                    || site
                        && matches!((tys.kind(a), tys.kind(b)), (TyKind::Array(e1, _), TyKind::Slice(e2)) if const_ty_compatible(tys, e1, e2)))
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (a, b) = (tys.tys_of(a), tys.tys_of(b));
            a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| const_ty_compatible(tys, x, y))
        }
        (TyKind::Array(e1, n1), TyKind::Array(e2, n2)) => n1 == n2 && const_ty_compatible(tys, e1, e2),
        // A fn item value here has no references in its params, or none
        // and only `'static` ones in its return (`fn_item` in
        // check/collect.rs), so a written `&'static` in the pointer type
        // (W-BORROW3: no longer erased) fits it part by part.
        (TyKind::FnPtr(s1), TyKind::FnPtr(s2)) => {
            let (a, b) = (tys.sig(s1).value, tys.sig(s2).value);
            let (ai, bi) = (tys.tys_of(a.inputs), tys.tys_of(b.inputs));
            a.is_unsafe == b.is_unsafe
                && a.extern_c == b.extern_c
                && b.free_slots == 0
                && ai.len() == bi.len()
                && ai.iter().zip(bi).all(|(&x, &y)| same_but_regions(tys, x, y) && static_marks_fit(tys, x, y, true, false))
                && same_but_regions(tys, a.output, b.output)
                && static_marks_fit(tys, a.output, b.output, false, false)
        }
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (a, b) = (tys.args(a1), tys.args(a2));
            a.len() == b.len()
                && a.iter().zip(b).all(|(x, y)| match (x, y) {
                    (super::GenericArg::Ty(x), super::GenericArg::Ty(y)) => const_ty_compatible(tys, *x, *y),
                    _ => x == y,
                })
        }
        _ => false,
    }
}

/// True when two types are equal up to their regions: the parts of fn
/// pointer signatures, where only subtyping applies (no `&mut` to `&`
/// or array to slice coercion). `static_marks_fit` judges the regions.
fn same_but_regions<T: TyIntern>(tys: &T, a: Ty, b: Ty) -> bool {
    if a == b || a == ERROR || b == ERROR {
        return true;
    }
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Ref(_, m1, x), TyKind::Ref(_, m2, y)) => m1 == m2 && same_but_regions(tys, x, y),
        (TyKind::RawPtr(m1, x), TyKind::RawPtr(m2, y)) => m1 == m2 && same_but_regions(tys, x, y),
        (TyKind::Slice(x), TyKind::Slice(y)) => same_but_regions(tys, x, y),
        (TyKind::Array(x, n1), TyKind::Array(y, n2)) => n1 == n2 && same_but_regions(tys, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tys.tys_of(x), tys.tys_of(y));
            x.len() == y.len() && x.iter().zip(y).all(|(&p, &q)| same_but_regions(tys, p, q))
        }
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (x, y) = (tys.args(a1), tys.args(a2));
            x.len() == y.len()
                && x.iter().zip(y).all(|(p, q)| match (p, q) {
                    (super::GenericArg::Ty(p), super::GenericArg::Ty(q)) => same_but_regions(tys, *p, *q),
                    (super::GenericArg::Lifetime(_), super::GenericArg::Lifetime(_)) => true,
                    _ => p == q,
                })
        }
        (TyKind::FnPtr(s1), TyKind::FnPtr(s2)) => {
            let (p, q) = (tys.sig(s1).value, tys.sig(s2).value);
            let (pi, qi) = (tys.tys_of(p.inputs), tys.tys_of(q.inputs));
            p.is_unsafe == q.is_unsafe
                && p.extern_c == q.extern_c
                && pi.len() == qi.len()
                && pi.iter().zip(qi).all(|(&x, &y)| same_but_regions(tys, x, y))
                && same_but_regions(tys, p.output, q.output)
        }
        _ => false,
    }
}

/// The written `&'static` references of two fn pointer signature parts
/// (W-BORROW3): an input (`contra`) of `found` may not demand `'static`
/// where `expected` takes any lifetime, an output of `found` must be
/// `'static` where `expected` promises it, and under `&mut` (`inv`) the
/// two must agree.
fn static_marks_fit<T: TyIntern>(tys: &T, found: Ty, expected: Ty, contra: bool, inv: bool) -> bool {
    let st = |r: super::Region| r == super::Region::Static;
    match (tys.kind(found), tys.kind(expected)) {
        (TyKind::Ref(rf, m, a), TyKind::Ref(re, _, b)) => {
            let ok = if inv {
                st(rf) == st(re)
            } else if contra {
                !st(rf) || st(re)
            } else {
                !st(re) || st(rf)
            };
            ok && static_marks_fit(tys, a, b, contra, inv || m.is_mut())
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (a, b) = (tys.tys_of(a), tys.tys_of(b));
            a.iter().zip(b).all(|(&x, &y)| static_marks_fit(tys, x, y, contra, inv))
        }
        (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => static_marks_fit(tys, x, y, contra, inv),
        // The covariant std containers keep the position; any other
        // Adt holds its args invariant (lust computes no variance here).
        (TyKind::Adt(_, a1), TyKind::Adt(_, a2)) => {
            use super::BuiltinTy as B;
            let co = matches!(tys.builtin_of(found), Some(B::Option | B::Result | B::Vec | B::Boxed | B::Rc));
            tys.args(a1).iter().zip(tys.args(a2)).all(|(x, y)| match (x.as_ty(), y.as_ty()) {
                (Some(x), Some(y)) => static_marks_fit(tys, x, y, contra, inv || !co),
                _ => true,
            })
        }
        (TyKind::FnPtr(_), TyKind::FnPtr(_)) => const_ty_compatible(tys, found, expected) || !inv,
        _ => true,
    }
}

/// Two types equal but for their regions (`bind_params`).
fn same_up_to_regions<T: TyIntern>(tys: &T, a: Ty, b: Ty) -> bool {
    if a == b {
        return true;
    }
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Ref(_, m1, x), TyKind::Ref(_, m2, y)) => m1 == m2 && same_up_to_regions(tys, x, y),
        (TyKind::RawPtr(m1, x), TyKind::RawPtr(m2, y)) => m1 == m2 && same_up_to_regions(tys, x, y),
        (TyKind::Slice(x), TyKind::Slice(y)) => same_up_to_regions(tys, x, y),
        (TyKind::Array(x, n1), TyKind::Array(y, n2)) => n1 == n2 && same_up_to_regions(tys, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tys.tys_of(x), tys.tys_of(y));
            x.len() == y.len() && x.iter().zip(y).all(|(&p, &q)| same_up_to_regions(tys, p, q))
        }
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (x, y) = (tys.args(a1), tys.args(a2));
            x.len() == y.len()
                && x.iter().zip(y).all(|(p, q)| match (p.as_ty(), q.as_ty()) {
                    (Some(p), Some(q)) => same_up_to_regions(tys, p, q),
                    _ => p == q,
                })
        }
        (TyKind::FnPtr(s1), TyKind::FnPtr(s2)) => {
            let (p, q) = (tys.sig(s1).value, tys.sig(s2).value);
            let (pi, qi) = (tys.tys_of(p.inputs), tys.tys_of(q.inputs));
            p.is_unsafe == q.is_unsafe
                && p.extern_c == q.extern_c
                && pi.len() == qi.len()
                && pi.iter().zip(qi).all(|(&x, &y)| same_up_to_regions(tys, x, y))
                && same_up_to_regions(tys, p.output, q.output)
        }
        _ => false,
    }
}

/// Matches a generic const fn's param or return type `pat` against a
/// concrete `actual`, recording each `Param(i)` in `binds[i]`. A param
/// bound twice must bind the same type; parts with no param must be
/// `const_ty_compatible`. False on any mismatch.
fn bind_params<T: TyIntern>(tys: &mut T, pat: Ty, actual: Ty, binds: &mut Vec<Option<Ty>>) -> bool {
    if actual == ERROR {
        return true;
    }
    if !tys.flags(pat).contains_param() {
        return const_ty_compatible(tys, actual, pat);
    }
    match (tys.kind(pat), tys.kind(actual)) {
        (TyKind::Param(p), _) => {
            let i = p.0 as usize;
            if binds.len() <= i {
                binds.resize(i + 1, None);
            }
            match binds[i] {
                // Up to regions: a no-param fn item's value keeps its
                // `'static` returns (W-BORROW3), a type from a signature
                // may not.
                Some(b) => same_up_to_regions(tys, b, actual),
                None => {
                    binds[i] = Some(actual);
                    true
                }
            }
        }
        (TyKind::Ref(_, m1, a), TyKind::Ref(_, m2, b)) => m1 == m2 && bind_params(tys, a, b, binds),
        (TyKind::Slice(a), TyKind::Slice(b)) => bind_params(tys, a, b, binds),
        (TyKind::Array(a, n1), TyKind::Array(b, n2)) => n1 == n2 && bind_params(tys, a, b, binds),
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (a, b) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
            a.len() == b.len() && a.iter().zip(&b).all(|(&x, &y)| bind_params(tys, x, y, binds))
        }
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (a, b) = (tys.args(a1).to_vec(), tys.args(a2).to_vec());
            a.len() == b.len()
                && a.iter().zip(&b).all(|(x, y)| match (x, y) {
                    (super::GenericArg::Ty(x), super::GenericArg::Ty(y)) => bind_params(tys, *x, *y, binds),
                    _ => x == y,
                })
        }
        (TyKind::FnPtr(s1), TyKind::FnPtr(s2)) => {
            let (b1, b2) = (tys.sig(s1), tys.sig(s2));
            let (i1, i2) = (tys.tys_of(b1.value.inputs).to_vec(), tys.tys_of(b2.value.inputs).to_vec());
            b1.count == b2.count
                && b1.value.is_unsafe == b2.value.is_unsafe
                && b1.value.extern_c == b2.value.extern_c
                && i1.len() == i2.len()
                && i1.iter().zip(&i2).all(|(&x, &y)| bind_params(tys, x, y, binds))
                && bind_params(tys, b1.value.output, b2.value.output, binds)
        }
        _ => false,
    }
}

/// The indices of the params `t` mentions.
fn params_in<T: TyIntern>(tys: &T, t: Ty, out: &mut Vec<u32>) {
    if !tys.flags(t).contains_param() {
        return;
    }
    match tys.kind(t) {
        TyKind::Param(p) => out.push(p.0),
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => params_in(tys, e, out),
        TyKind::Tuple(ts) => {
            for &e in tys.tys_of(ts) {
                params_in(tys, e, out);
            }
        }
        TyKind::Adt(_, a) => {
            for g in tys.args(a) {
                if let Some(e) = g.as_ty() {
                    params_in(tys, e, out);
                }
            }
        }
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for &e in tys.tys_of(b.value.inputs) {
                params_in(tys, e, out);
            }
            params_in(tys, b.value.output, out);
        }
        // Any other kind with a param: count it unbindable.
        _ => out.push(u32::MAX),
    }
}

/// `t` with each bound param replaced (unbound params stay as written).
fn subst_binds<T: TyIntern>(tys: &mut T, t: Ty, binds: &[Option<Ty>]) -> Ty {
    if !tys.flags(t).contains_param() || binds.iter().all(|b| b.is_none()) {
        return t;
    }
    let args: Vec<super::GenericArg> = binds
        .iter()
        .enumerate()
        .map(|(i, b)| super::GenericArg::Ty(b.unwrap_or_else(|| tys.intern(TyKind::Param(super::ParamId(i as u32))))))
        .collect();
    super::subst(tys, t, &args)
}

/// The L0110 a const item gets when its value type is not its declared type.
pub fn const_ty_mismatch(span: Span, what: &str) -> Diag {
    Diag::new("L0110", span, format!("mismatched types in {what}"), "Change the value or the declared type.")
}

/// True when `v` fits in the integer type (const overflow is an error).
fn fits(v: i128, it: IntTy) -> bool {
    let bits = it.bits();
    if bits >= 128 {
        return true;
    }
    if it.signed() { v >= -(1i128 << (bits - 1)) && v < (1i128 << (bits - 1)) } else { v >= 0 && v < (1i128 << bits) }
}

// `ConstValue::Int` stores the canonical form of its typed value:
// sign-extended for signed types below 128 bits, zero-extended for
// unsigned types below 128 bits, and the raw 128 bits for i128 and
// u128 (so u128::MAX is -1). The helpers below convert between that
// storage, the raw bits, and the signed value. Every operation runs
// in its operand type, so u128 values at or above 2^127 compare,
// divide, and shift as unsigned.

/// The raw low bits of a stored integer, at its type's width.
fn int_bits(v: i128, it: IntTy) -> u128 {
    let bits = it.bits();
    if bits >= 128 { v as u128 } else { (v as u128) & ((1u128 << bits) - 1) }
}

/// The stored form of raw bits at a type's width.
fn int_from_bits(u: u128, it: IntTy) -> i128 {
    if it.bits() >= 128 { u as i128 } else { truncate_to_int(u as i128, it) }
}

/// The smallest value of a signed integer type (0 for unsigned).
fn int_min(it: IntTy) -> i128 {
    if !it.signed() {
        0
    } else if it.bits() >= 128 {
        i128::MIN
    } else {
        -(1i128 << (it.bits() - 1))
    }
}

/// Compares two stored integers at a type (signed value or raw bits).
fn cmp_int(a: i128, b: i128, it: Option<IntTy>) -> std::cmp::Ordering {
    match it {
        Some(it) if !it.signed() => int_bits(a, it).cmp(&int_bits(b, it)),
        Some(it) => truncate_to_int(a, it).cmp(&truncate_to_int(b, it)),
        None => a.cmp(&b),
    }
}

/// One binary integer operation in its operand type, as const
/// evaluation runs it (rustc E0080): arithmetic overflow, division
/// by zero, `MIN / -1`, and a shift amount at or past the bit width
/// are `None`. Shift and bitwise results wrap to the type's width.
/// Inputs and the result use the stored form (see `int_bits`), so
/// u128 values at or above 2^127 stay correct. Both const
/// evaluators (this one and the scalar one in collect) run integer
/// arithmetic through here, so they cannot disagree.
pub fn int_binop(op: BinOp, it: IntTy, x: i128, y: i128) -> Option<i128> {
    if it.signed() {
        let (x, y) = (truncate_to_int(x, it), truncate_to_int(y, it));
        let r = match op {
            BinOp::Add => x.checked_add(y),
            BinOp::Sub => x.checked_sub(y),
            BinOp::Mul => x.checked_mul(y),
            BinOp::Div | BinOp::Rem => {
                if y == 0 || (x == int_min(it) && y == -1) {
                    None
                } else if op == BinOp::Div {
                    Some(x / y)
                } else {
                    Some(x % y)
                }
            }
            BinOp::BitAnd => Some(int_from_bits(int_bits(x, it) & int_bits(y, it), it)),
            BinOp::BitOr => Some(int_from_bits(int_bits(x, it) | int_bits(y, it), it)),
            BinOp::BitXor => Some(int_from_bits(int_bits(x, it) ^ int_bits(y, it), it)),
            BinOp::Shl | BinOp::Shr => {
                let amt = u32::try_from(y).ok().filter(|&s| s < it.bits());
                match (op, amt) {
                    (BinOp::Shl, Some(s)) => Some(int_from_bits(int_bits(x, it) << s, it)),
                    (BinOp::Shr, Some(s)) => Some(x >> s),
                    _ => None,
                }
            }
            _ => return None,
        }?;
        if !matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr) && !fits(r, it) {
            return None;
        }
        Some(r)
    } else {
        let (x, y) = (int_bits(x, it), int_bits(y, it));
        let max = it.max128();
        let r = match op {
            BinOp::Add => x.checked_add(y).filter(|&r| r <= max),
            BinOp::Sub => x.checked_sub(y),
            BinOp::Mul => x.checked_mul(y).filter(|&r| r <= max),
            BinOp::Div => x.checked_div(y),
            BinOp::Rem => x.checked_rem(y),
            BinOp::BitAnd => Some(x & y),
            BinOp::BitOr => Some(x | y),
            BinOp::BitXor => Some(x ^ y),
            BinOp::Shl | BinOp::Shr => {
                let amt = u32::try_from(y).ok().filter(|&s| s < it.bits());
                match (op, amt) {
                    (BinOp::Shl, Some(s)) => Some((x << s) & max),
                    (BinOp::Shr, Some(s)) => Some(x >> s),
                    _ => None,
                }
            }
            _ => return None,
        }?;
        Some(int_from_bits(r, it))
    }
}

/// Compares two stored integers of one type (for the scalar evaluator).
pub fn int_cmp(it: IntTy, a: i128, b: i128) -> std::cmp::Ordering {
    cmp_int(a, b, Some(it))
}

/// Negation in a signed integer type: `None` on `MIN` and on every
/// unsigned type (const overflow, rustc E0080).
pub fn int_neg(it: IntTy, x: i128) -> Option<i128> {
    if !it.signed() {
        return None;
    }
    let x = truncate_to_int(x, it);
    if x == int_min(it) { None } else { Some(-x) }
}

/// Bitwise not in an integer type, in stored form.
pub fn int_not(it: IntTy, x: i128) -> i128 {
    int_from_bits(!int_bits(x, it), it)
}

/// The stored form of raw bits at a type's width (for the scalar evaluator).
pub fn int_stored(u: u128, it: IntTy) -> i128 {
    int_from_bits(u, it)
}

/// A float-to-int `as` cast, saturating at the target type's range
/// (NaN becomes 0), as Rust defines it. The host `as` casts have
/// the same semantics, so each target goes through its own host
/// type: casting to i128 first and truncating would wrap instead.
pub fn float_to_int(bits: u64, f: FloatTy, it: IntTy) -> i128 {
    let x: f64 = match f {
        FloatTy::F64 => f64::from_bits(bits),
        FloatTy::F32 => f32::from_bits(bits as u32) as f64,
    };
    match it {
        IntTy::I8 => x as i8 as i128,
        IntTy::I16 => x as i16 as i128,
        IntTy::I32 => x as i32 as i128,
        IntTy::I64 | IntTy::Isize => x as i64 as i128,
        IntTy::I128 => x as i128,
        IntTy::U8 => x as u8 as i128,
        IntTy::U16 => x as u16 as i128,
        IntTy::U32 => x as u32 as i128,
        IntTy::U64 | IntTy::Usize => x as u64 as i128,
        IntTy::U128 => (x as u128) as i128,
    }
}

/// True when an expression is an unsuffixed int or float literal,
/// possibly negated or wrapped in statement-free blocks: the forms
/// whose type a cast target decides (`{ 300 } as u8` is a `u8`
/// literal out of range, as `300 as u8` is).
pub fn is_unsuffixed_lit(ast: &Ast, e: ExprId) -> bool {
    match ast.expr(e) {
        Expr::Int(_, suffix) => suffix.is_none(),
        Expr::Float(i) => {
            let t = ast.strings[*i as usize].trim_end();
            !t.ends_with("f32") && !t.ends_with("f64")
        }
        Expr::Unary { op: UnOp::Neg, expr } => is_unsuffixed_lit(ast, *expr),
        Expr::Block(b) | Expr::ConstBlock(b) => {
            let b = ast.block(*b);
            b.stmts.is_empty() && b.tail.is_some_and(|t| is_unsuffixed_lit(ast, t))
        }
        _ => false,
    }
}

/// True when an expression's integer type is not pinned by anything
/// in it: only unsuffixed literals, `!`/`-`, and arithmetic over such
/// operands. Rust infers the type from the surroundings and falls
/// back to `i32`; the evaluator runs such an expression wide (i128)
/// and re-runs it at the pinning type where one appears (a binary
/// operation against a typed operand, a cast, an inline const with
/// no expected type). A name, a call, or a suffixed literal pins it.
pub fn flex_int_expr(ast: &Ast, e: ExprId) -> bool {
    match ast.expr(e) {
        Expr::Int(_, suffix) => suffix.is_none(),
        Expr::Unary { op: UnOp::Neg | UnOp::Not, expr } => flex_int_expr(ast, *expr),
        Expr::Binary { op, lhs, rhs } => {
            !op.is_cmp()
                && !matches!(op, BinOp::And | BinOp::Or)
                && flex_int_expr(ast, *lhs)
                && (matches!(op, BinOp::Shl | BinOp::Shr) || flex_int_expr(ast, *rhs))
        }
        Expr::Block(b) | Expr::ConstBlock(b) => {
            let b = ast.block(*b);
            b.stmts.is_empty() && b.tail.is_some_and(|t| flex_int_expr(ast, t))
        }
        Expr::If { then, els, .. } => {
            let then = ast.block(*then);
            then.stmts.is_empty()
                && then.tail.is_some_and(|t| flex_int_expr(ast, t))
                && els.is_some_and(|e| flex_int_expr(ast, e))
        }
        _ => false,
    }
}

/// Evaluates one const expression. `expected` is the type the context wants,
/// used for literal widths and array element types.
pub fn eval<'a, C: ConstCx<'a>>(cx: &mut C, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
    check_macro_forms(cx.ast(), e)?;
    // A literal local pinned only after a write held wide values
    // before the pin: the evaluation runs again with that local typed
    // at its `let` (see `FlexLocal`). Each run adds a pin, so the loop
    // ends.
    let mut pins: Vec<(PatId, Ty)> = Vec::new();
    loop {
        let (r, rerun) = eval_once(cx, e, expected, std::mem::take(&mut pins));
        match rerun {
            Some(p) if p.len() <= MAX_FLEX_RERUNS => pins = p,
            _ => return r,
        }
    }
}

/// Bounds the re-runs of one const evaluation (one per literal local
/// pinned after a write).
const MAX_FLEX_RERUNS: usize = 64;

/// One run of `eval` with the given literal-local pins. Returns the
/// pins to run again with when a dirty literal local got pinned.
fn eval_once<'a, C: ConstCx<'a>>(
    cx: &mut C,
    e: ExprId,
    expected: Option<Ty>,
    pins: Vec<(PatId, Ty)>,
) -> (Result<TypedValue, Diag>, Option<Vec<(PatId, Ty)>>) {
    let mut ev = Evaluator {
        steps: 0,
        extra_cap: 0,
        call_depth: 0,
        move_read: false,
        extending: std::collections::HashSet::new(),
        ext_roots: std::collections::HashSet::new(),
        dead_seen: std::collections::HashSet::new(),
        flex_debt: Vec::new(),
        local_debt: Vec::new(),
        self_sym: None,
        ref_bind: false,
        mut_arg: None,
        flex_locals: Vec::new(),
        next_flex_group: 0,
        pins,
        rerun: false,
        binds: Vec::new(),
    };
    let r = ev.run(cx, e, expected);
    let rerun = ev.rerun.then_some(ev.pins);
    (r, rerun)
}

impl Evaluator {
    /// Evaluates the const expression `e` from an empty env.
    fn run<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
        let mut env: Env = Vec::new();
        let span = cx.ast().expr_span(e);
        self.mark_extending(cx, e);
        match self.expr(cx, &mut env, e, expected)? {
            Flow::Val(v) => {
                // An unpinned literal that no context ever pinned falls back
                // to i32 in rustc: one outside i32's range is an error there,
                // however it escaped (a cast of the local it was bound to, a
                // tuple element nobody reads).
                if let Some(&d) = self.flex_debt.first() {
                    return Err(Diag::new(C_OUTSIDE, cx.ast().expr_span(d), "integer literal out of range in const", "Change the literal or the type."));
                }
                // The final value stands for the item's whole life: a
                // borrow of a temporary inside it must be promotable
                // (E0492/E0764).
                check_final_refs(cx, &v.0, v.1, span)?;
                Ok(v)
            }
            _ => Err(outside(span, "control flow out of a const expression")),
        }
    }
}

/// Which construction `Evaluator::check_ne` judges.
#[derive(Clone, Copy)]
enum NeKind {
    Lit,
    Ctor,
    Pat,
}

struct Evaluator {
    steps: u64,
    /// Extra steps a byte blob grants: a loop over N bytes needs a
    /// bounded number of steps per byte, so work that is linear in
    /// the data it reads stays inside the bound, while a plain
    /// infinite loop still hits the plain cap. Set from the largest
    /// blob the evaluation touches (see `note_blob`).
    extra_cap: u64,
    /// How deep the evaluator is in called const fn bodies. Field
    /// privacy asks run only at depth 0: a called const fn's body is
    /// written in its own module and checked there.
    call_depth: u32,
    /// True while evaluating an expression whose value moves into
    /// its parent (a call argument, an aggregate element, a tail):
    /// a local read at its leaf is a move (the E0493 check).
    move_read: bool,
    /// The extending borrows of the item (rustc's temporary lifetime
    /// extension, see `mark_extending`): their temporaries live in
    /// the final value and are never dropped. A borrowed drop
    /// temporary anywhere else is dropped inside the evaluation (E0493).
    extending: std::collections::HashSet<ExprId>,
    /// The temporaries extended by an extending borrow of a projection
    /// (`&C.1`, `&(D(1), 4).1`): the root value of the projection.
    ext_roots: std::collections::HashSet<ExprId>,
    /// The dead branches already scanned: the drop check is static, so
    /// one scan per branch is enough, also in a loop, and nested dead
    /// branches cost one pass each, not an exponential one.
    dead_seen: std::collections::HashSet<(bool, u32)>,
    /// Unsuffixed literals evaluated wide (no pinning type) whose
    /// magnitude does not fit i32, by expression. Evaluating the
    /// same expression at a pinning type, or reading a local it
    /// was bound to at a pinning type, clears the debt; a debt
    /// left at the end of `eval` is rustc's i32 fallback error.
    flex_debt: Vec<ExprId>,
    /// Which local names carry which flex debts.
    local_debt: Vec<(Sym, ExprId)>,
    /// The name a method body's receiver is bound under (`self`),
    /// set by the first method call: `Expr::SelfValue` reads it.
    self_sym: Option<Sym>,
    /// True while `match_pat` matches below a reference it went
    /// through: bindings there bind by reference.
    ref_bind: bool,
    /// The call argument being evaluated when it is a `&mut` borrow:
    /// the only place a `&mut` value may be made (`mut_ref_outside`).
    mut_arg: Option<ExprId>,
    /// The literal locals of the current frame whose integer type no
    /// use has pinned yet (see `FlexLocal`).
    flex_locals: Vec<FlexLocal>,
    next_flex_group: u32,
    /// The integer type of each literal local pinned so far, by its
    /// `let` pattern: a re-run types the local at its `let`.
    pins: Vec<(PatId, Ty)>,
    /// Set when a literal local was pinned after a write: its earlier
    /// arithmetic ran wide, so `eval` runs again with the pin.
    rerun: bool,
    /// The type args of the generic const fn whose body runs (by param
    /// index), for the reads that need a concrete type.
    binds: Vec<Option<Ty>>,
}

/// A local bound by `let x = <unsuffixed literal>;` with no written
/// type (`let mut hash = 0;`). Rust infers its type from later uses;
/// the evaluator holds it wide (i128) until the first use that pins
/// an integer type (a typed operand, a typed call argument, a typed
/// `let`, an index, a return), then retypes it. Locals that meet each
/// other in arithmetic share a group and are pinned together, as
/// inference unifies them. A local still holding its literal is
/// re-evaluated at the pinned type in place; one written since then
/// ran wide arithmetic, so the whole evaluation runs again with the
/// pin applied at the `let` (`Evaluator::rerun`).
#[derive(Clone)]
struct FlexLocal {
    /// The env slot and name of the binding.
    slot: usize,
    name: Sym,
    pat: PatId,
    /// The literal expression the slot still holds, or None once the
    /// slot was written with another value.
    init: Option<ExprId>,
    group: u32,
}

/// An unsuffixed literal expression with no names: re-evaluating it
/// at another type gives the value it has at that type.
fn pure_int_lit(ast: &Ast, e: ExprId) -> bool {
    match ast.expr(e) {
        Expr::Int(_, suffix) => suffix.is_none(),
        Expr::Unary { op: UnOp::Neg | UnOp::Not, expr } => pure_int_lit(ast, *expr),
        Expr::Binary { op, lhs, rhs } => {
            !op.is_cmp() && !matches!(op, BinOp::And | BinOp::Or) && pure_int_lit(ast, *lhs) && pure_int_lit(ast, *rhs)
        }
        Expr::Block(b) => {
            let b = ast.block(*b);
            b.stmts.is_empty() && b.tail.is_some_and(|t| pure_int_lit(ast, t))
        }
        _ => false,
    }
}

/// Steps one blob byte grants. A hash loop body (index, xor or
/// shift, multiply, increment, test) stays well under this.
const STEPS_PER_BLOB_BYTE: u64 = 96;

impl Evaluator {
    fn step(&mut self, span: Span) -> Result<(), Diag> {
        self.steps += 1;
        if self.steps > STEP_CAP + self.extra_cap {
            return Err(outside(span, "this const item (step limit reached)"));
        }
        Ok(())
    }

    /// Records an unpinned literal outside i32's range (see `flex_debt`).
    fn note_flex_debt(&mut self, e: ExprId) {
        if !self.flex_debt.contains(&e) {
            self.flex_debt.push(e);
        }
    }

    /// Clears one literal's flex debt (it was evaluated at a pinning type).
    fn clear_flex_debt(&mut self, e: ExprId) {
        self.flex_debt.retain(|&d| d != e);
        self.local_debt.retain(|&(_, d)| d != e);
    }

    /// Clears the flex debts a local carries (it was read at a pinning type).
    fn clear_local_debt(&mut self, name: Sym) {
        let debts: Vec<ExprId> = self.local_debt.iter().filter(|(n, _)| *n == name).map(|&(_, d)| d).collect();
        for d in debts {
            self.flex_debt.retain(|&x| x != d);
        }
        self.local_debt.retain(|(n, _)| *n != name);
    }

    /// Records a blob value this evaluation touches, raising the
    /// step cap in proportion to its length.
    fn note_blob(&mut self, v: &ConstValue) {
        match v {
            ConstValue::Bytes(b) => {
                self.extra_cap = self.extra_cap.max((b.len() as u64).saturating_mul(STEPS_PER_BLOB_BYTE));
            }
            ConstValue::Ref(inner) => self.note_blob(inner),
            _ => {}
        }
    }

    /// Rejects a named field the context calls private to this const
    /// expression's module. A no-op inside a called const fn.
    fn check_named_field<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, field: Sym, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && cx.named_field_private(adt, field) {
            let label = crate::intern::source_name(cx.sym_text(field)).to_string();
            return Err(private_field(span, &label));
        }
        Ok(())
    }

    /// Rejects a tuple field the context calls private.
    fn check_tuple_field<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, index: u32, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && cx.tuple_field_private(adt, index) {
            return Err(private_field(span, &index.to_string()));
        }
        Ok(())
    }

    /// Rejects a tuple struct constructor (call or pattern) when any
    /// of its `n` fields is private, as rustc does (E0603).
    fn check_tuple_ctor<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, n: usize, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && (0..n).any(|i| cx.tuple_field_private(adt, i as u32)) {
            return Err(private_ctor(span));
        }
        Ok(())
    }

    /// Rejects a construction or pattern the context blocks under
    /// `#[non_exhaustive]`: a struct literal, a tuple or unit
    /// constructor, or a named-field pattern without `..`. A no-op
    /// inside a called const fn, like the privacy checks.
    fn check_ne(&mut self, what: Option<&'static str>, kind: NeKind, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0
            && let Some(what) = what
        {
            return Err(match kind {
                NeKind::Lit => Diag::new(
                    "L0510",
                    span,
                    format!("cannot create non-exhaustive {what} using struct expression"),
                    "Use a constructor function the defining crate exports.",
                ),
                NeKind::Ctor => Diag::new(
                    "L0510",
                    span,
                    format!("{what} is private"),
                    "Use a constructor function the defining crate exports.",
                ),
                NeKind::Pat => Diag::new(
                    "L0510",
                    span,
                    format!("`..` required with {what} marked as non-exhaustive"),
                    "End the pattern with `..`.",
                ),
            });
        }
        Ok(())
    }

    /// The literal local (`FlexLocal`) a path expression names, as an
    /// index into `flex_locals`.
    fn flex_index<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, e: ExprId) -> Option<usize> {
        let Expr::Path(segs) = cx.ast().expr(e) else { return None };
        let [seg] = segs.as_slice() else { return None };
        let slot = env.iter().rposition(|(n, _, _, _)| *n == seg.name)?;
        self.flex_locals.iter().position(|f| f.slot == slot && f.name == seg.name)
    }

    /// True when the type of `e` is still open: it is built only from
    /// unsuffixed literals and literal locals. Pushes the groups of
    /// those locals to `out` (the caller drops them on false).
    fn flex_parts<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, e: ExprId, out: &mut Vec<u32>) -> bool {
        match cx.ast().expr(e) {
            Expr::Int(_, suffix) => suffix.is_none(),
            Expr::Path(_) => match self.flex_index(cx, env, e) {
                Some(i) => {
                    out.push(self.flex_locals[i].group);
                    true
                }
                None => false,
            },
            Expr::Unary { op: UnOp::Neg | UnOp::Not, expr } => self.flex_parts(cx, env, *expr, out),
            Expr::Binary { op, lhs, rhs } => {
                if op.is_cmp() || matches!(op, BinOp::And | BinOp::Or) {
                    false
                } else if matches!(op, BinOp::Shl | BinOp::Shr) {
                    self.flex_parts(cx, env, *lhs, out)
                } else {
                    self.flex_parts(cx, env, *lhs, out) && self.flex_parts(cx, env, *rhs, out)
                }
            }
            Expr::Block(b) => {
                let b = cx.ast().block(*b);
                b.stmts.is_empty() && b.tail.is_some_and(|t| self.flex_parts(cx, env, t, out))
            }
            _ => false,
        }
    }

    /// The literal-local groups of `e` when its type is still open,
    /// else None.
    fn flex_groups<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, e: ExprId) -> Option<Vec<u32>> {
        let mut out = Vec::new();
        self.flex_parts(cx, env, e, &mut out).then_some(out)
    }

    /// Merges literal-local groups that meet in arithmetic (inference
    /// gives them one type). Returns the merged group.
    fn unify_flex(&mut self, groups: &[u32]) -> Option<u32> {
        let &g0 = groups.first()?;
        for f in &mut self.flex_locals {
            if groups.contains(&f.group) {
                f.group = g0;
            }
        }
        Some(g0)
    }

    /// Gives every literal local of the groups the integer type `t`
    /// (see `FlexLocal`). A local still holding its literal is
    /// re-evaluated at `t`; a written one sets `rerun` and stops this run.
    fn pin_flex<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, groups: &[u32], t: Ty, span: Span) -> Result<(), Diag> {
        // A literal local is held as an i128 already; an i128 context
        // (often the wide type of another open operand) changes nothing.
        if !self.pins_to(cx, t) {
            return Ok(());
        }
        while let Some(i) = self.flex_locals.iter().position(|f| groups.contains(&f.group)) {
            let f = self.flex_locals.remove(i);
            if f.slot >= env.len() || env[f.slot].0 != f.name {
                continue;
            }
            if !self.pins.iter().any(|&(p, _)| p == f.pat) {
                self.pins.push((f.pat, t));
            }
            self.clear_local_debt(f.name);
            let Some(init) = f.init else {
                self.rerun = true;
                return Err(outside(span, "this integer local (its type is known only after a write)"));
            };
            let (v, _) = self.value(cx, env, init, Some(t))?;
            env[f.slot].1 = (v, t);
        }
        Ok(())
    }

    /// True when `t` is an integer type a literal local takes (any but
    /// i128, the type it is held at).
    fn pins_to<'a, C: ConstCx<'a>>(&self, cx: &C, t: Ty) -> bool {
        self.int_ty_of(cx, t).is_some_and(|it| it != IntTy::I128)
    }

    /// Pins the literal locals of `e` to the type `t` of the other side
    /// of an operation, when `e`'s type is still open and `other` has a
    /// type of its own. True when it pinned any.
    fn pin_against<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, other: ExprId, t: Ty, span: Span) -> Result<bool, Diag> {
        let Some(groups) = self.flex_groups(cx, env, e) else { return Ok(false) };
        if groups.is_empty() || self.flex_groups(cx, env, other).is_some() || !self.pins_to(cx, t) {
            return Ok(false);
        }
        self.pin_flex(cx, env, &groups, t, span)?;
        Ok(true)
    }

    fn int_ty_of<'a, C: ConstCx<'a>>(&self, cx: &C, t: Ty) -> Option<IntTy> {
        match cx.tys_ref().kind(t) {
            TyKind::Int(i) => Some(i),
            _ => None,
        }
    }

    fn expr<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<Flow, Diag> {
        let span = cx.ast().expr_span(e);
        self.step(span)?;
        let v = match cx.ast().expr(e) {
            Expr::Int(v, suffix) => {
                // With no expected type an unsuffixed literal stays wide
                // (i128): a const fn local takes its real type from its
                // uses, which this evaluator does not infer. The value
                // is range-checked again where it meets a declared type
                // (the item coercion in collect, the return coercion in
                // `call`), so a wide literal never escapes unchecked.
                let t = match suffix {
                    Some(s) => super::int(IntTy::from_suffix(*s)),
                    None => expected.filter(|&t| self.int_ty_of(cx, t).is_some()).unwrap_or(super::int(IntTy::I128)),
                };
                let it = self.int_ty_of(cx, t).unwrap_or(IntTy::I128);
                if *v > it.max128() {
                    return Err(Diag::new(C_OUTSIDE, span, "integer literal out of range in const", "Change the literal or the type."));
                }
                // A wide literal past i32's range owes a pinning
                // type from some later use (see `flex_debt`); an
                // evaluation at a real type settles it.
                if suffix.is_none() {
                    if expected.is_some_and(|t| self.int_ty_of(cx, t).is_some()) {
                        self.clear_flex_debt(e);
                    } else if *v > i32::MAX as u128 {
                        self.note_flex_debt(e);
                    }
                }
                (ConstValue::Int(int_from_bits(*v, it)), t)
            }
            Expr::Float(i) => {
                let text = cx.ast().strings[*i as usize].as_str();
                match crate::check::collect::parse_float_literal(text) {
                    Some((_, suffix)) => {
                        let f = suffix.unwrap_or(match expected.map(|t| cx.tys_ref().kind(t)) {
                            Some(TyKind::Float(f)) => f,
                            _ => FloatTy::F64,
                        });
                        // One rounding, straight to the target type.
                        if crate::check::collect::float_literal_overflows(text, f) {
                            return Err(Diag::new(
                                C_OUTSIDE,
                                span,
                                "float literal out of range in const",
                                "Change the literal or the type.",
                            ));
                        }
                        let Some(bits) = crate::check::collect::parse_float_literal_as(text, f) else {
                            return Err(outside(span, "this float literal"));
                        };
                        let t = cx.tys().float_ty(f);
                        (ConstValue::Float(bits, f), t)
                    }
                    None => return Err(outside(span, "this float literal")),
                }
            }
            Expr::Bool(b) => (ConstValue::Bool(*b), BOOL),
            Expr::Char(c) => (ConstValue::Char(*c), CHAR),
            Expr::Str(i) => (ConstValue::Str(*i), REF_STR),
            Expr::ByteStr(i) => {
                // One blob value for the whole literal, at its
                // `[u8; N]` array type, however large it is.
                let Some(b) = cx.ast().blobs.get(*i as usize) else {
                    return Err(outside(span, "this byte string literal"));
                };
                let b = b.clone();
                self.note_blob(&ConstValue::Bytes(b.clone()));
                let c = cx.tys().intern_const(super::ConstKind::Int(b.len() as u128));
                let t = cx.tys().intern(TyKind::Array(super::int(IntTy::U8), c));
                (ConstValue::Bytes(b), t)
            }
            Expr::Unit => (ConstValue::Unit, UNIT),
            Expr::Path(segs) => return Ok(Flow::Val(self.path_value(cx, env, segs, span, expected)?)),
            // A method body's receiver, bound as a local named `self`.
            Expr::SelfValue => {
                let Some(slot) = self.self_sym.and_then(|s| env.iter_mut().rev().find(|(n, _, _, _)| *n == s)) else {
                    return Err(outside(span, "`self` here"));
                };
                if self.move_read {
                    slot.3 = true;
                }
                return Ok(Flow::Val(slot.1.clone()));
            }
            Expr::QPath { self_ty, trait_path, segs } if segs.len() == 1 && !trait_path.is_empty() => {
                return match cx.qpath_const(*self_ty, trait_path, segs[0].name) {
                    Some(v) => Ok(Flow::Val(v)),
                    None => Err(outside(span, "this path")),
                };
            }
            // `<u64>::MAX`: an inherent const of a primitive by its
            // qualified form.
            Expr::QPath { self_ty, trait_path, segs } if segs.len() == 1 && trait_path.is_empty() => {
                let t = cx.resolve_ty(*self_ty);
                let item = segs[0].name;
                let v = match cx.tys_ref().kind(t) {
                    TyKind::Int(it) => self.int_assoc_const(cx, it.name(), cx.sym_text(item)),
                    TyKind::Char => self.char_assoc_const(cx, item),
                    TyKind::Float(f) => match primitive_float_assoc(f, cx.sym_text(item)) {
                        Some((bits, None)) => Some((ConstValue::Float(bits, f), t)),
                        Some((v, Some(it))) => Some((ConstValue::Int(v as i128), super::int(it))),
                        None => None,
                    },
                    _ => None,
                };
                return v.map(Flow::Val).ok_or_else(|| outside(span, "this path"));
            }
            Expr::Block(b) => return self.block(cx, env, *b, expected),
            Expr::ConstBlock(b) => {
                // An inline const is an item of its own: its tail
                // borrows extend into its value.
                self.mark_extending(cx, e);
                // An inline const with no expected type pins its own
                // literals: Rust falls back to i32 there, not i128.
                if expected.is_none() && flex_int_expr(cx.ast(), e) {
                    return self.block(cx, env, *b, Some(super::I32));
                }
                return self.block(cx, env, *b, expected);
            }
            // A range with bounds (`35..=64`, `2..5`, `3..`, `..=9`): the
            // value lowering builds for it, its bounds then (inclusive) the
            // `exhausted` flag; materialized by lower.rs
            // `const_builtin_aggregate`.
            Expr::Range { lo, hi, inclusive } if lo.is_some() || hi.is_some() => {
                use crate::ty::iter::{IterKind, iter_parts, mk_iter};
                let exp_elem = expected.and_then(|t| iter_parts(cx.tys_ref(), t)).and_then(|(_, a)| a.first().copied());
                let mut vals = Vec::new();
                let mut elem = exp_elem;
                for b in [lo, hi].into_iter().flatten() {
                    let (v, t) = self.value(cx, env, *b, elem)?;
                    if !matches!(cx.tys_ref().kind(t), TyKind::Int(_) | TyKind::Char) {
                        return Err(outside(cx.ast().expr_span(*b), "this range bound"));
                    }
                    if elem.is_some_and(|w| w != t) {
                        return Err(const_ty_mismatch(cx.ast().expr_span(*b), "this range bound"));
                    }
                    elem = Some(t);
                    vals.push(v);
                }
                let k = match (lo.is_some(), hi.is_some(), *inclusive) {
                    (true, true, true) => IterKind::RangeInclusive,
                    (true, true, false) => IterKind::Range,
                    (true, false, _) => IterKind::RangeFrom,
                    (false, true, true) => IterKind::RangeToInclusive,
                    (false, true, false) => IterKind::RangeTo,
                    (false, false, _) => unreachable!(),
                };
                if k == IterKind::RangeInclusive {
                    vals.push(ConstValue::Bool(false));
                }
                let et = elem.unwrap_or(ERROR);
                (ConstValue::Aggregate(vals), mk_iter(cx.tys(), k, &[et]))
            }
            Expr::Tuple(elems) => {
                let exp: Vec<Option<Ty>> = match expected.map(|t| cx.tys_ref().kind(t)) {
                    Some(TyKind::Tuple(ts)) => cx.tys_ref().tys_of(ts).iter().map(|&t| Some(t)).collect(),
                    _ => vec![None; elems.len()],
                };
                let mut vals = Vec::new();
                let mut tys = Vec::new();
                for (i, &el) in elems.iter().enumerate() {
                    let (v, t) = self.value_moved(cx, env, el, exp.get(i).copied().flatten())?;
                    vals.push(v);
                    tys.push(t);
                }
                let ts = cx.tys().intern_tys(&tys);
                (ConstValue::Aggregate(vals), cx.tys().intern(TyKind::Tuple(ts)))
            }
            Expr::Array(elems) => {
                // A slice expectation is the backing array of `&[..]` at a
                // slice type: its elements want the slice's element.
                let exp_elem = expected.and_then(|t| match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    _ => None,
                });
                let mut vals = Vec::new();
                let mut elem_ty = exp_elem;
                for &el in elems {
                    let (v, t) = self.value_moved(cx, env, el, elem_ty)?;
                    elem_ty = Some(t);
                    vals.push(v);
                }
                let elem = elem_ty.unwrap_or(ERROR);
                let c = cx.tys().intern_const(super::ConstKind::Int(elems.len() as u128));
                (ConstValue::Aggregate(vals), cx.tys().intern(TyKind::Array(elem, c)))
            }
            Expr::ArrayRepeat { value, len } => {
                let (nv, _) = self.value(cx, env, *len, Some(USIZE))?;
                let ConstValue::Int(n) = nv else { return Err(outside(span, "this array length")) };
                let n = u64::try_from(n).map_err(|_| outside(span, "this array length"))?;
                let exp_elem = expected.and_then(|t| match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    _ => None,
                });
                // Every repeat evaluates its operand once. A const
                // item or inline const operand is re-evaluated per
                // element by the compiler, so it is never copied or
                // dropped here; any other operand materializes one
                // value that the repeat then copies (above length 1)
                // or drops (length 0).
                let (v, t) = self.value_moved(cx, env, *value, exp_elem)?;
                let operand_local = match cx.ast().expr(*value) {
                    Expr::Path(segs) if segs.len() == 1 => env.iter().any(|(name, _, _, _)| *name == segs[0].name),
                    _ => false,
                };
                let operand_static = match cx.ast().expr(*value) {
                    Expr::Path(segs) if segs.len() == 1 && !operand_local => cx.static_item(segs[0].name, span).is_some(),
                    _ => false,
                };
                if operand_static && !cx.is_copy(t) {
                    return Err(Diag::new(
                        "L0110",
                        span,
                        "cannot move out of a static item",
                        "A repeat of a non-`Copy` static value would move it; use a const item instead.",
                    ));
                }
                let operand_const = match cx.ast().expr(*value) {
                    Expr::ConstBlock(_) => true,
                    Expr::Path(segs) => {
                        !operand_local
                            && !operand_static
                            && match segs.as_slice() {
                                [s] => cx.const_item(s.name, span).is_some(),
                                _ => cx.assoc_const_item(segs).is_some(),
                            }
                    }
                    _ => false,
                };
                if n == 0 {
                    // A materialized operand is dropped at once, so
                    // a drop operand is E0493 here (a const operand
                    // and a unit variant make no temporary).
                    let materializes = match cx.ast().expr(*value) {
                        Expr::ConstBlock(_) => false,
                        Expr::Path(_) | Expr::QPath { .. } => operand_local,
                        _ => true,
                    };
                    if materializes && cx.needs_drop(t) {
                        return Err(drop_diag(cx, t, span));
                    }
                    let elem = exp_elem.unwrap_or(t);
                    let c = cx.tys().intern_const(super::ConstKind::Int(0));
                    (ConstValue::Aggregate(Vec::new()), cx.tys().intern(TyKind::Array(elem, c)))
                } else {
                    // Above length 1 a repeat duplicates its operand:
                    // it must be `Copy`, or a const operand as above.
                    // A const fn call makes one value, so it needs
                    // `Copy` like any other operand (rustc E0277).
                    if n > 1 && !cx.is_copy(t) && !operand_const {
                        return Err(Diag::new(
                            "L0110",
                            span,
                            "the trait `Copy` is not implemented for this type",
                            "Array repeat with a length above 1 needs a Copy element, a const item, or write the elements out.",
                        ));
                    }
                    let c = cx.tys().intern_const(super::ConstKind::Int(n as u128));
                    (ConstValue::Repeat(Box::new(v), n), cx.tys().intern(TyKind::Array(t, c)))
                }
            }
            Expr::Unary { op, expr } => {
                // A negated literal is range-checked after the negation,
                // so `-128` is a valid i8: check the magnitude against
                // the type's minimum, not its maximum.
                if *op == UnOp::Neg
                    && let Expr::Int(v, suffix) = cx.ast().expr(*expr)
                {
                    let (v, suffix) = (*v, *suffix);
                    let t = match suffix {
                        Some(s) => super::int(IntTy::from_suffix(s)),
                        None => expected.filter(|&t| self.int_ty_of(cx, t).is_some()).unwrap_or(super::int(IntTy::I128)),
                    };
                    let it = self.int_ty_of(cx, t).unwrap_or(IntTy::I128);
                    if !it.signed() || v > it.max128() + 1 {
                        return Err(Diag::new(
                            C_OUTSIDE,
                            span,
                            "integer literal out of range in const",
                            "Change the literal or the type.",
                        ));
                    }
                    let r = if v == (1u128 << 127) { i128::MIN } else { -(v as i128) };
                    if suffix.is_none() {
                        if expected.is_some_and(|t| self.int_ty_of(cx, t).is_some()) {
                            self.clear_flex_debt(*expr);
                        } else if v > (i32::MAX as u128) + 1 {
                            self.note_flex_debt(*expr);
                        }
                    }
                    (ConstValue::Int(r), t)
                } else {
                    let (v, t) = self.value(cx, env, *expr, expected)?;
                    match (op, v) {
                        (UnOp::Neg, ConstValue::Float(bits, f)) => {
                            let nb = match f {
                                FloatTy::F64 => (-f64::from_bits(bits)).to_bits(),
                                FloatTy::F32 => (-f32::from_bits(bits as u32)).to_bits() as u64,
                            };
                            (ConstValue::Float(nb, f), t)
                        }
                        (UnOp::Neg, ConstValue::Int(i)) => {
                            let it = self.int_ty_of(cx, t);
                            if let Some(it) = it
                                && (!it.signed() || i == int_min(it))
                            {
                                return Err(outside(span, "this negation (overflow)"));
                            }
                            let r = i.checked_neg().ok_or_else(|| outside(span, "this negation (overflow)"))?;
                            (ConstValue::Int(r), t)
                        }
                        (UnOp::Not, ConstValue::Int(i)) => {
                            let r = match self.int_ty_of(cx, t) {
                                Some(it) => int_from_bits(!int_bits(i, it), it),
                                None => !i,
                            };
                            (ConstValue::Int(r), t)
                        }
                        (UnOp::Not, ConstValue::Bool(b)) => (ConstValue::Bool(!b), BOOL),
                        _ => return Err(outside(span, "this unary operation")),
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => return Ok(Flow::Val(self.binary(cx, env, *op, *lhs, *rhs, expected, span)?)),
            Expr::Cast { expr, ty } => {
                let target = cx.resolve_ty(*ty);
                // An unsuffixed literal takes its type from the cast
                // target, so `300 as u8` is out of range, not 44. A
                // wider unpinned expression keeps the i32 fallback,
                // so `(2147483648 >> 7) as i64` is out of range too.
                let exp = if is_unsuffixed_lit(cx.ast(), *expr) {
                    Some(target)
                } else if flex_int_expr(cx.ast(), *expr) {
                    Some(super::I32)
                } else {
                    None
                };
                let v = self.value(cx, env, *expr, exp)?;
                return Ok(Flow::Val(self.cast(cx, v, target, span)?));
            }
            Expr::Ref { expr, mutable, .. } => {
                // An extending `&mut` is part of the final value, which
                // `check_final_refs` rejects (rustc E0764).
                if *mutable && self.mut_arg.take() != Some(e) && !self.extending.contains(&e) {
                    return Err(mut_ref_outside(span, "a `&mut` borrow that is not a const fn call argument"));
                }
                // `&STATIC` and `&CONST` keep their identity where the caller
                // can use it; anything else is a promoted temporary.
                if let Expr::Path(segs) = cx.ast().expr(*expr)
                    && segs.len() == 1
                    && let Some((idx, sty)) = cx.static_item(segs[0].name, cx.ast().expr_span(*expr))
                {
                    // `&ARR` where a slice reference is wanted is the unsize
                    // coercion; the value keeps the static's identity and the
                    // wanted type.
                    if let Some(et) = expected
                        && matches!(cx.tys_ref().kind(et), TyKind::Ref(..))
                        && {
                            let rt = cx.tys().mk_ref(*mutable, sty);
                            const_ty_compatible(cx.tys_ref(), rt, et)
                        }
                    {
                        return Ok(Flow::Val((ConstValue::StaticRef(idx), et)));
                    }
                    let rt = cx.tys().mk_ref(*mutable, sty);
                    return Ok(Flow::Val((ConstValue::StaticRef(idx), rt)));
                }
                // A wanted reference type wants its pointee type inside, so an
                // unsuffixed literal takes that width (except the slice form
                // below, which has no single pointee value). The operand of
                // `&` is no coercion site: a wanted `&[T]` pointee is not
                // passed in, so `&&[1]` stays no `&&[u8]`, as in rustc.
                let slice_ref = |t: Ty| matches!(cx.tys_ref().kind(t), TyKind::Ref(_, _, s) if matches!(cx.tys_ref().kind(s), TyKind::Slice(_)));
                let inner_expected = expected.and_then(|et| match cx.tys_ref().kind(et) {
                    TyKind::Ref(_, _, inner) if !slice_ref(inner) => Some(inner),
                    _ => None,
                });
                // A borrow of a drop temporary lives on only when the
                // borrow is extending: then the temporary (for a
                // projection, its root value) is part of the final
                // value. Any other one is dropped at its statement's
                // end (E0493). A borrow of a place drops with its
                // owner, judged at that scope's end instead.
                let extended = self.extending.contains(&e);
                if extended {
                    self.ext_roots.insert(projection_root(cx.ast(), *expr));
                }
                let (v, t) = self.value_place(cx, env, *expr, inner_expected)?;
                if !extended && !self.is_place(cx, env, *expr) && cx.needs_drop(t) {
                    return Err(drop_diag(cx, t, span));
                }
                // A str value stands for a `str` place behind `*s` or
                // `s[..]`, whose borrow is the `&str` itself; a borrow of
                // any other `&str` value (`&"ab"`) is a `&&str`.
                let str_place = matches!(cx.ast().expr(*expr), Expr::Deref(_) | Expr::Index { .. });
                let (v, rt) = if let ConstValue::Str(_) | ConstValue::StrBytes(_) = v
                    && str_place
                {
                    return Ok(Flow::Val((v, t)));
                } else if let Some(et) = expected
                    && let TyKind::Ref(_, _, s) = cx.tys_ref().kind(et)
                    && let TyKind::Slice(want) = cx.tys_ref().kind(s)
                    && matches!(v, ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Bytes(_))
                {
                    // `&[1, 2]` at a slice type: the aggregate is the slice
                    // backing; materialization builds the fat value. Its
                    // elements must fit the slice's (array elements are
                    // coercion sites): `&[true]` is no `&[u8]`.
                    let fits = match cx.tys_ref().kind(t) {
                        TyKind::Array(el, _) | TyKind::Slice(el) => const_ty_compatible(cx.tys_ref(), el, want),
                        _ => false,
                    };
                    if !fits {
                        return Err(const_ty_mismatch(span, "this slice element"));
                    }
                    (v, et)
                } else {
                    let rt = cx.tys().mk_ref(*mutable, t);
                    (ConstValue::Ref(Box::new(v)), rt)
                };
                // A borrow of a place inside a static points into that
                // static's storage (`&TABLE[i]`, `&S.f`), not at a copy.
                if !*mutable
                    && let Some((idx, path, _)) = self.static_place(cx, env, *expr)?
                {
                    let v = if path.is_empty() { ConstValue::StaticRef(idx) } else { ConstValue::StaticPlace(idx, path.into()) };
                    return Ok(Flow::Val((v, rt)));
                }
                (v, rt)
            }
            Expr::Deref(inner) => {
                let (v, t) = self.value_place(cx, env, *inner, None)?;
                match v {
                    ConstValue::Ref(_) | ConstValue::StaticRef(_) | ConstValue::StaticPlace(..) => match self.deref_value(cx, v, t) {
                        // Unchanged: a static the context cannot read.
                        (_, dt) if dt == t => return Err(outside(span, "this dereference")),
                        got => got,
                    },
                    ConstValue::Str(i) => (ConstValue::Str(i), t),
                    ConstValue::StrBytes(b) => (ConstValue::StrBytes(b), t),
                    _ => return Err(outside(span, "this dereference")),
                }
            }
            Expr::Field { base, name } => {
                let (v, t) = self.value_place(cx, env, *base, None)?;
                self.check_temp_drop(cx, env, *base, t, span)?;
                let (v, t) = self.auto_deref(cx, v, t);
                let Some(adt) = cx.tys_ref().local_adt(t) else { return Err(outside(span, "this field access")) };
                self.check_named_field(cx, adt, *name, span)?;
                let fields = cx.variant_fields(adt, 0);
                let Some(i) = fields.iter().position(|(n, _)| n == name) else {
                    return Err(outside(span, "this field access"));
                };
                match v {
                    ConstValue::Aggregate(vals) => (vals.into_iter().nth(i).unwrap(), fields[i].1),
                    _ => return Err(outside(span, "this field access")),
                }
            }
            Expr::TupleField { base, index } => {
                let (v, t) = self.value_place(cx, env, *base, None)?;
                self.check_temp_drop(cx, env, *base, t, span)?;
                let (v, t) = self.auto_deref(cx, v, t);
                if !matches!(cx.tys_ref().kind(t), TyKind::Tuple(_))
                    && let Some(adt) = cx.tys_ref().local_adt(t)
                {
                    self.check_tuple_field(cx, adt, *index, span)?;
                }
                let elem_ty = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).get(*index as usize).copied(),
                    _ => cx.tys_ref().local_adt(t).and_then(|a| cx.variant_fields(a, 0).get(*index as usize).map(|f| f.1)),
                };
                match (v, elem_ty) {
                    (ConstValue::Aggregate(vals), Some(et)) => {
                        (vals.into_iter().nth(*index as usize).ok_or_else(|| outside(span, "this field access"))?, et)
                    }
                    _ => return Err(outside(span, "this field access")),
                }
            }
            Expr::Index { base, index } => {
                // A range index stays outside: rustc rejects it in
                // const too (the `Index` trait is not const-stable,
                // E0658); slice patterns and `split_at` are the const
                // slicing forms. It falls through to the outside error.
                // A local base is read in place: cloning a large array
                // (an `include_bytes!` blob) per element read would make
                // a loop over it quadratic (W-CHECK-G3).
                if let Some(got) = self.index_local(cx, env, *base, *index, span)? {
                    return Ok(Flow::Val(got));
                }
                if let Some(got) = self.index_item(cx, env, *base, *index, span)? {
                    return Ok(Flow::Val(got));
                }
                let (v, t) = self.value_place(cx, env, *base, None)?;
                self.check_temp_drop(cx, env, *base, t, span)?;
                let (v, t) = self.auto_deref(cx, v, t);
                let (iv, _) = self.value(cx, env, *index, Some(USIZE))?;
                let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
                let i = usize::try_from(i).map_err(|_| outside(span, "this index"))?;
                // A slice value at a `&[T]` type is its backing
                // aggregate, so an index reads the type through the
                // reference as well as off an array or slice directly.
                let elem = match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => el,
                    TyKind::Ref(_, _, inner) => match cx.tys_ref().kind(inner) {
                        TyKind::Array(el, _) | TyKind::Slice(el) => el,
                        _ => return Err(outside(span, "this index")),
                    },
                    _ => return Err(outside(span, "this index")),
                };
                let got = match v {
                    ConstValue::Aggregate(vals) => vals.into_iter().nth(i),
                    ConstValue::Repeat(v, n) if (i as u64) < n => Some(*v),
                    ConstValue::Bytes(b) => b.as_slice().get(i).map(|&x| ConstValue::Int(x as i128)),
                    _ => None,
                };
                match got {
                    Some(g) => (g, elem),
                    None => return Err(outside(span, "this index (out of bounds)")),
                }
            }
            Expr::StructLit { path, fields, update } => {
                let Some((adt, variant, ty)) = cx.struct_target(path) else {
                    return Err(outside(span, "this struct literal"));
                };
                // A generic struct literal is the expected instance of
                // its Adt (`static S: K<u8> = K { .. }`); check typed it.
                // Written type args (`K::<u16> { .. }`) are not matched
                // against it: such a literal keeps the template type.
                let def_of = |t: Ty| cx.tys_ref().adt_parts(t).map(|(d, _)| d);
                let written_args = path.iter().any(|s| !s.type_args().is_empty());
                let (ty, inst) = match expected {
                    Some(t) if !written_args && def_of(t).is_some() && def_of(t) == def_of(ty) => {
                        let args = cx.tys_ref().adt_parts(t).map(|(_, a)| cx.tys_ref().args(a).to_vec()).unwrap_or_default();
                        (t, Some(args))
                    }
                    _ => (ty, None),
                };
                // Field types of the instance: the template's, with its args.
                let mut field_defs = cx.variant_fields(adt, variant);
                if let Some(args) = &inst {
                    for f in &mut field_defs {
                        f.1 = super::subst(cx.tys(), f.1, args);
                    }
                }
                // Privacy first: written fields, and every field when
                // `..base` fills the rest (rustc E0451 for both).
                let ne_what = cx.ne_lit_what(adt, variant);
                self.check_ne(ne_what, NeKind::Lit, span)?;
                for &(fname, fspan, _) in fields {
                    self.check_named_field(cx, adt, fname, fspan)?;
                }
                if update.is_some() {
                    for &(fname, _) in &field_defs {
                        self.check_named_field(cx, adt, fname, span)?;
                    }
                }
                let mut vals: Vec<Option<ConstValue>> = vec![None; field_defs.len()];
                for &(fname, _, fe) in fields {
                    let Some(i) = field_defs.iter().position(|(n, _)| *n == fname) else {
                        return Err(outside(span, "this struct literal"));
                    };
                    let (v, vt) = self.value_moved(cx, env, fe, Some(field_defs[i].1))?;
                    if !const_ty_compatible(cx.tys_ref(), vt, field_defs[i].1) {
                        return Err(const_ty_mismatch(cx.ast().expr_span(fe), "this struct literal field"));
                    }
                    vals[i] = Some(v);
                }
                if let Some(u) = update {
                    let (bv, _) = self.value_moved(cx, env, *u, Some(ty))?;
                    let bvals = match bv {
                        ConstValue::Aggregate(bvals) => Some(bvals),
                        ConstValue::Variant(_, bvals) => Some(bvals),
                        _ => None,
                    };
                    if let Some(bvals) = bvals {
                        for (i, b) in bvals.into_iter().enumerate() {
                            if vals.get(i).is_some_and(|v| v.is_none()) {
                                vals[i] = Some(b);
                            }
                        }
                    }
                }
                let vals: Option<Vec<ConstValue>> = vals.into_iter().collect();
                match vals {
                    Some(vals) if cx.tys_ref().local_adt(ty).is_some() => {
                        // A struct-like enum variant keeps its variant;
                        // an aggregate would silently become variant 0.
                        if cx.is_enum(adt) { (ConstValue::Variant(variant, vals), ty) } else { (ConstValue::Aggregate(vals), ty) }
                    }
                    _ => return Err(outside(span, "this struct literal")),
                }
            }
            Expr::OffsetOf { ty, fields } => {
                let mut cur = cx.resolve_ty(*ty);
                let mut off: u64 = 0;
                for &ffield in fields {
                    let Some(adt) = cx.tys_ref().local_adt(cur) else {
                        return Err(outside(span, "this `offset_of!`"));
                    };
                    if !matches!(
                        cx.adt_repr(adt).kind,
                        super::layout::ReprKind::C | super::layout::ReprKind::Transparent
                    ) && cx.adt_repr(adt).pack.is_none()
                    {
                        return Err(Diag::new(
                            "L0650",
                            span,
                            "`offset_of!` on a default-repr type is not supported",
                            "Add `#[repr(C)]` to the type, or measure with `size_of`.",
                        ));
                    }
                    let defs = cx.variant_fields(adt, 0);
                    // Tuple field defs carry their index text as the name.
                    let found = match ffield {
                        crate::ast::OffsetField::Name(fname) => defs.iter().position(|(n, _)| *n == fname),
                        crate::ast::OffsetField::Index(idx) => {
                            if (idx as usize) < defs.len() && cx.sym_text(defs[idx as usize].0).parse::<u32>() == Ok(idx) {
                                Some(idx as usize)
                            } else {
                                None
                            }
                        }
                    };
                    let Some(i) = found else {
                        return Err(outside(span, "this `offset_of!` field"));
                    };
                    match ffield {
                        crate::ast::OffsetField::Name(fname) => self.check_named_field(cx, adt, fname, span)?,
                        crate::ast::OffsetField::Index(idx) => self.check_tuple_field(cx, adt, idx, span)?,
                    }
                    let Some(l) = cx.layout(cur) else {
                        return Err(Diag::new(
                            "L0652",
                            span,
                            "unsupported layout form in `offset_of!`",
                            "Use a type inside the supported layout grammar.",
                        ));
                    };
                    off += l.field_offsets.get(i).copied().unwrap_or(0);
                    cur = defs[i].1;
                }
                (ConstValue::Int(off as i128), USIZE)
            }
            Expr::Call { callee, args } => return Ok(Flow::Val(self.call(cx, env, *callee, args, span, expected)?)),
            // Only primitive methods evaluate today (`method_call`
            // below). If user const methods land: run the method
            // body with `call_depth` raised, as the ConstFn call
            // arm does, so its field accesses are not privacy
            // checked against the caller's module.
            Expr::MethodCall { recv, name, args, .. } => {
                return Ok(Flow::Val(self.method_call(cx, env, *recv, *name, args, expected, span)?));
            }
            Expr::If { cond, then, els } => {
                // `if let pat = scrut { .. }`: the bindings live in
                // the then block only.
                if let Expr::Let { pat, scrut } = cx.ast().expr(*cond) {
                    let (pat, scrut) = (*pat, *scrut);
                    let (sv, st) = self.value_moved(cx, env, scrut, None)?;
                    if cx.needs_drop(st) && pat_destructures(cx.ast(), pat) {
                        return Err(drop_diag(cx, st, span));
                    }
                    let mut binds = Vec::new();
                    if self.match_pat(cx, env, pat, &sv, st, true, &mut binds)? {
                        let saved = env.len();
                        env.extend(binds);
                        let r = self.block(cx, env, *then, expected);
                        if r.is_ok() {
                            self.check_scope_drops(cx, env, saved, span)?;
                        }
                        env.truncate(saved);
                        if r.is_ok()
                            && let Some(els) = els
                        {
                            self.scan_dead_expr(cx, env, *els)?;
                        }
                        return r;
                    }
                    let denv = self.dead_env(cx, env, pat, st);
                    self.scan_dead_block(cx, &denv, *then)?;
                    match els {
                        Some(els) => return self.expr(cx, env, *els, expected),
                        None => (ConstValue::Unit, UNIT),
                    }
                } else {
                    let (cv, _) = self.value(cx, env, *cond, Some(BOOL))?;
                    let ConstValue::Bool(b) = cv else { return Err(outside(span, "this condition")) };
                    if b {
                        let r = self.block(cx, env, *then, expected);
                        if r.is_ok()
                            && let Some(els) = els
                        {
                            self.scan_dead_expr(cx, env, *els)?;
                        }
                        return r;
                    }
                    match els {
                        Some(els) => {
                            let r = self.expr(cx, env, *els, expected);
                            if r.is_ok() {
                                self.scan_dead_block(cx, env, *then)?;
                            }
                            return r;
                        }
                        None => {
                            self.scan_dead_block(cx, env, *then)?;
                            (ConstValue::Unit, UNIT)
                        }
                    }
                }
            }
            Expr::Match { scrut, arms } => return self.match_expr(cx, env, *scrut, arms, expected, span),
            Expr::While { label, cond, body } => {
                let mut first = true;
                loop {
                    self.step(span)?;
                    // `while let pat = scrut { .. }`: bindings are
                    // fresh per iteration and live in the body.
                    let saved = env.len();
                    let mut dead_pat = None;
                    let go = if let Expr::Let { pat, scrut } = cx.ast().expr(*cond) {
                        let (pat, scrut) = (*pat, *scrut);
                        let (sv, st) = self.value_moved(cx, env, scrut, None)?;
                        if cx.needs_drop(st) && pat_destructures(cx.ast(), pat) {
                            return Err(drop_diag(cx, st, span));
                        }
                        let mut binds = Vec::new();
                        let m = self.match_pat(cx, env, pat, &sv, st, true, &mut binds)?;
                        if m {
                            env.extend(binds);
                        }
                        dead_pat = Some((pat, st));
                        m
                    } else {
                        let (cv, _) = self.value(cx, env, *cond, Some(BOOL))?;
                        let ConstValue::Bool(b) = cv else { return Err(outside(span, "this condition")) };
                        b
                    };
                    if !go {
                        env.truncate(saved);
                        // A body that never runs still drops its
                        // locals in rustc's static check.
                        if first {
                            match dead_pat {
                                Some((pat, st)) => {
                                    let denv = self.dead_env(cx, env, pat, st);
                                    self.scan_dead_block(cx, &denv, *body)?;
                                }
                                None => self.scan_dead_block(cx, env, *body)?,
                            }
                        }
                        break;
                    }
                    first = false;
                    let flow = self.block(cx, env, *body, Some(UNIT));
                    if flow.is_ok() {
                        self.check_scope_drops(cx, env, saved, span)?;
                    }
                    env.truncate(saved);
                    match flow? {
                        Flow::Val(_) => {}
                        Flow::Continue(l) if l.is_none() || l == label.map(|x| x.name) => {}
                        Flow::Break(_, l) if l.is_none() || l == label.map(|x| x.name) => break,
                        other => return Ok(other),
                    }
                }
                (ConstValue::Unit, UNIT)
            }
            Expr::Loop { label, body } => loop {
                self.step(span)?;
                match self.block(cx, env, *body, Some(UNIT))? {
                    Flow::Val(_) => {}
                    Flow::Continue(l) if l.is_none() || l == label.map(|x| x.name) => {}
                    Flow::Break(v, l) if l.is_none() || l == label.map(|x| x.name) => {
                        break v.unwrap_or((ConstValue::Unit, UNIT));
                    }
                    other => return Ok(other),
                }
            },
            Expr::Break { label, value } => {
                let v = match value {
                    Some(v) => Some(self.value_moved(cx, env, *v, None)?),
                    None => None,
                };
                return Ok(Flow::Break(v, label.map(|l| l.name)));
            }
            Expr::Continue(label) => return Ok(Flow::Continue(label.map(|l| l.name))),
            Expr::Return(v) => {
                let v = match v {
                    Some(v) => self.value_moved(cx, env, *v, None)?,
                    None => (ConstValue::Unit, UNIT),
                };
                return Ok(Flow::Return(v));
            }
            Expr::Assign { lhs, rhs } => {
                // A whole integer local gives the value its type.
                let place_int = match cx.ast().expr(*lhs) {
                    Expr::Path(segs) if segs.len() == 1 && self.flex_index(cx, env, *lhs).is_none() => {
                        env.iter().rev().find(|(n, _, _, _)| *n == segs[0].name).map(|s| s.1.1).filter(|&t| t != super::int(IntTy::I128) && self.int_ty_of(cx, t).is_some())
                    }
                    _ => None,
                };
                let (v, vt) = self.value_moved(cx, env, *rhs, place_int)?;
                // Writing a literal local: a typed value pins it; an open
                // one joins its group and is what the slot now holds.
                if let Some(i) = self.flex_index(cx, env, *lhs) {
                    let g = self.flex_locals[i].group;
                    match self.flex_groups(cx, env, *rhs) {
                        None => self.pin_flex(cx, env, &[g], vt, span)?,
                        Some(gs) => {
                            self.unify_flex(&[vec![g], gs].concat());
                            if let Some(i) = self.flex_index(cx, env, *lhs) {
                                self.flex_locals[i].init = pure_int_lit(cx.ast(), *rhs).then_some(*rhs);
                            }
                        }
                    }
                }
                self.assign_place(cx, env, *lhs, v, span)?;
                (ConstValue::Unit, UNIT)
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let shift = matches!(op, BinOp::Shl | BinOp::Shr);
                // `x op= y` on a literal local: a typed `y` pins it (not
                // a shift amount); otherwise the result is a write.
                let mut flex_rv = None;
                if let Some(i) = self.flex_index(cx, env, *lhs) {
                    let g = self.flex_locals[i].group;
                    let (rv, rt) = self.value(cx, env, *rhs, None)?;
                    match self.flex_groups(cx, env, *rhs) {
                        None if !shift => self.pin_flex(cx, env, &[g], rt, span)?,
                        gs => {
                            if !shift {
                                self.unify_flex(&[vec![g], gs.unwrap_or_default()].concat());
                            }
                            if let Some(i) = self.flex_index(cx, env, *lhs) {
                                self.flex_locals[i].init = None;
                            }
                        }
                    }
                    flex_rv = Some(rv);
                }
                let cur = self.value(cx, env, *lhs, None)?;
                let rv = match flex_rv {
                    Some(rv) => rv,
                    None if shift && self.flex_groups(cx, env, *rhs).is_some_and(|g| !g.is_empty()) => self.value(cx, env, *rhs, None)?.0,
                    None => self.value(cx, env, *rhs, Some(cur.1))?.0,
                };
                let ct = cur.1;
                let out = self.int_op(cx, *op, cur, (rv, ct), span)?;
                self.assign_place(cx, env, *lhs, out.0, span)?;
                (ConstValue::Unit, UNIT)
            }
            Expr::Macro { kind, args, fmt, .. } => return Ok(Flow::Val(self.macro_(cx, env, *kind, args, fmt, span)?)),
            Expr::LabeledBlock { label, body } => match self.block(cx, env, *body, expected)? {
                Flow::Break(v, l) if l == Some(label.name) => v.unwrap_or((ConstValue::Unit, UNIT)),
                Flow::Val(v) => v,
                other => return Ok(other),
            },
            Expr::Closure { .. } if expected.is_some_and(|t| matches!(cx.tys_ref().kind(t), TyKind::FnPtr(_))) => match cx.closure_value(e, expected.unwrap()) {
                Some(v) => v,
                None => return Err(outside(span, "this expression")),
            },
            _ => return Err(outside(span, "this expression")),
        };
        Ok(Flow::Val(v))
    }

    /// Evaluates an expression whose value moves into its parent
    /// (a call argument, an aggregate element, a `let` initializer):
    /// a local read inside it marks that local moved.
    fn value_moved<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
        let prev = self.move_read;
        self.move_read = true;
        let r = self.value(cx, env, e, expected);
        self.move_read = prev;
        r
    }

    /// Evaluates a place read (a field or index base, a borrow's
    /// operand): never a move, whatever the parent does.
    fn value_place<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
        let prev = self.move_read;
        self.move_read = false;
        let r = self.value(cx, env, e, expected);
        self.move_read = prev;
        r
    }

    /// The E0493 check at a scope's end: a local of a drop type
    /// that was not moved out is destroyed here.
    fn check_scope_drops<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, saved: usize, span: Span) -> Result<(), Diag> {
        for (_, v, _, moved) in &env[saved..] {
            if !moved && cx.needs_drop(v.1) {
                return Err(drop_diag(cx, v.1, span));
            }
        }
        Ok(())
    }

    /// The E0493 check for a projected or borrowed temporary: a
    /// new value of a drop type used as a field, index, or method
    /// base is destroyed when its statement ends, unless an
    /// extending borrow keeps it (`ext_roots`).
    fn check_temp_drop<'a, C: ConstCx<'a>>(&self, cx: &mut C, env: &Env, base: ExprId, base_ty: Ty, span: Span) -> Result<(), Diag> {
        if !self.ext_roots.contains(&base) && !self.is_place(cx, env, base) && cx.needs_drop(base_ty) {
            return Err(drop_diag(cx, base_ty, span));
        }
        Ok(())
    }

    /// True when `e` names an existing value (a local, a static, or a
    /// projection) instead of making a temporary. A const item path is
    /// a value: each use makes a fresh copy of the const.
    fn is_place<'a, C: ConstCx<'a>>(&self, cx: &mut C, env: &Env, e: ExprId) -> bool {
        match cx.ast().expr(e) {
            Expr::Path(segs) => {
                let [seg] = segs.as_slice() else { return false };
                let name = seg.name;
                env.iter().any(|(n, _, _, _)| *n == name) || cx.static_item(name, cx.ast().expr_span(e)).is_some()
            }
            Expr::QPath { .. } => false,
            _ => is_place_expr(cx.ast(), e),
        }
    }

    /// Marks the extending borrows of a const item or inline const
    /// whose value is `e` (rustc's temporary lifetime extension): the
    /// value itself, the operand of an extending borrow or cast, the
    /// elements of a tuple, array, struct literal, or tuple
    /// constructor call, a block's tail, and `if` and `match` arm
    /// values. A `let` inside the item does not extend to the item.
    fn mark_extending<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, e: ExprId) {
        let ast = cx.ast();
        match ast.expr(e).clone() {
            Expr::Ref { raw: false, expr, .. } => {
                self.extending.insert(e);
                self.mark_extending(cx, expr);
            }
            Expr::Cast { expr, .. } => self.mark_extending(cx, expr),
            Expr::Tuple(es) | Expr::Array(es) => {
                for x in es {
                    self.mark_extending(cx, x);
                }
            }
            Expr::StructLit { fields, .. } => {
                for (_, _, x) in fields {
                    self.mark_extending(cx, x);
                }
            }
            Expr::Call { callee, args } => {
                if matches!(cx.call_target(callee), CallTarget::VariantCtor { .. }) {
                    for x in args {
                        self.mark_extending(cx, x);
                    }
                }
            }
            Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::ConstBlock(b) => {
                if let Some(t) = ast.block(b).tail {
                    self.mark_extending(cx, t);
                }
            }
            Expr::If { then, els, .. } => {
                if let Some(t) = ast.block(then).tail {
                    self.mark_extending(cx, t);
                }
                if let Some(x) = els {
                    self.mark_extending(cx, x);
                }
            }
            Expr::Match { arms, .. } => {
                for arm in arms {
                    self.mark_extending(cx, arm.body);
                }
            }
            _ => {}
        }
    }

    /// Evaluates a branch the live path did not take, only to
    /// surface its E0493 drops and E0015 non-const calls: rustc
    /// checks both statically, so they still reject in dead code,
    /// while its panics and overflows do not. The environment, step
    /// count, and drop-temporary count are restored afterwards.
    fn scan_dead_block<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &Env, b: ast::BlockId) -> Result<(), Diag> {
        if !self.dead_seen.insert((true, b.0)) {
            return Ok(());
        }
        let (steps, flex, local) = (self.steps, self.flex_debt.len(), self.local_debt.len());
        let depth = self.call_depth;
        let mut env2 = env.clone();
        // The scan's writes and pins of literal locals are not real.
        let fsave = (self.flex_locals.clone(), self.pins.len(), self.rerun);
        let r = self.block(cx, &mut env2, b, None);
        (self.flex_locals, self.rerun) = (fsave.0, fsave.2);
        self.pins.truncate(fsave.1);
        self.steps = steps;
        self.call_depth = depth;
        self.flex_debt.truncate(flex);
        self.local_debt.truncate(local);
        match r {
            Err(d) if is_drop_diag(&d) || is_nonconst_call_diag(&d) => Err(d),
            _ => Ok(()),
        }
    }

    /// `scan_dead_block` for one expression (an `else` arm).
    fn scan_dead_expr<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &Env, e: ExprId) -> Result<(), Diag> {
        if !self.dead_seen.insert((false, e.0)) {
            return Ok(());
        }
        let (steps, flex, local) = (self.steps, self.flex_debt.len(), self.local_debt.len());
        let depth = self.call_depth;
        let mut env2 = env.clone();
        // The scan's writes and pins of literal locals are not real.
        let fsave = (self.flex_locals.clone(), self.pins.len(), self.rerun);
        let r = self.expr(cx, &mut env2, e, None);
        (self.flex_locals, self.rerun) = (fsave.0, fsave.2);
        self.pins.truncate(fsave.1);
        self.steps = steps;
        self.call_depth = depth;
        self.flex_debt.truncate(flex);
        self.local_debt.truncate(local);
        match r {
            Err(d) if is_drop_diag(&d) || is_nonconst_call_diag(&d) => Err(d),
            _ => Ok(()),
        }
    }

    /// The environment a dead branch is scanned in: `env` plus the
    /// bindings of `pat` (matched against a value of type `t`), each
    /// bound to a zero value of its type. A name the walk cannot type
    /// stays unbound, so a read of it ends the scan there.
    fn dead_env<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &Env, pat: PatId, t: Ty) -> Env {
        let mut out = env.clone();
        self.dead_binds(cx, pat, t, &mut out, 0);
        out
    }

    fn dead_binds<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, pat: PatId, t: Ty, out: &mut Env, depth: u32) {
        if depth > 16 {
            return;
        }
        // A type the walk cannot see (an elided `None::<T>` argument)
        // binds an integer zero: integer uses go on.
        let bind = |cx: &mut C, out: &mut Env, name: Sym, mutable: bool, t: Ty| {
            let v = if t == ERROR { Some(ConstValue::Int(0)) } else { zero_value(cx, t, 0) };
            if let Some(v) = v {
                out.push((name, (v, t), mutable, false));
            }
        };
        // Positional sub-patterns against their types; a `..` element
        // maps the elements after it from the end.
        let positional = |this: &mut Self, cx: &mut C, out: &mut Env, elems: &[PatId], tys: &[Ty]| {
            let rest = elems.iter().position(|&p| matches!(cx.ast().pat(p), Pat::Rest));
            for (i, &p) in elems.iter().enumerate() {
                let ti = match rest {
                    Some(r) if i > r => tys.len().checked_sub(elems.len() - i),
                    _ => Some(i),
                };
                if let Some(&et) = ti.and_then(|ti| tys.get(ti)) {
                    this.dead_binds(cx, p, et, out, depth + 1);
                }
            }
        };
        match cx.ast().pat(pat).clone() {
            Pat::Binding { name, mutable, by_ref: false } => bind(cx, out, name, mutable, t),
            Pat::At { name, mutable, by_ref: false, inner } => {
                bind(cx, out, name, mutable, t);
                self.dead_binds(cx, inner, t, out, depth + 1);
            }
            Pat::Paren(p) => self.dead_binds(cx, p, t, out, depth + 1),
            Pat::Or(ps) => {
                if let Some(&p) = ps.first() {
                    self.dead_binds(cx, p, t, out, depth + 1);
                }
            }
            Pat::Ref { inner, .. } => {
                let it = match cx.tys_ref().kind(t) {
                    TyKind::Ref(_, _, it) => it,
                    _ => ERROR,
                };
                self.dead_binds(cx, inner, it, out, depth + 1);
            }
            Pat::Tuple(elems) => {
                let tys = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).to_vec(),
                    _ => vec![ERROR; elems.len()],
                };
                positional(self, cx, out, &elems, &tys);
            }
            Pat::TupleStruct { path, elems } => {
                let variant = if cx.tys_ref().option_elem(t).is_some() || cx.tys_ref().result_args(t).is_some() {
                    match path.last().map(|s| cx.sym_text(s.name)) {
                        Some("Some" | "Ok") => Some(if cx.tys_ref().option_elem(t).is_some() { 1 } else { 0 }),
                        Some("Err") => Some(1),
                        _ => None,
                    }
                } else {
                    cx.pattern_variant(&path).map(|(_, v)| v)
                };
                let tys = variant.and_then(|v| part_tys(cx, t, v, elems.len())).unwrap_or_else(|| vec![ERROR; elems.len()]);
                positional(self, cx, out, &elems, &tys);
            }
            Pat::Struct { path, fields, .. } => {
                let typed = cx.pattern_variant(&path).and_then(|(adt, v)| {
                    let names = cx.variant_fields(adt, v);
                    part_tys(cx, t, v, names.len()).map(|tys| (names, tys))
                });
                for (fname, fp) in fields {
                    let ft = typed.as_ref().and_then(|(names, tys)| names.iter().position(|(n, _)| *n == fname).map(|i| tys[i]));
                    self.dead_binds(cx, fp, ft.unwrap_or(ERROR), out, depth + 1);
                }
            }
            Pat::Slice { prefix, suffix, .. } => {
                let el = match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => el,
                    _ => ERROR,
                };
                for p in prefix.into_iter().chain(suffix) {
                    self.dead_binds(cx, p, el, out, depth + 1);
                }
            }
            _ => {}
        }
    }

    /// Evaluates to a plain value (any control-flow escape is an error here).
    fn value<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
        match self.expr(cx, env, e, expected)? {
            Flow::Val(v) => {
                // A blob that arrives here (a const item's value, a
                // call argument) grants its per-byte step allowance
                // even when no literal was evaluated in this item.
                self.note_blob(&v.0);
                Ok(v)
            }
            _ => Err(outside(cx.ast().expr_span(e), "control flow out of a const expression")),
        }
    }

    /// Peels one reference layer for field and index access: a promoted
    /// value, or the place a reference into a static names (read from
    /// the static's value).
    fn deref_value<'a, C: ConstCx<'a>>(&self, cx: &mut C, v: ConstValue, t: Ty) -> (ConstValue, Ty) {
        let it = match cx.tys_ref().kind(t) {
            TyKind::Ref(_, _, it) => it,
            _ => return (v, t),
        };
        let got = match &v {
            ConstValue::StaticRef(idx) => read_static(cx, *idx, &[]),
            ConstValue::StaticPlace(idx, path) => read_static(cx, *idx, path),
            _ => None,
        };
        if let ConstValue::Ref(inner) = v {
            return (*inner, it);
        }
        match got {
            Some(g) => (g, it),
            None => (v, t),
        }
    }

    /// Peels every reference layer, for field and index access (auto-deref).
    fn auto_deref<'a, C: ConstCx<'a>>(&self, cx: &mut C, mut v: ConstValue, mut t: Ty) -> (ConstValue, Ty) {
        while matches!(cx.tys_ref().kind(t), TyKind::Ref(..)) {
            let (v2, t2) = self.deref_value(cx, v, t);
            let done = t2 == t;
            (v, t) = (v2, t2);
            if done {
                break;
            }
        }
        (v, t)
    }

    /// The static place a reference-typed `e` that is no static place
    /// itself points to: a const, local, or field holding a `StaticRef` or
    /// `StaticPlace` (`const R: &[M] = &ARR;` then `&R[1]`). Only cheap
    /// place shapes are evaluated again.
    fn static_target<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId) -> Result<Option<(u32, Vec<StaticStep>, Ty)>, Diag> {
        if !matches!(cx.ast().expr(e), Expr::Path(_) | Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. }) {
            return Ok(None);
        }
        let (v, t) = self.value_place(cx, env, e, None)?;
        let TyKind::Ref(_, _, it) = cx.tys_ref().kind(t) else { return Ok(None) };
        Ok(match v {
            ConstValue::StaticRef(idx) => Some((idx, Vec::new(), it)),
            ConstValue::StaticPlace(idx, path) => Some((idx, path.into_vec(), it)),
            _ => None,
        })
    }

    /// The static place `e` names (`S`, `S.f`, `S.0[i]`, `(*S)[i]`, auto-deref
    /// included) as a static index, a path from its root, and the place's
    /// type. A deref of a reference to another static re-roots the path
    /// there, so the result is the storage rustc's value points to. None
    /// when `e` is no such place, or a step cannot be followed.
    fn static_place<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId) -> Result<Option<(u32, Vec<StaticStep>, Ty)>, Diag> {
        let ast = cx.ast();
        // The base place of a projection, with every reference layer peeled.
        macro_rules! base {
            ($b:expr) => {{
                let got = match self.static_place(cx, env, $b)? {
                    Some(got) => Some(got),
                    None => self.static_target(cx, env, $b)?,
                };
                let Some((mut idx, mut path, mut t)) = got else { return Ok(None) };
                while let TyKind::Ref(_, _, it) = cx.tys_ref().kind(t) {
                    if !static_deref(cx, &mut idx, &mut path) {
                        return Ok(None);
                    }
                    t = it;
                }
                (idx, path, t)
            }};
        }
        let got = match ast.expr(e) {
            Expr::Path(segs) => {
                let [seg] = segs.as_slice() else { return Ok(None) };
                if env.iter().any(|(n, _, _, _)| *n == seg.name) {
                    return Ok(None);
                }
                cx.static_item(seg.name, ast.expr_span(e)).map(|(idx, t)| (idx, Vec::new(), t))
            }
            Expr::Deref(inner) => match self.static_place(cx, env, *inner)? {
                Some((mut idx, mut path, t)) => {
                    let TyKind::Ref(_, _, it) = cx.tys_ref().kind(t) else { return Ok(None) };
                    static_deref(cx, &mut idx, &mut path).then_some((idx, path, it))
                }
                None => self.static_target(cx, env, *inner)?,
            },
            Expr::Field { base, name } => {
                let (idx, mut path, t) = base!(*base);
                let Some(adt) = cx.tys_ref().local_adt(t).filter(|&a| !cx.is_enum(a)) else { return Ok(None) };
                let fields = cx.variant_fields(adt, 0);
                fields.iter().position(|(n, _)| n == name).map(|i| {
                    path.push(StaticStep::Field(i as u32));
                    (idx, path, fields[i].1)
                })
            }
            Expr::TupleField { base, index } => {
                let (idx, mut path, t) = base!(*base);
                let ft = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).get(*index as usize).copied(),
                    _ => cx.tys_ref().local_adt(t).filter(|&a| !cx.is_enum(a)).and_then(|a| cx.variant_fields(a, 0).get(*index as usize).map(|f| f.1)),
                };
                ft.map(|ft| {
                    path.push(StaticStep::Field(*index));
                    (idx, path, ft)
                })
            }
            Expr::Index { base, index } => {
                let (idx, mut path, t) = base!(*base);
                let (TyKind::Array(el, _) | TyKind::Slice(el)) = cx.tys_ref().kind(t) else { return Ok(None) };
                let (ConstValue::Int(i), _) = self.value(cx, env, *index, Some(USIZE))? else { return Ok(None) };
                u32::try_from(i).ok().map(|i| {
                    path.push(StaticStep::Elem(i));
                    (idx, path, el)
                })
            }
            _ => None,
        };
        Ok(got)
    }

    fn block<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, b: ast::BlockId, expected: Option<Ty>) -> Result<Flow, Diag> {
        let block = cx.ast().block(b);
        let saved = env.len();
        // Literal locals of slots this env no longer has are stale.
        self.flex_locals.retain(|f| f.slot < saved);
        let mut out = (ConstValue::Unit, UNIT);
        for stmt in &block.stmts {
            match stmt {
                ast::Stmt::Let { pat, ty, init, els, .. } => {
                    let Some(init) = init else { return Err(outside(cx.ast().pat_span(*pat), "an uninitialized binding")) };
                    // A literal local pinned in an earlier run is typed
                    // at its `let` (see `FlexLocal`).
                    let plain = matches!(cx.ast().pat(*pat), Pat::Binding { by_ref: false, .. });
                    let pinned = if ty.is_none() && plain { self.pins.iter().find(|&&(p, _)| p == *pat).map(|&(_, t)| t) } else { None };
                    let exp = ty.map(|t| cx.resolve_ty(t)).or(pinned);
                    let debt_before = self.flex_debt.clone();
                    let mut v = self.value_moved(cx, env, *init, exp)?;
                    // The initializer coerces to the written type, or
                    // the binding is a mismatch (rustc E0308). Only in
                    // the const expression's own code: a called const
                    // fn's body is type-checked as a fn, and its written
                    // types (its params, `Self`) do not resolve here.
                    if let Some(t) = exp
                        && self.call_depth == 0
                    {
                        if !const_ty_compatible(cx.tys_ref(), v.1, t) {
                            return Err(const_ty_mismatch(cx.ast().expr_span(*init), "this `let` initializer"));
                        }
                        if t != ERROR {
                            v.1 = t;
                        }
                    }
                    // A drop value that is not bound whole is
                    // destroyed by the binding itself: a `_` pattern
                    // drops it at once, and a destructuring pattern
                    // drops what it does not move out (E0493).
                    if cx.needs_drop(v.1) && !pat_is_whole_binding(cx.ast(), *pat) {
                        return Err(drop_diag(cx, v.1, cx.ast().pat_span(*pat)));
                    }
                    // A wide literal in the init (or carried by a
                    // local the init reads) now rides on the new
                    // bindings: reading one at a pinning type
                    // settles it (see `flex_debt`).
                    let mut debts: Vec<ExprId> = self.flex_debt.iter().copied().filter(|d| !debt_before.contains(d)).collect();
                    if let Expr::Path(segs) = cx.ast().expr(*init)
                        && segs.len() == 1
                    {
                        for &(n, d) in &self.local_debt {
                            if n == segs[0].name && !debts.contains(&d) {
                                debts.push(d);
                            }
                        }
                    }
                    let mut binds = Vec::new();
                    if !self.match_pat(cx, env, *pat, &v.0.clone(), v.1, true, &mut binds)? {
                        // A let-else runs its (diverging) else block
                        // instead; its flow is the block's flow.
                        if let Some(els_b) = els {
                            let flow = self.block(cx, env, *els_b, None);
                            self.check_scope_drops(cx, env, saved, cx.ast().pat_span(*pat))?;
                            env.truncate(saved);
                            return flow;
                        }
                        return Err(outside(cx.ast().pat_span(*pat), "a refutable pattern"));
                    }
                    for &(name, _, _, _) in &binds {
                        for &d in &debts {
                            self.local_debt.push((name, d));
                        }
                    }
                    // `let x = <literal>;` with no type: a literal local
                    // (its groups are read before the binding shadows).
                    let flex = if exp.is_none() && plain && v.1 == super::int(IntTy::I128) { self.flex_groups(cx, env, *init) } else { None };
                    let slot = env.len();
                    self.flex_locals.retain(|f| f.slot < slot);
                    if let (Some(groups), [(name, _, _, _)]) = (flex, binds.as_slice()) {
                        let group = self.unify_flex(&groups).unwrap_or_else(|| {
                            self.next_flex_group += 1;
                            self.next_flex_group
                        });
                        let init = pure_int_lit(cx.ast(), *init).then_some(*init);
                        self.flex_locals.push(FlexLocal { slot, name: *name, pat: *pat, init, group });
                    }
                    env.extend(binds);
                }
                ast::Stmt::Expr { expr, .. } => match self.expr(cx, env, *expr, None)? {
                    // A statement value of a drop type is destroyed
                    // at the end of the statement (E0493).
                    Flow::Val(v) => {
                        if cx.needs_drop(v.1) {
                            return Err(drop_diag(cx, v.1, cx.ast().expr_span(*expr)));
                        }
                    }
                    other => {
                        self.check_scope_drops(cx, env, saved, cx.ast().expr_span(*expr))?;
                        env.truncate(saved);
                        return Ok(other);
                    }
                },
                // An item (a local `const` or `fn`) does nothing when the
                // block runs; a path to it evaluates where it is used, or
                // rejects there.
                ast::Stmt::Item(_) => {}
                ast::Stmt::Macro { .. } => {
                    return Err(outside(cx.ast().block(b).span, "items in a const block"));
                }
            }
        }
        if let Some(tail) = block.tail {
            // The tail value moves out of the block; its own drop
            // is judged by the block's parent, the locals it leaves
            // behind by the scope check below.
            let prev = self.move_read;
            self.move_read = true;
            let tail_flow = self.expr(cx, env, tail, expected);
            self.move_read = prev;
            match tail_flow? {
                Flow::Val(v) => out = v,
                other => {
                    self.check_scope_drops(cx, env, saved, cx.ast().expr_span(tail))?;
                    env.truncate(saved);
                    return Ok(other);
                }
            }
        }
        self.check_scope_drops(cx, env, saved, block.span)?;
        env.truncate(saved);
        Ok(Flow::Val(out))
    }

    fn path_value<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        segs: &[ast::PathSeg],
        span: Span,
        expected: Option<Ty>,
    ) -> Result<TypedValue, Diag> {
        if segs.len() == 1 {
            let name = segs[0].name;
            // A read at an integer type pins a literal local.
            if let Some(t) = expected
                && let Some(slot) = env.iter().rposition(|(n, _, _, _)| *n == name)
                && let Some(i) = self.flex_locals.iter().position(|f| f.name == name && f.slot == slot)
            {
                let g = self.flex_locals[i].group;
                self.pin_flex(cx, env, &[g], t, span)?;
            }
            if let Some(slot) = env.iter_mut().rev().find(|(n, _, _, _)| *n == name) {
                if self.move_read {
                    slot.3 = true;
                }
                let v = slot.1.clone();
                // A read at a pinning integer type settles the
                // local's wide literals (see `flex_debt`).
                if expected.is_some_and(|t| self.int_ty_of(cx, t).is_some()) {
                    self.clear_local_debt(name);
                }
                return Ok(v);
            }
            if let Some(v) = cx.const_item(name, span) {
                return Ok(v);
            }
            if let Some((idx, ty)) = cx.static_item(name, span) {
                // Reading an immutable static in const gives its value; the
                // context only returns statics it may read this way.
                if let Some(v) = cx.const_item(name, span) {
                    return Ok(v);
                }
                let _ = idx;
                let _ = ty;
                return Err(outside(span, "a reference to a static"));
            }
        }
        if let Some((adt, variant, ty)) = cx.unit_variant(segs, expected) {
            let _ = adt;
            return Ok((ConstValue::Variant(variant, Vec::new()), ty));
        }
        // Associated consts of integer types: `i64::MAX`, `usize::MAX`, `u8::MIN`, ...
        if segs.len() >= 2 {
            if let Some(v) = self.nonzero_assoc_const(cx, segs) {
                return Ok(v);
            }
        }
        if segs.len() == 2 {
            if let Some(v) = self.int_assoc_const(cx, cx.sym_text(segs[0].name), cx.sym_text(segs[1].name)) {
                return Ok(v);
            }
            if cx.sym_text(segs[0].name) == "char"
                && let Some(v) = self.char_assoc_const(cx, segs[1].name)
            {
                return Ok(v);
            }
            // Through a type alias of a primitive (`IdCell::MAX`).
            if !segs[0].has_args()
                && let Some(prim) = cx.alias_primitive(segs[0].name)
            {
                let v = match prim {
                    "char" => self.char_assoc_const(cx, segs[1].name),
                    "f32" | "f64" => {
                        let f = if prim == "f32" { FloatTy::F32 } else { FloatTy::F64 };
                        match primitive_float_assoc(f, cx.sym_text(segs[1].name)) {
                            Some((bits, None)) => Some((ConstValue::Float(bits, f), cx.tys().float_ty(f))),
                            Some((v, Some(it))) => Some((ConstValue::Int(v as i128), super::int(it))),
                            None => None,
                        }
                    }
                    _ => self.int_assoc_const(cx, prim, cx.sym_text(segs[1].name)),
                };
                if let Some(v) = v {
                    return Ok(v);
                }
            }
        }
        // Inherent associated consts of user types: `Type::CONST`.
        if segs.len() >= 2
            && let Some(v) = cx.assoc_const_item(segs)
        {
            return Ok(v);
        }
        if let Some(v) = self.float_assoc_const(cx, segs) {
            return Ok(v);
        }
        if let Some(v) = cx.fn_item(segs, span) {
            return Ok(v);
        }
        if let [head, _] = segs
            && !cx.names_type(head.name)
        {
            return Err(unknown_type(cx, head, span));
        }
        Err(outside(span, &format!("the path `{}`", path_text(cx, segs))))
    }

    /// `f64::NAN`, `std::f64::consts::PI`, and friends, by written names.
    fn float_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &mut C, segs: &[ast::PathSeg]) -> Option<TypedValue> {
        let names: Vec<&str> = segs.iter().map(|s| cx.sym_text(s.name)).collect();
        let (ty_name, item, module) = match names.as_slice() {
            [t, i] => (*t, *i, false),
            [p, t, c, i] if matches!(*p, "std" | "core" | "alloc") && *c == "consts" => (*t, *i, true),
            _ => return None,
        };
        let f = match ty_name {
            "f32" => FloatTy::F32,
            "f64" => FloatTy::F64,
            _ => return None,
        };
        if module {
            let bits = float_consts_value(f, item)?;
            let t = cx.tys().float_ty(f);
            return Some((ConstValue::Float(bits, f), t));
        }
        match primitive_float_assoc(f, item)? {
            (bits, None) => {
                let t = cx.tys().float_ty(f);
                Some((ConstValue::Float(bits, f), t))
            }
            (v, Some(it)) => Some((ConstValue::Int(v as i128), super::int(it))),
        }
    }

    /// `char::MAX`, `char::REPLACEMENT_CHARACTER`, and
    /// `char::UNICODE_VERSION` by the item's written name (the caller
    /// checks that the type is `char`).
    fn char_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &mut C, item: Sym) -> Option<TypedValue> {
        match cx.sym_text(item) {
            "MAX" => Some((ConstValue::Char(char::MAX), CHAR)),
            "MIN" => Some((ConstValue::Char(char::MIN), CHAR)),
            "REPLACEMENT_CHARACTER" => Some((ConstValue::Char(char::REPLACEMENT_CHARACTER), CHAR)),
            "UNICODE_VERSION" => {
                let (maj, min, pat) = char::UNICODE_VERSION;
                let u8t = super::int(IntTy::U8);
                let ts = cx.tys().intern_tys(&[u8t, u8t, u8t]);
                let ty = cx.tys().intern(TyKind::Tuple(ts));
                let parts = vec![ConstValue::Int(maj as i128), ConstValue::Int(min as i128), ConstValue::Int(pat as i128)];
                Some((ConstValue::Aggregate(parts), ty))
            }
            _ => None,
        }
    }

    /// `i32::MAX` and friends, resolved by written names.
    fn int_assoc_const<'a, C: ConstCx<'a>>(&self, _cx: &C, ty_name: &str, item: &str) -> Option<TypedValue> {
        let it = IntTy::ALL.iter().find(|i| i.name() == ty_name).copied()?;
        let bits = it.bits();
        let v = match item {
            "MAX" => {
                if bits >= 128 {
                    if it.signed() { i128::MAX } else { -1 }
                } else if it.signed() {
                    (1i128 << (bits - 1)) - 1
                } else {
                    (1i128 << bits) - 1
                }
            }
            "MIN" => {
                if it.signed() {
                    if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) }
                } else {
                    0
                }
            }
            "BITS" => return Some((ConstValue::Int(bits as i128), super::int(IntTy::U32))),
            _ => return None,
        };
        Some((ConstValue::Int(v), super::int(it)))
    }

    /// `NonZeroU32::MIN` and kin (TRIAGE T5), by written alias
    /// names (the last two segments, after import expansion).
    fn nonzero_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &mut C, segs: &[ast::PathSeg]) -> Option<TypedValue> {
        let (ty_seg, item_seg) = segs.split_at(segs.len() - 1);
        let it = match cx.sym_text(ty_seg.last()?.name) {
            "NonZeroU8" => IntTy::U8,
            "NonZeroU16" => IntTy::U16,
            "NonZeroU32" => IntTy::U32,
            "NonZeroU64" => IntTy::U64,
            "NonZeroU128" => IntTy::U128,
            "NonZeroUsize" => IntTy::Usize,
            "NonZeroI8" => IntTy::I8,
            "NonZeroI16" => IntTy::I16,
            "NonZeroI32" => IntTy::I32,
            "NonZeroI64" => IntTy::I64,
            "NonZeroI128" => IntTy::I128,
            "NonZeroIsize" => IntTy::Isize,
            _ => return None,
        };
        let bits = it.bits();
        let v = match cx.sym_text(item_seg[0].name) {
            "MAX" => {
                if it == IntTy::U128 {
                    -1
                } else {
                    truncate_to_int(it.max128() as i128, it)
                }
            }
            "MIN" => {
                if it.signed() {
                    if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) }
                } else {
                    1
                }
            }
            _ => return None,
        };
        let t = crate::check::generics::nonzero_ty(cx.tys(), super::int(it));
        Some((ConstValue::Aggregate(vec![ConstValue::Int(v)]), t))
    }

    fn binary<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        match op {
            BinOp::And => {
                let (v, _) = self.value(cx, env, lhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                if !b {
                    return Ok((ConstValue::Bool(false), BOOL));
                }
                let (v, _) = self.value(cx, env, rhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                return Ok((ConstValue::Bool(b), BOOL));
            }
            BinOp::Or => {
                let (v, _) = self.value(cx, env, lhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                if b {
                    return Ok((ConstValue::Bool(true), BOOL));
                }
                let (v, _) = self.value(cx, env, rhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                return Ok((ConstValue::Bool(b), BOOL));
            }
            _ => {}
        }
        // A comparison's expected type is bool: it does not pin the
        // operands. An unpinned (flex) operand takes the other
        // operand's type, as inference does (`!0 > T` with `T: u8`
        // computes `!0` in u8); two unpinned operands of a comparison
        // fall back to i32. Re-running a flex operand at its pinning
        // type is sound: it has no name, call, or suffix to disagree.
        let lhs_exp = if op.is_cmp() { None } else { expected };
        let (mut lv, mut lt) = self.value(cx, env, lhs, lhs_exp)?;
        // A shift amount's type is its own: the shifted value's type
        // does not pin a literal local there.
        let shift = matches!(op, BinOp::Shl | BinOp::Shr);
        let rhs_exp = if shift && self.flex_groups(cx, env, rhs).is_some_and(|g| !g.is_empty()) { None } else { Some(lt) };
        let (mut rv, mut rt) = self.value(cx, env, rhs, rhs_exp)?;
        let both_int = matches!(lv, ConstValue::Int(_)) && matches!(rv, ConstValue::Int(_));
        // A shift's operands have independent types in Rust: the
        // amount's type never pins the shifted value's (`4 << S`
        // with `S: u32` in a u64 context computes in u64). So the
        // re-pinning below skips shifts; a flex left side with no
        // pinning type at all falls back to i32, as inference does.
        if both_int && matches!(op, BinOp::Shl | BinOp::Shr) && flex_int_expr(cx.ast(), lhs) && self.int_ty_of(cx, lt).is_none() {
            let pin = match lhs_exp {
                Some(t) if self.int_ty_of(cx, t).is_some() => t,
                _ => super::I32,
            };
            (lv, lt) = self.value(cx, env, lhs, Some(pin))?;
        }
        if both_int
            && !matches!(op, BinOp::Shl | BinOp::Shr)
            && lt != rt
            && self.int_ty_of(cx, lt).is_some()
            && self.int_ty_of(cx, rt).is_some()
        {
            if flex_int_expr(cx.ast(), lhs) && !flex_int_expr(cx.ast(), rhs) {
                (lv, lt) = self.value(cx, env, lhs, Some(rt))?;
            } else if flex_int_expr(cx.ast(), rhs) && !flex_int_expr(cx.ast(), lhs) {
                (rv, rt) = self.value(cx, env, rhs, Some(lt))?;
            }
        }
        if both_int && op.is_cmp() && flex_int_expr(cx.ast(), lhs) && flex_int_expr(cx.ast(), rhs) {
            (lv, lt) = self.value(cx, env, lhs, Some(super::I32))?;
            (rv, rt) = self.value(cx, env, rhs, Some(super::I32))?;
        }
        // A typed operand pins a local on the other side, as
        // inference does: settle its wide literals.
        if both_int && !matches!(op, BinOp::Shl | BinOp::Shr) {
            for (side, other_ty) in [(lhs, rt), (rhs, lt)] {
                if self.int_ty_of(cx, other_ty).is_some()
                    && let Expr::Path(segs) = cx.ast().expr(side)
                    && segs.len() == 1
                {
                    self.clear_local_debt(segs[0].name);
                }
            }
        }
        // A literal local meets a typed operand: it takes that type, as
        // inference does. Two open sides share one type.
        if both_int && !shift {
            if self.pin_against(cx, env, lhs, rhs, rt, span)? {
                (lv, lt) = self.value(cx, env, lhs, Some(rt))?;
            } else if self.pin_against(cx, env, rhs, lhs, lt, span)? {
                (rv, rt) = self.value(cx, env, rhs, Some(lt))?;
            } else if let (Some(a), Some(b)) = (self.flex_groups(cx, env, lhs), self.flex_groups(cx, env, rhs)) {
                self.unify_flex(&[a, b].concat());
            }
        }
        let _ = rt;
        if op.is_cmp() {
            // Only primitive scalars compare in const: rustc has no const
            // `PartialEq` for tuples, arrays, `&str`, `Option`, or fn
            // pointers (E0658), and this accepted them.
            let scalar = |v: &ConstValue| matches!(v, ConstValue::Int(_) | ConstValue::Float(..) | ConstValue::Bool(_) | ConstValue::Char(_));
            if !scalar(&lv) || !scalar(&rv) {
                return Err(outside(span, "this comparison of non-scalar values"));
            }
            let eq = values_eq(&lv, &rv);
            let ord = match (&lv, &rv) {
                (ConstValue::Float(a, FloatTy::F64), ConstValue::Float(b, _)) => f64::from_bits(*a).partial_cmp(&f64::from_bits(*b)),
                (ConstValue::Float(a, FloatTy::F32), ConstValue::Float(b, _)) => {
                    f32::from_bits(*a as u32).partial_cmp(&f32::from_bits(*b as u32))
                }
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(cmp_int(*a, *b, self.int_ty_of(cx, lt))),
                (ConstValue::Char(a), ConstValue::Char(b)) => Some(a.cmp(b)),
                (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(a.cmp(b)),
                _ => None,
            };
            let r = match op {
                BinOp::Eq => eq,
                BinOp::Ne => !eq,
                BinOp::Lt => ord == Some(std::cmp::Ordering::Less),
                BinOp::Le => matches!(ord, Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal)),
                BinOp::Gt => ord == Some(std::cmp::Ordering::Greater),
                BinOp::Ge => matches!(ord, Some(std::cmp::Ordering::Greater | std::cmp::Ordering::Equal)),
                _ => unreachable!(),
            };
            if !op.is_cmp() || (matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) && ord.is_none()) {
                return Err(outside(span, "this comparison"));
            }
            return Ok((ConstValue::Bool(r), BOOL));
        }
        match (lv, rv) {
            (ConstValue::Float(a, f), ConstValue::Float(b, _)) => {
                let r = match f {
                    FloatTy::F64 => {
                        let (x, y) = (f64::from_bits(a), f64::from_bits(b));
                        let r = match op {
                            BinOp::Add => x + y,
                            BinOp::Sub => x - y,
                            BinOp::Mul => x * y,
                            BinOp::Div => x / y,
                            BinOp::Rem => x % y,
                            _ => return Err(outside(span, "this operation")),
                        };
                        r.to_bits()
                    }
                    FloatTy::F32 => {
                        let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
                        let r = match op {
                            BinOp::Add => x + y,
                            BinOp::Sub => x - y,
                            BinOp::Mul => x * y,
                            BinOp::Div => x / y,
                            BinOp::Rem => x % y,
                            _ => return Err(outside(span, "this operation")),
                        };
                        r.to_bits() as u64
                    }
                };
                Ok((ConstValue::Float(r, f), lt))
            }
            (ConstValue::Int(a), ConstValue::Int(b)) => self.int_op(cx, op, (ConstValue::Int(a), lt), (ConstValue::Int(b), lt), span),
            (ConstValue::Bool(a), ConstValue::Bool(b)) => {
                let r = match op {
                    BinOp::BitAnd => a & b,
                    BinOp::BitOr => a | b,
                    BinOp::BitXor => a ^ b,
                    _ => return Err(outside(span, "this operation")),
                };
                Ok((ConstValue::Bool(r), BOOL))
            }
            _ => Err(outside(span, "this operation")),
        }
    }

    fn int_op<'a, C: ConstCx<'a>>(&self, cx: &C, op: BinOp, a: TypedValue, b: TypedValue, span: Span) -> Result<TypedValue, Diag> {
        let (ConstValue::Int(x), t) = a else { return Err(outside(span, "this operation")) };
        let ConstValue::Int(y) = b.0 else { return Err(outside(span, "this operation")) };
        let over = || outside(span, "this operation (overflow or division by zero)");
        // Every operation runs in the operand type: overflow of that
        // type is a const error (rustc E0080), and shifts check the
        // amount against the type's width. Unsigned math runs on the
        // raw bits, so u128 values at or above 2^127 stay correct.
        let Some(it) = self.int_ty_of(cx, t) else {
            let r = match op {
                BinOp::Add => x.checked_add(y),
                BinOp::Sub => x.checked_sub(y),
                BinOp::Mul => x.checked_mul(y),
                BinOp::Div => x.checked_div(y),
                BinOp::Rem => x.checked_rem(y),
                BinOp::BitAnd => Some(x & y),
                BinOp::BitOr => Some(x | y),
                BinOp::BitXor => Some(x ^ y),
                BinOp::Shl => u32::try_from(y).ok().and_then(|y| x.checked_shl(y)),
                BinOp::Shr => u32::try_from(y).ok().and_then(|y| x.checked_shr(y)),
                _ => return Err(outside(span, "this operation")),
            };
            return Ok((ConstValue::Int(r.ok_or_else(over)?), t));
        };
        // A wide (unsuffixed-literal) operand that does not fit the
        // operation type is an overflow, never a silent wrap. The
        // shift amount is exempt: its own check bounds it.
        let stored_fits = |v: i128| {
            if it.bits() >= 128 {
                true
            } else if it.signed() {
                fits(v, it)
            } else {
                v >= 0 && (v as u128) <= it.max128()
            }
        };
        if !stored_fits(x) || (!matches!(op, BinOp::Shl | BinOp::Shr) && !stored_fits(y)) {
            return Err(over());
        }
        if !matches!(
            op,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr
        ) {
            return Err(outside(span, "this operation"));
        }
        let r = int_binop(op, it, x, y).ok_or_else(over)?;
        Ok((ConstValue::Int(r), t))
    }

    fn cast<'a, C: ConstCx<'a>>(&self, cx: &C, (v, from_ty): TypedValue, target: Ty, span: Span) -> Result<TypedValue, Diag> {
        let tk = cx.tys_ref().kind(target);
        match (v, tk) {
            (ConstValue::Float(bits, f), TyKind::Float(g)) => {
                let r = match (f, g) {
                    (FloatTy::F64, FloatTy::F32) => (f64::from_bits(bits) as f32).to_bits() as u64,
                    (FloatTy::F32, FloatTy::F64) => (f32::from_bits(bits as u32) as f64).to_bits(),
                    _ => bits,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Float(bits, f), TyKind::Int(it)) => Ok((ConstValue::Int(float_to_int(bits, f, it)), target)),
            (ConstValue::Int(i), TyKind::Float(g)) => {
                // The source type decides the conversion: an unsigned
                // source converts from its raw bits, never as a negative.
                let unsigned = matches!(self.int_ty_of(cx, from_ty), Some(it) if !it.signed());
                let r = match (g, unsigned) {
                    (FloatTy::F64, true) => ((i as u128) as f64).to_bits(),
                    (FloatTy::F32, true) => ((i as u128) as f32).to_bits() as u64,
                    (FloatTy::F64, false) => (i as f64).to_bits(),
                    (FloatTy::F32, false) => (i as f32).to_bits() as u64,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Int(i), TyKind::Int(it)) => Ok((ConstValue::Int(truncate_to_int(i, it)), target)),
            (ConstValue::Bool(b), TyKind::Int(_)) => Ok((ConstValue::Int(b as i128), target)),
            (ConstValue::Char(c), TyKind::Int(_)) => Ok((ConstValue::Int(c as i128), target)),
            (ConstValue::Int(i), TyKind::Char) => {
                let c = u32::try_from(i).ok().and_then(char::from_u32);
                match c {
                    Some(c) => Ok((ConstValue::Char(c), target)),
                    None => Err(outside(span, "this cast (invalid char)")),
                }
            }
            (ConstValue::Variant(variant, _), TyKind::Int(it)) => match cx.tys_ref().local_adt(from_ty) {
                Some(adt) => Ok((ConstValue::Int(truncate_to_int(cx.discriminant(adt, variant), it)), target)),
                None => Err(outside(span, "this cast")),
            },
            (v, _) if matches!(v, ConstValue::Int(_) | ConstValue::Bool(_)) && tk == TyKind::Bool => Err(outside(span, "this cast")),
            _ => Err(outside(span, "this cast")),
        }
    }

    fn call<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
        expected: Option<Ty>,
    ) -> Result<TypedValue, Diag> {
        // `Vec::new()` and `String::new()` are const fns (an empty buffer),
        // read where the expected type is the std one (W-THREADS: the
        // `static M: Mutex<Vec<T>> = Mutex::new(Vec::new())` shape).
        if args.is_empty()
            && let Some(want) = expected
            && let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() >= 2
            && cx.sym_text(segs[segs.len() - 1].name) == "new"
            && segs[segs.len() - 1].type_args().is_empty()
        {
            let ty_name = cx.sym_text(segs[segs.len() - 2].name);
            let b = cx.tys_ref().builtin_of(want);
            if (ty_name == "Vec" && b == Some(super::BuiltinTy::Vec)) || (ty_name == "String" && b == Some(super::BuiltinTy::String)) {
                return Ok((ConstValue::Aggregate(Vec::new()), want));
            }
        }
        // `String::new()` names its type without an expected one
        // (`let s = String::new();`).
        if args.is_empty()
            && expected.is_none()
            && let Expr::Path(segs) = cx.ast().expr(callee)
            && let [ty_seg, f] = segs.as_slice()
            && cx.sym_text(ty_seg.name) == "String"
            && cx.sym_text(f.name) == "new"
            && f.type_args().is_empty()
        {
            return Ok((ConstValue::Aggregate(Vec::new()), super::STRING));
        }
        // `Cell::new(v)` is a const fn: the value is the cell's (a Cell's C
        // form is its value's).
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && let [arg] = args
            && segs.iter().all(|s| s.type_args().is_empty())
            && matches!(segs.iter().map(|s| cx.sym_text(s.name)).collect::<Vec<_>>().as_slice(), ["std" | "core", "cell", "Cell", "new"])
        {
            let want = expected.and_then(|t| cx.tys_ref().cell_elem(t));
            let (v, vt) = self.value(cx, env, *arg, want)?;
            let cell_def = cx.tys_ref().builtins().cell;
            let t = cx.tys().mk_adt(cell_def, &[super::GenericArg::Ty(vt)]);
            return Ok((v, t));
        }
        // `AtomicUsize::new(v)` and the other atomics' `new` are const fns
        // (W-THREADS): the value is the atomic's (its C form is the value).
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() > 2
            && args.len() <= 1
        {
            let names: Vec<&str> = segs.iter().map(|s| cx.sym_text(s.name)).collect();
            if let Some((&"new", ty_path)) = names.split_last()
                && let Some(k) = super::sync::SyncTy::by_path(ty_path)
                && let Some(av) = k.atomic_value()
                && args.len() == 1
            {
                let (v, vt) = self.value(cx, env, args[0], Some(av.ty()))?;
                if !const_ty_compatible(cx.tys_ref(), vt, av.ty()) {
                    return Err(outside(span, "this atomic initializer"));
                }
                let t = super::sync::sync_ty(cx.tys(), k, &[]);
                return Ok((v, t));
            }
            // `Condvar::new()`, `OnceLock::new()`, and `Barrier::new(n)`:
            // a zeroed state (and a Barrier's count).
            if let Some((&"new", ty_path)) = names.split_last()
                && let Some(k @ (super::sync::SyncTy::Condvar | super::sync::SyncTy::OnceLock | super::sync::SyncTy::Barrier)) = super::sync::SyncTy::by_path(ty_path)
            {
                if k == super::sync::SyncTy::Barrier {
                    let [a] = args else { return Err(outside(span, "this Barrier initializer")) };
                    let (v, _) = self.value(cx, env, *a, Some(super::int(super::IntTy::Usize)))?;
                    return Ok((ConstValue::Aggregate(vec![v]), super::sync::sync_ty(cx.tys(), k, &[])));
                }
                if !args.is_empty() || !segs[segs.len() - 2].type_args().is_empty() {
                    return Err(outside(span, "this initializer"));
                }
                let elem = match expected.and_then(|t| cx.tys_ref().adt_first_ty_arg(t)) {
                    Some(e) => e,
                    None if k == super::sync::SyncTy::Condvar => super::ERROR,
                    None => return Err(outside(span, "a `OnceLock::new()` with no known element type")),
                };
                let targs: &[Ty] = if k == super::sync::SyncTy::Condvar { &[] } else { &[elem] };
                return Ok((ConstValue::Aggregate(Vec::new()), super::sync::sync_ty(cx.tys(), k, targs)));
            }
            // `Mutex::new(v)` and `RwLock::new(v)` are const fns too: an
            // unlocked, unpoisoned lock around the value.
            if let Some((&"new", ty_path)) = names.split_last()
                && let Some(k) = super::sync::SyncTy::by_path(ty_path)
                && k.is_lock()
                && args.len() == 1
            {
                let written = segs[segs.len() - 2].type_args();
                let want = match written.first() {
                    Some(_) => return Err(outside(span, "a lock initializer with a turbofish")),
                    None => expected.and_then(|t| cx.tys_ref().adt_first_ty_arg(t)),
                };
                let (v, vt) = self.value(cx, env, args[0], want)?;
                let t = super::sync::sync_ty(cx.tys(), k, &[vt]);
                return Ok((ConstValue::Aggregate(vec![v]), t));
            }
        }
        // `HashMap::with_hasher(s)` and `HashSet::with_hasher(s)` are
        // const fns (Rust 1.85): an empty table around the hasher value.
        // The table type is the expected one (a static, a field, a lock's
        // payload), and the written type must name that kind (directly or
        // through an alias such as rustc-hash's `FxHashMap`).
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && let [.., ty_seg, f] = segs.as_slice()
            && args.len() == 1
            && cx.sym_text(f.name) == "with_hasher"
            && f.type_args().is_empty()
            && let Some(want) = expected
            && let Some((k @ (super::hash::HashTy::HashMap | super::hash::HashTy::HashSet), targs)) = super::hash::hash_parts(cx.tys_ref(), want)
            && (super::hash::HashTy::by_name(cx.sym_text(ty_seg.name)) == Some(k) || cx.alias_hash(ty_seg.name) == Some(k))
        {
            let s = *targs.last().unwrap_or(&ERROR);
            let (hv, ht) = self.value_moved(cx, env, args[0], Some(s))?;
            if !const_ty_compatible(cx.tys_ref(), ht, s) {
                return Err(const_ty_mismatch(span, "this hasher"));
            }
            return Ok((ConstValue::Aggregate(vec![hv]), want));
        }
        // `BuildHasherDefault::new()` is a const fn (Rust 1.85): the unit
        // builder, at the expected `BuildHasherDefault<H>`.
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && let [.., ty_seg, f] = segs.as_slice()
            && args.is_empty()
            && cx.sym_text(f.name) == "new"
            && f.type_args().is_empty()
            && cx.sym_text(ty_seg.name) == "BuildHasherDefault"
            && let Some(want) = expected
            && matches!(super::hash::hash_parts(cx.tys_ref(), want), Some((super::hash::HashTy::BuildHasherDefault, _)))
        {
            return Ok((ConstValue::Unit, want));
        }
        // `mem::discriminant`'s reads in std source (library/core/src/mem.rs):
        // the declared discriminant of the enum value, and the code of
        // the integer type rustc keeps it in (0 and `u8` for a non-enum).
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && let [a, b, c] = segs.as_slice()
            && cx.sym_text(a.name) == "core"
            && cx.sym_text(b.name) == "intrinsics"
            && matches!(cx.sym_text(c.name), "discriminant_value" | "discriminant_kind")
            && let [arg] = args
        {
            let kind = cx.sym_text(c.name) == "discriminant_kind";
            let (v, t) = self.value(cx, env, *arg, None)?;
            // The std fn is generic: its parameter has the type `&T`.
            let t = if self.binds.is_empty() { t } else { subst_binds(cx.tys(), t, &self.binds.clone()) };
            let (v, t) = self.auto_deref(cx, v, t);
            let tys = cx.tys_ref();
            let adt = tys.local_adt(t).filter(|&a| cx.is_enum(a));
            let builtin_enum = tys.option_elem(t).is_some() || tys.result_args(t).is_some();
            let concrete = !tys.flags(t).contains_param() && !matches!(tys.kind(t), TyKind::Ref(..) | TyKind::Error);
            let (disc, holder) = match (&v, adt) {
                (ConstValue::Variant(i, _), Some(a)) => (cx.discriminant(a, *i), cx.adt_repr(a).disc_holder()),
                (ConstValue::Variant(i, _), None) if builtin_enum => (*i as i128, IntTy::Isize),
                (v, None) if !builtin_enum && concrete && !matches!(v, ConstValue::Variant(..)) => (0, IntTy::U8),
                _ => return Err(outside(span, "this discriminant read")),
            };
            return Ok(if kind {
                (ConstValue::Int(super::layout::disc_kind_code(holder) as i128), super::int(IntTy::U8))
            } else {
                (ConstValue::Int(disc), super::int(IntTy::I128))
            });
        }
        // A call through a local (a fn pointer value): rustc rejects
        // fn pointer calls in const contexts. Never resolve the name
        // to an item of the same name instead.
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() == 1
            && env.iter().any(|(n, _, _, _)| *n == segs[0].name)
        {
            return Err(outside(span, "a call through a fn pointer"));
        }
        // `f64::from_bits(n)` and `f32::from_bits(n)` are const fns.
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() == 2
            && cx.sym_text(segs[1].name) == "from_bits"
            && args.len() == 1
        {
            let f = match cx.sym_text(segs[0].name) {
                "f64" => Some((FloatTy::F64, super::int(IntTy::U64))),
                "f32" => Some((FloatTy::F32, super::int(IntTy::U32))),
                _ => None,
            };
            if let Some((f, arg_ty)) = f {
                let (v, _) = self.value(cx, env, args[0], Some(arg_ty))?;
                let ConstValue::Int(i) = v else { return Err(outside(span, "this `from_bits` argument")) };
                let bits = i as u128 as u64;
                let bits = if f == FloatTy::F32 { bits & 0xFFFF_FFFF } else { bits };
                let t = cx.tys().float_ty(f);
                return Ok((ConstValue::Float(bits, f), t));
            }
        }
        // `char::from_u32(n)` (also `core::char::from_u32`) is a
        // const fn answering an `Option<char>`.
        if let Expr::Path(segs) = cx.ast().expr(callee) {
            let names: Vec<String> = segs.iter().map(|s| cx.sym_text(s.name).to_string()).collect();
            let tail2: Vec<&str> = names.iter().rev().take(2).rev().map(|s| s.as_str()).collect();
            if tail2 == ["char", "from_u32"] && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc"))) && args.len() == 1 {
                let n = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                let v = u32::try_from(n).ok().and_then(char::from_u32).map(ConstValue::Char);
                return Ok(self.opt_value(cx, CHAR, v));
            }
            // `char::from_digit(d, radix)` is a const fn too; it panics
            // only above radix 36, which rejects here instead of running.
            if tail2 == ["char", "from_digit"]
                && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc")))
                && args.len() == 2
            {
                let d = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                let r = self.int_arg(cx, env, args[1], super::int(IntTy::U32), span)?;
                let (Some(d), Some(r)) = (u32::try_from(d).ok(), u32::try_from(r).ok()) else {
                    return Err(outside(span, "this `from_digit` call"));
                };
                if r > 36 {
                    return Err(outside(span, "this `from_digit` radix (above 36)"));
                }
                let v = char::from_digit(d, r).map(ConstValue::Char);
                return Ok(self.opt_value(cx, CHAR, v));
            }
            if tail2 == ["char", "from_u32_unchecked"]
                && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc")))
                && args.len() == 1
            {
                let n = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                return match u32::try_from(n).ok().and_then(char::from_u32) {
                    Some(c) => Ok((ConstValue::Char(c), CHAR)),
                    None => Err(outside(span, "this `from_u32_unchecked` (invalid char)")),
                };
            }
            // `{integer}::midpoint(a, b)`, by written name.
            if names.len() == 2 && names[1] == "midpoint" && args.len() == 2 {
                if let Some(it) = IntTy::ALL.iter().find(|i| i.name() == names[0].as_str()).copied() {
                    let t = super::int(it);
                    let a = self.int_arg(cx, env, args[0], t, span)?;
                    let b = self.int_arg(cx, env, args[1], t, span)?;
                    let r = if it.signed() {
                        truncate_to_int(a, it).midpoint(truncate_to_int(b, it))
                    } else {
                        int_from_bits(int_bits(a, it).midpoint(int_bits(b, it)), it)
                    };
                    return Ok((ConstValue::Int(r), t));
                }
            }
            // Integer byte-order associated fns: `u32::from_be_bytes`,
            // `i64::from_le`, and friends, by written names.
            if names.len() == 2 && args.len() == 1 {
                if let Some(it) = IntTy::ALL.iter().find(|i| i.name() == names[0].as_str()).copied() {
                    let width = it.bits();
                    let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
                    let t = super::int(it);
                    match names[1].as_str() {
                        "from_be_bytes" | "from_le_bytes" | "from_ne_bytes" => {
                            let (v, _) = self.value(cx, env, args[0], None)?;
                            let Some(bs) = self.seq_bytes(&v) else { return Err(outside(span, "this call")) };
                            if bs.len() as u32 != width / 8 {
                                return Err(outside(span, "this call"));
                            }
                            let be = names[1] == "from_be_bytes" || (names[1] == "from_ne_bytes" && cfg!(target_endian = "big"));
                            let mut bits: u128 = 0;
                            for (i, &b) in bs.iter().enumerate() {
                                let shift = if be { 8 * (bs.len() - 1 - i) } else { 8 * i };
                                bits |= (b as u128) << shift;
                            }
                            return Ok((ConstValue::Int(int_from_bits(bits & mask, it)), t));
                        }
                        "from_be" | "from_le" => {
                            let n = self.int_arg(cx, env, args[0], t, span)?;
                            let xb = int_bits(n, it);
                            let swap = xb.swap_bytes() >> (128 - width);
                            let want_swap = (names[1] == "from_be") == cfg!(target_endian = "little");
                            return Ok((ConstValue::Int(int_from_bits((if want_swap { swap } else { xb }) & mask, it)), t));
                        }
                        _ => {}
                    }
                }
            }
        }
        match cx.call_target(callee) {
            CallTarget::SizeOf(t) => {
                let l = cx.layout(t).ok_or_else(|| {
                    Diag::new("L0652", span, layout_fail_text(&*cx, "size_of"), "Use a type inside the supported layout grammar.")
                })?;
                Ok((ConstValue::Int(l.size as i128), USIZE))
            }
            CallTarget::AlignOf(t) => {
                let l = cx.layout(t).ok_or_else(|| {
                    Diag::new("L0652", span, layout_fail_text(&*cx, "align_of"), "Use a type inside the supported layout grammar.")
                })?;
                Ok((ConstValue::Int(l.align as i128), USIZE))
            }
            CallTarget::VariantCtor { adt, variant, ty } if adt.0 >= u32::MAX - 1 => {
                // The `Some` and `Ok`/`Err` shims (adt u32::MAX and
                // u32::MAX - 1): the payload type comes from the expected
                // `Option`/`Result` (`Some(5u16)` for an `Option<u8>` is a
                // mismatch, never a silent narrowing), else from the
                // argument (`Some` only).
                let _ = ty;
                let [a] = args else { return Err(outside(span, "this constructor call")) };
                let want = if adt.0 == u32::MAX {
                    expected.and_then(|t| cx.tys_ref().option_elem(t))
                } else {
                    let Some((ok, err)) = expected.and_then(|t| cx.tys_ref().result_args(t)) else {
                        return Err(outside(span, "this `Ok`/`Err` value (type annotations needed)"));
                    };
                    Some(if variant == 0 { ok } else { err })
                };
                let (v, vt) = self.value_moved(cx, env, *a, want)?;
                if let Some(want) = want
                    && !const_ty_compatible(cx.tys_ref(), vt, want)
                {
                    return Err(const_ty_mismatch(cx.ast().expr_span(*a), "this constructor argument"));
                }
                let ty = match (adt.0 == u32::MAX, expected) {
                    (true, _) => {
                        let e = want.unwrap_or(vt);
                        cx.tys().mk_option(e)
                    }
                    (false, Some(t)) => t,
                    (false, None) => ERROR,
                };
                Ok((ConstValue::Variant(variant, vec![v]), ty))
            }
            CallTarget::VariantCtor { adt, variant, ty } => {
                // A user variant knows its field types; check each argument
                // against them. A generic Adt's fields are the template's:
                // substitute the instance's args, from the expected type
                // (`const C: Cow<str> = Cow::Borrowed(..)`) or from type
                // arguments written on the path (`Cow::<str>::Borrowed`),
                // as the struct literal form above does.
                let ty_def = cx.tys_ref().adt_parts(ty).map(|(d, _)| d);
                let (ty, inst) = match expected {
                    Some(t) if ty_def.is_some() && cx.tys_ref().adt_parts(t).map(|(d, _)| d) == ty_def => {
                        let args = cx.tys_ref().adt_parts(t).map(|(_, a)| cx.tys_ref().args(a).to_vec()).unwrap_or_default();
                        (t, Some(args))
                    }
                    _ => {
                        let written: Vec<super::GenericArg> = match cx.ast().expr(callee) {
                            Expr::Path(segs) => segs
                                .iter()
                                .flat_map(|s| s.type_args())
                                .map(|t| super::GenericArg::Ty(cx.resolve_ty(t)))
                                .collect(),
                            _ => Vec::new(),
                        };
                        if written.is_empty() {
                            (ty, None)
                        } else {
                            let ty = match ty_def {
                                Some(d) => cx.tys().mk_adt(d, &written),
                                None => ty,
                            };
                            (ty, Some(written))
                        }
                    }
                };
                let fields: Vec<Ty> = if adt.0 >= u32::MAX - 1 {
                    Vec::new()
                } else {
                    cx.variant_fields(adt, variant)
                        .iter()
                        .map(|f| match &inst {
                            Some(args) => super::subst(cx.tys(), f.1, args),
                            None => f.1,
                        })
                        .collect()
                };
                // A tuple struct constructor is private when any field
                // is; enum variant fields take the enum's visibility.
                if adt.0 < u32::MAX - 1 && !cx.is_enum(adt) {
                    self.check_tuple_ctor(cx, adt, fields.len(), span)?;
                }
                if adt.0 < u32::MAX - 1 {
                    let what = cx.ne_ctor_what(adt, variant);
                    self.check_ne(what, NeKind::Ctor, span)?;
                }
                // A generic Adt with no expected or written args takes
                // them from the argument types (`W(5u32)`).
                let infer = inst.is_none() && adt.0 < u32::MAX - 1 && fields.iter().any(|&f| cx.tys_ref().flags(f).contains_param());
                let mut binds: Vec<Option<Ty>> = Vec::new();
                let mut vals = Vec::new();
                for (i, &a) in args.iter().enumerate() {
                    let want = fields.get(i).copied();
                    let want_now = if infer { want.map(|w| subst_binds(cx.tys(), w, &binds)) } else { want };
                    let (v, vt) = self.value_moved(cx, env, a, want_now)?;
                    if let Some(want) = want {
                        let ok = if infer { bind_params(cx.tys(), want, vt, &mut binds) } else { const_ty_compatible(cx.tys_ref(), vt, want) };
                        if !ok {
                            return Err(const_ty_mismatch(cx.ast().expr_span(a), "this constructor argument"));
                        }
                    }
                    vals.push(v);
                }
                let ty = if infer {
                    cx.adt_instance(adt, &binds).ok_or_else(|| outside(span, "this constructor call (type annotations needed)"))?
                } else {
                    ty
                };
                // A tuple struct builds an aggregate, like its struct
                // literal form; only enum variants (and the shims,
                // whose layout is enum-shaped) build a variant value.
                if adt.0 >= u32::MAX - 1 || cx.is_enum(adt) {
                    Ok((ConstValue::Variant(variant, vals), ty))
                } else {
                    Ok((ConstValue::Aggregate(vals), ty))
                }
            }
            CallTarget::ConstFn(body) => self.run_const_fn(cx, env, body, None, args, span, expected),
            CallTarget::NonConst => Err(nonconst(span, "this function")),
            CallTarget::Unknown if let Some(it) = self.nonzero_new_ty(cx, callee, args, expected) => {
                // `NonZeroU32::new(n)` and kin are const fns (std 1.47):
                // `Some` of the wrapped integer, `None` for zero.
                let t = super::int(it);
                let n = self.int_arg(cx, env, args[0], t, span)?;
                let nz = crate::check::generics::nonzero_ty(cx.tys(), t);
                Ok(self.opt_value(cx, nz, (n != 0).then(|| ConstValue::Aggregate(vec![ConstValue::Int(n)]))))
            }
            CallTarget::Unknown => match cx.ast().expr(callee) {
                Expr::Path(segs) if STD_NONCONST.contains(&path_text(cx, segs).as_str()) => Err(nonconst(span, &path_text(cx, segs))),
                Expr::Path(segs) if segs.len() == 2 && !cx.names_type(segs[0].name) => Err(unknown_type(cx, &segs[0], span)),
                Expr::Path(segs) => Err(outside(span, &format!("the call of `{}`", path_text(cx, segs)))),
                _ => Err(outside(span, "this call")),
            },
        }
    }

    /// The integer type of a `NonZero` constructor call (`NonZeroU32::new`,
    /// `std::num::NonZero::<u8>::new`, or `NonZero::new` at an expected
    /// `Option<NonZero<T>>`), by written names. Callers ask only after
    /// the path resolved to no user fn.
    fn nonzero_new_ty<'a, C: ConstCx<'a>>(&self, cx: &mut C, callee: ExprId, args: &[ExprId], expected: Option<Ty>) -> Option<IntTy> {
        let Expr::Path(segs) = cx.ast().expr(callee) else { return None };
        let [prefix @ .., ty_seg, f] = segs.as_slice() else { return None };
        if args.len() != 1 || cx.sym_text(f.name) != "new" || !f.type_args().is_empty() {
            return None;
        }
        let names: Vec<&str> = prefix.iter().map(|s| cx.sym_text(s.name)).collect();
        if !matches!(names.as_slice(), [] | ["std" | "core", "num"]) || prefix.iter().any(|s| !s.type_args().is_empty()) {
            return None;
        }
        let ty_name = cx.sym_text(ty_seg.name);
        if let Some(it) = ty_name.strip_prefix("NonZero").and_then(|w| IntTy::ALL.iter().find(|i| i.name().eq_ignore_ascii_case(w)).copied()) {
            return ty_seg.type_args().is_empty().then_some(it);
        }
        if ty_name != "NonZero" {
            return None;
        }
        let t = match ty_seg.type_args().as_slice() {
            [a] => cx.resolve_ty(*a),
            [] => {
                let inner = expected.and_then(|t| cx.tys_ref().option_elem(t))?;
                crate::check::generics::nonzero_elem(cx.tys_ref(), inner)?
            }
            _ => return None,
        };
        self.int_ty_of(cx, t)
    }

    /// Runs const fn `body` on `args` (evaluated in the caller's
    /// module, before the call depth moves) and returns its value at
    /// the declared return type. `recv` is a method call's receiver,
    /// already adjusted to the `self` parameter's type: it is the
    /// first argument, and `args` fill the parameters after it.
    #[allow(clippy::too_many_arguments)]
    fn run_const_fn<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        body: ConstFnBody,
        recv: Option<TypedValue>,
        args: &[ExprId],
        span: Span,
        expected: Option<Ty>,
    ) -> Result<TypedValue, Diag> {
        let off = usize::from(recv.is_some());
        if args.len() + off != body.params.len() {
            return Err(outside(span, "this call (wrong number of arguments)"));
        }
        // Arguments evaluate in the caller's module, so they
        // evaluate before the call depth moves.
        // A generic fn's type args come from the expected type
        // and the argument types (`binds`, by param index); its
        // result has its return type with them substituted.
        let generic = body.generic != ConstGeneric::No;
        let mut binds: Vec<Option<Ty>> = Vec::new();
        if generic && let Some(e) = expected {
            let _ = bind_params(cx.tys(), body.ret, e, &mut binds);
        }
        let mut arg_vals: Vec<TypedValue> = Vec::new();
        if let Some((v0, vt)) = recv {
            if let Some(&want) = body.param_tys.first() {
                let ok = if generic { bind_params(cx.tys(), want, vt, &mut binds) } else { const_ty_compatible(cx.tys_ref(), vt, want) };
                if !ok {
                    return Err(const_ty_mismatch(span, "this method receiver"));
                }
            }
            arg_vals.push((v0, body.param_tys.first().copied().unwrap_or(vt)));
        }
        for (i, &a) in args.iter().enumerate() {
            let i = i + off;
            let want = body.param_tys.get(i).copied();
            let want_now = if generic { want.map(|w| subst_binds(cx.tys(), w, &binds)) } else { want };
            self.mut_arg = matches!(cx.ast().expr(a), Expr::Ref { mutable: true, .. }).then_some(a);
            let r = self.value_moved(cx, env, a, want_now);
            self.mut_arg = None;
            let (v0, vt) = r?;
            if let Some(want) = want {
                let ok = if generic { bind_params(cx.tys(), want, vt, &mut binds) } else { const_ty_compatible(cx.tys_ref(), vt, want) };
                if !ok {
                    return Err(const_ty_mismatch(cx.ast().expr_span(a), "this call argument"));
                }
            }
            // The parameter has its declared type inside the body,
            // whatever width the argument literal was written at.
            arg_vals.push((v0, body.param_tys.get(i).copied().unwrap_or(vt)));
        }
        // A `&mut` argument's value is a cloned cell: writes
        // through the parameter land in the clone, so after
        // the body they are copied back to the caller's
        // place (or the caller's own `&mut` cell, for a
        // reborrow passed on). A write-back target is
        // (arg index, target expr, target-is-a-place).
        // Only a plain `&mut T` parameter is written back; a `&mut`
        // inside another parameter value, or in the result, would be a
        // copy whose writes are lost (`mut_ref_outside`). A value with
        // no reference in it holds no `&mut`, whatever its type
        // (`Self { last: None, .. }` of a type with an `Option<&mut T>`).
        for (i, &pt) in body.param_tys.iter().enumerate() {
            let Some((v, _)) = arg_vals.get(i) else { continue };
            let (inner, v) = match (cx.tys_ref().kind(pt), v) {
                (TyKind::Ref(_, m, it), ConstValue::Ref(cell)) if m.is_mut() => (it, &**cell),
                _ => (pt, v),
            };
            if value_has_ref(v) && holds_mut_ref(cx, inner, &mut Vec::new()) {
                return Err(mut_ref_outside(span, "a const fn whose parameter or result holds a `&mut` this way"));
            }
        }
        let ret_holds_mut = holds_mut_ref(cx, body.ret, &mut Vec::new());
        let mut wb_targets: Vec<(usize, ExprId, bool)> = Vec::new();
        for (i, &a) in args.iter().enumerate() {
            let i = i + off;
            let Some(want) = body.param_tys.get(i).copied() else { continue };
            if body.params[i].2.is_some()
                || !matches!(cx.tys_ref().kind(want), TyKind::Ref(_, super::Mut::Mut, _))
                || !matches!(arg_vals[i].0, ConstValue::Ref(_))
            {
                continue;
            }
            match cx.ast().expr(a) {
                Expr::Ref { mutable: true, expr: place, .. } => {
                    if matches!(cx.ast().expr(*place), Expr::Path(_) | Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_)) {
                        wb_targets.push((i, *place, true));
                    }
                }
                _ => wb_targets.push((i, a, false)),
            }
        }
        // Parameter patterns and the body are the callee's
        // code, checked in its own module: run both below
        // depth 0 so the privacy hooks stay out.
        // Rustc caps const evaluation at 128 stack frames,
        // the item itself included, so 127 nested const fn
        // frames is the most this evaluator may enter.
        if self.call_depth >= 127 {
            return Err(Diag::new(
                C_OUTSIDE,
                span,
                "reached the maximum number of const stack frames",
                "Make the const computation shallower, for example with a loop.",
            ));
        }
        self.call_depth += 1;
        if body.has_self {
            self.self_sym = Some(body.params[0].0);
        }
        let mut fenv: Env = Vec::new();
        let mut bind_err: Option<Diag> = None;
        let mut param_fenv_idx: Vec<Option<usize>> = Vec::new();
        for (i, v) in arg_vals.into_iter().enumerate() {
            let (name, mutable, pat) = body.params[i];
            match pat {
                Some(pat) => {
                    // Destructuring a drop parameter destroys
                    // what it does not move out (E0493).
                    if cx.needs_drop(v.1) && !pat_is_whole_binding(cx.ast(), pat) {
                        bind_err = Some(drop_diag(cx, v.1, span));
                        break;
                    }
                    let mut binds = Vec::new();
                    match self.match_pat(cx, &mut fenv, pat, &v.0.clone(), v.1, true, &mut binds) {
                        Ok(true) => fenv.extend(binds),
                        Ok(false) => {
                            bind_err = Some(outside(span, "this call (argument pattern)"));
                            break;
                        }
                        Err(d) => {
                            bind_err = Some(d);
                            break;
                        }
                    }
                }
                None => {
                    param_fenv_idx.push(Some(fenv.len()));
                    fenv.push((name, v, mutable, false));
                    continue;
                }
            }
            param_fenv_idx.push(None);
        }
        // The write-back slots: fenv index, the param cell's
        // address (a body that reassigns the parameter
        // itself replaces the cell, and then no write-back
        // is sound), target expr, target-is-a-place.
        let wb_slots: Vec<(usize, usize, ExprId, bool)> = wb_targets
            .iter()
            .filter_map(|&(i, target, is_place)| {
                let fidx = param_fenv_idx.get(i).copied().flatten()?;
                match &fenv.get(fidx)?.1.0 {
                    ConstValue::Ref(cell) => Some((fidx, cell.as_ref() as *const ConstValue as usize, target, is_place)),
                    _ => None,
                }
            })
            .collect();
        // Every type arg must be known, and the lazy
        // constructors' `F: FnOnce() -> T` must hold.
        let call_ret = if generic {
            // (A bound type may hold the caller's own params, in a
            // generic const fn body: those are fine.)
            let r = subst_binds(cx.tys(), body.ret, &binds);
            let mut used = Vec::new();
            for &t in body.param_tys.iter().chain([&body.ret]) {
                params_in(cx.tys_ref(), t, &mut used);
            }
            if used.iter().any(|&i| binds.get(i as usize).copied().flatten().is_none()) {
                return Err(outside(span, "this generic const fn call (type annotations needed)"));
            }
            if body.generic == ConstGeneric::LazyCtor {
                let holds = match (binds.first().copied().flatten(), binds.get(1).copied().flatten()) {
                    (Some(t), Some(f)) => match cx.tys_ref().kind(f) {
                        TyKind::FnPtr(sig) => {
                            let b = cx.tys_ref().sig(sig);
                            cx.tys_ref().tys_of(b.value.inputs).is_empty() && b.value.output == t && !b.value.is_unsafe && !b.value.extern_c
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if !holds {
                    return Err(outside(span, "this lazy constructor's init fn"));
                }
            }
            // A bounded fn runs when the context proves every bound
            // at these type args (stable const fns cannot call trait
            // methods, so the bounds only gate the call).
            if body.generic == ConstGeneric::Bounded {
                match cx.bounds_hold(body.def, &binds, span) {
                    Some(true) => {}
                    Some(false) => {
                        return Err(Diag::new(
                            "L0612",
                            span,
                            "a trait bound of this const fn call is not satisfied",
                            "Call it with types that meet the fn's bounds.",
                        ));
                    }
                    None => return Err(outside(span, "a call to a generic const fn with these bounds")),
                }
            }
            r
        } else {
            body.ret
        };
        cx.enter_const_fn(body.owner);
        // The callee's literal locals index its own env; its type
        // parameters bind to this call's type args.
        let caller_flex = std::mem::take(&mut self.flex_locals);
        let caller_binds = std::mem::replace(&mut self.binds, if generic { binds.clone() } else { Vec::new() });
        let flow = match bind_err {
            Some(d) => Err(d),
            None => self.block(cx, &mut fenv, body.body, Some(body.ret)),
        };
        self.flex_locals = caller_flex;
        self.binds = caller_binds;
        cx.exit_const_fn();
        self.call_depth -= 1;
        // A parameter of a drop type that the body did not
        // move out is destroyed by the call (E0493).
        if flow.is_ok() {
            self.check_scope_drops(cx, &fenv, 0, span)?;
        }
        let flow = flow?;
        if matches!(flow, Flow::Val(_) | Flow::Return(_)) {
            for &(fidx, addr, target, is_place) in &wb_slots {
                let new_v = match fenv.get(fidx).map(|s| &s.1.0) {
                    Some(ConstValue::Ref(cell)) if cell.as_ref() as *const ConstValue as usize == addr => (**cell).clone(),
                    _ => continue,
                };
                if is_place {
                    self.assign_place(cx, env, target, new_v, span)?;
                } else if let Ok(slot) = self.place_slot(cx, env, target, span)
                    && let ConstValue::Ref(cell) = slot
                {
                    **cell = new_v;
                }
            }
        }
        match flow {
            // The fn body is type-checked as a fn; its value has the
            // declared return type here. A wide (unsuffixed-literal)
            // integer result is range-checked against it first:
            // this is where an untyped local meets its real type.
            Flow::Val(v) | Flow::Return(v) => {
                if ret_holds_mut && value_has_ref(&v.0) {
                    return Err(mut_ref_outside(span, "a const fn whose parameter or result holds a `&mut` this way"));
                }
                if let (ConstValue::Int(i), Some(it)) = (&v.0, self.int_ty_of(cx, body.ret))
                    && v.1 != body.ret
                {
                    let ok = if it.bits() >= 128 {
                        true
                    } else if it.signed() {
                        fits(*i, it)
                    } else {
                        *i >= 0 && (*i as u128) <= it.max128()
                    };
                    if !ok {
                        return Err(outside(span, "this const fn result (overflow)"));
                    }
                    return Ok((ConstValue::Int(int_from_bits(int_bits(*i, it), it)), body.ret));
                }
                Ok((v.0, call_ret))
            }
            _ => Err(outside(span, "control flow out of a const fn")),
        }
    }

    /// The `lo..hi` window of a sequence const value (through a
    /// promoted reference): a blob windows in O(1), an aggregate
    /// clones only the window. None when the window is out of
    /// bounds or the value is not a sequence. This backs const
    /// slicing forms rustc allows (`split_at`); range indexing
    /// itself is not const-stable in rustc and stays outside.
    fn sub_seq(&self, v: &ConstValue, lo: usize, hi: usize) -> Option<ConstValue> {
        if lo > hi || hi > self.seq_len(v)? {
            return None;
        }
        match v {
            ConstValue::Bytes(b) => b.sub(lo, hi).map(ConstValue::Bytes),
            ConstValue::Aggregate(vals) => Some(ConstValue::Aggregate(vals[lo..hi].to_vec())),
            ConstValue::Repeat(x, _) => Some(ConstValue::Repeat(x.clone(), (hi - lo) as u64)),
            ConstValue::Ref(inner) => self.sub_seq(inner, lo, hi),
            _ => None,
        }
    }

    /// The element count of a slice or array const value, through a
    /// promoted reference if the value carries one.
    /// `base[index]` when `base` names a local holding an array, a slice,
    /// or a reference to one: the element, read without cloning the
    /// sequence. None when the base is not such a local.
    fn index_local<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, base: ExprId, index: ExprId, span: Span) -> Result<Option<TypedValue>, Diag> {
        if local_value(cx, env, base).is_none() {
            return Ok(None);
        }
        let (iv, _) = self.value(cx, env, index, Some(USIZE))?;
        let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
        let i = usize::try_from(i).map_err(|_| outside(span, "this index"))?;
        let Some((v, t)) = local_value(cx, env, base) else { return Ok(None) };
        let (mut v, mut t) = (v, *t);
        while let (ConstValue::Ref(inner), TyKind::Ref(_, _, it)) = (v, cx.tys_ref().kind(t)) {
            v = inner;
            t = it;
        }
        let elem = match cx.tys_ref().kind(t) {
            TyKind::Array(el, _) | TyKind::Slice(el) => el,
            _ => return Ok(None),
        };
        let got = match v {
            ConstValue::Aggregate(vals) => vals.get(i).cloned(),
            ConstValue::Repeat(v, n) if (i as u64) < *n => Some((**v).clone()),
            ConstValue::Bytes(b) => b.as_slice().get(i).map(|&x| ConstValue::Int(x as i128)),
            ConstValue::Aggregate(_) | ConstValue::Repeat(..) => None,
            _ => return Ok(None),
        };
        match got {
            Some(g) => Ok(Some((g, elem))),
            None => Err(outside(span, "this index (out of bounds)")),
        }
    }

    /// `ITEM[i]` for a const or static item base, read in place
    /// (`ConstCx::const_item_ref`): the general path clones the whole
    /// item value per read, so many statics that index one big table
    /// were quadratic. Same answers as the general path; None (before
    /// the index is evaluated) for any shape it does not cover.
    fn index_item<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, base: ExprId, index: ExprId, span: Span) -> Result<Option<TypedValue>, Diag> {
        let Expr::Path(segs) = cx.ast().expr(base) else { return Ok(None) };
        let [seg] = segs.as_slice() else { return Ok(None) };
        let (name, at) = (seg.name, cx.ast().expr_span(base));
        if env.iter().any(|(n, _, _, _)| *n == name) {
            return Ok(None);
        }
        // The value as `deref_value` sees it, and its element type.
        fn peel<'v, T: TyIntern>(tys: &T, v: &'v ConstValue, t: Ty) -> Option<(&'v ConstValue, Ty)> {
            let (v, t) = match (v, tys.kind(t)) {
                (ConstValue::Ref(inner), TyKind::Ref(_, _, it)) => (&**inner, it),
                _ => (v, t),
            };
            let elem = match tys.kind(t) {
                TyKind::Array(el, _) | TyKind::Slice(el) => el,
                TyKind::Ref(_, _, inner) => match tys.kind(inner) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => el,
                    _ => return None,
                },
                _ => return None,
            };
            matches!(v, ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Bytes(_)).then_some((v, elem))
        }
        // The first read evaluates the item (`const_item` reports its
        // errors); later reads find it in place.
        if cx.const_item_ref(name, at).is_none() && cx.const_item(name, at).is_none() {
            return Ok(None);
        }
        let Some((v, t)) = cx.const_item_ref(name, at) else { return Ok(None) };
        if peel(cx.tys_ref(), v, t).is_none() {
            return Ok(None);
        }
        self.check_temp_drop(cx, env, base, t, span)?;
        let (iv, _) = self.value(cx, env, index, Some(USIZE))?;
        let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
        let i = usize::try_from(i).map_err(|_| outside(span, "this index"))?;
        let Some((v, t)) = cx.const_item_ref(name, at) else { return Ok(None) };
        let Some((v, elem)) = peel(cx.tys_ref(), v, t) else { return Ok(None) };
        let got = match v {
            ConstValue::Aggregate(vals) => vals.get(i).cloned(),
            ConstValue::Repeat(v, n) if (i as u64) < *n => Some((**v).clone()),
            ConstValue::Bytes(b) => b.as_slice().get(i).map(|&x| ConstValue::Int(x as i128)),
            _ => None,
        };
        match got {
            Some(g) => Ok(Some((g, elem))),
            None => Err(outside(span, "this index (out of bounds)")),
        }
    }

    fn seq_len(&self, v: &ConstValue) -> Option<usize> {
        match v {
            ConstValue::Aggregate(vals) => Some(vals.len()),
            ConstValue::Repeat(_, n) => Some(*n as usize),
            ConstValue::Bytes(b) => Some(b.len()),
            ConstValue::Ref(inner) => self.seq_len(inner),
            _ => None,
        }
    }

    /// The elements of a slice or array const value as bytes, when
    /// every element is a `u8` integer.
    fn seq_bytes(&self, v: &ConstValue) -> Option<Vec<u8>> {
        match v {
            ConstValue::Aggregate(vals) => {
                let mut out = Vec::with_capacity(vals.len());
                for x in vals {
                    match x {
                        ConstValue::Int(i) => out.push(u8::try_from(*i).ok()?),
                        _ => return None,
                    }
                }
                Some(out)
            }
            ConstValue::Repeat(x, n) => match **x {
                ConstValue::Int(i) => Some(vec![u8::try_from(i).ok()?; *n as usize]),
                _ => None,
            },
            ConstValue::Bytes(b) => Some(b.as_slice().to_vec()),
            ConstValue::Ref(inner) => self.seq_bytes(inner),
            _ => None,
        }
    }

    /// An `Option` const value at a fresh `Option<elem>` type.
    fn opt_value<'a, C: ConstCx<'a>>(&self, cx: &mut C, elem: Ty, v: Option<ConstValue>) -> TypedValue {
        let t = cx.tys().mk_option(elem);
        match v {
            Some(v) => (ConstValue::Variant(1, vec![v]), t),
            None => (ConstValue::Variant(0, Vec::new()), t),
        }
    }

    /// Primitive method calls in const position: the `str`, slice,
    /// integer, char, float, and `Option` methods rustc marks const
    /// (inherent ones; conditionally-const trait methods such as
    /// `Ord::max` and `From::from` stay rejected, as rustc rejects
    /// them in plain constants). Anything else keeps the outside
    /// error, so a wrong receiver or a non-const method never
    /// evaluates to a made-up value.
    fn method_call<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        recv_e: ExprId,
        name: Sym,
        args: &[ExprId],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let name_sym = name;
        let name = cx.sym_text(name).to_string();
        let outside_err = || outside(span, &format!("the method call `{name}`"));
        // `len` of a local sequence, read in place (see `index_local`).
        if name == "len"
            && args.is_empty()
            && let Some((v, _)) = local_value(cx, env, recv_e)
            && let Some(n) = self.seq_len(v)
        {
            return Ok((ConstValue::Int(n as i128), USIZE));
        }
        let (rv, rt) = self.value_place(cx, env, recv_e, None)?;
        self.check_temp_drop(cx, env, recv_e, rt, span)?;
        // An inherent method of a user type runs as a const fn call,
        // with the receiver adjusted to its `self` parameter as
        // rustc's autoref and autoderef do.
        let mut base_t = rt;
        let mut refs = 0u32;
        while let TyKind::Ref(_, _, it) = cx.tys_ref().kind(base_t) {
            base_t = it;
            refs += 1;
        }
        if cx.tys_ref().local_adt(base_t).is_some() {
            match cx.method_target(base_t, name_sym) {
                CallTarget::Unknown => {}
                target => {
                    if self.call_depth == 0 && cx.method_private(base_t, name_sym) {
                        return Err(Diag::new(
                            "L0510",
                            span,
                            format!("method `{name}` is private"),
                            "Make the method `pub(crate)` (the smallest widening that works).",
                        ));
                    }
                    let CallTarget::ConstFn(body) = target else { return Err(nonconst(span, &name)) };
                    let recv = self.method_receiver(cx, env, recv_e, (rv, rt), refs, &body, span)?;
                    return self.run_const_fn(cx, env, body, Some(recv), args, span, expected);
                }
            }
        }
        // `Cell::get` and `Cell::into_inner` are const fns: a Cell's
        // value is its content's (see `Cell::new` in `call`).
        if let Some(elem) = cx.tys_ref().cell_elem(base_t)
            && matches!(name.as_str(), "get" | "into_inner")
            && args.is_empty()
        {
            let (v, _) = self.auto_deref(cx, rv.clone(), rt);
            return Ok((v, elem));
        }
        // An inherent integer method on an unpinned receiver is
        // ambiguous (rustc E0689), even where the surroundings
        // would pin the type later: the body checker reports the
        // same shape as L0111. The `Ord` methods `min`, `max`, and
        // `clamp` hold for every integer type, so they stay.
        if matches!(rv, ConstValue::Int(_))
            && flex_int_expr(cx.ast(), recv_e)
            && !matches!(name.as_str(), "min" | "max" | "clamp")
        {
            return Err(Diag::new(
                "L0111",
                span,
                format!("cannot call method `{name}` on an integer whose type is not known yet"),
                "Add a type suffix such as `5i64`, or a type annotation on the variable.",
            ));
        }
        // `NonZero::get` is a const fn: the wrapped integer.
        if name == "get"
            && args.is_empty()
            && let Some(elem) = crate::check::generics::nonzero_elem(cx.tys_ref(), base_t)
        {
            let (v, _) = self.auto_deref(cx, rv.clone(), rt);
            if let ConstValue::Aggregate(f) = v
                && let [n @ ConstValue::Int(_)] = f.as_slice()
            {
                return Ok((n.clone(), elem));
            }
            return Err(outside_err());
        }
        let no_args = |args: &[ExprId]| args.is_empty();
        match &rv {
            ConstValue::Str(_) | ConstValue::StrBytes(_) => {
                let text = match &rv {
                    ConstValue::Str(i) => cx.ast().strings[*i as usize].clone(),
                    ConstValue::StrBytes(b) => String::from_utf8(b.as_slice().to_vec()).map_err(|_| outside_err())?,
                    _ => unreachable!(),
                };
                let bytes = text.as_bytes();
                match name.as_str() {
                    // `str::split_at` is a const fn; off a char
                    // boundary or past the end it panics, which is a
                    // const evaluation error (rustc E0080).
                    "split_at" if args.len() == 1 => {
                        let mid = self.int_arg(cx, env, args[0], USIZE, span)?;
                        let Some(mid) = usize::try_from(mid).ok().filter(|&m| text.is_char_boundary(m)) else {
                            return Err(outside(span, "this `split_at` (the index is not a char boundary of the string)"));
                        };
                        let (a, b) = text.split_at(mid);
                        let part = |x: &str| ConstValue::StrBytes(ast::ByteBlob::new(x.as_bytes().to_vec()));
                        let ts = cx.tys().intern_tys(&[REF_STR, REF_STR]);
                        let t = cx.tys().intern(TyKind::Tuple(ts));
                        Ok((ConstValue::Aggregate(vec![part(a), part(b)]), t))
                    }
                    "len" if no_args(args) => Ok((ConstValue::Int(bytes.len() as i128), USIZE)),
                    "is_empty" if no_args(args) => Ok((ConstValue::Bool(bytes.is_empty()), BOOL)),
                    "is_ascii" if no_args(args) => Ok((ConstValue::Bool(bytes.iter().all(|b| b.is_ascii())), BOOL)),
                    "as_bytes" if no_args(args) => {
                        // One blob for the string's bytes, so a hash
                        // over a large `include_str!` stays linear.
                        let slice = cx.tys().intern(TyKind::Slice(super::int(IntTy::U8)));
                        let t = cx.tys().mk_ref(false, slice);
                        Ok((ConstValue::Bytes(ast::ByteBlob::new(bytes.to_vec())), t))
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Int(x) => {
                let x = *x;
                self.int_method(cx, env, x, rt, &name, args, expected, span)
            }
            ConstValue::Char(c) => {
                let c = *c;
                self.char_method(cx, env, c, &name, args, span)
            }
            ConstValue::Float(bits, f) => {
                let (bits, f) = (*bits, *f);
                match name.as_str() {
                    "to_bits" if no_args(args) => {
                        let it = if f == FloatTy::F32 { IntTy::U32 } else { IntTy::U64 };
                        Ok((ConstValue::Int(bits as i128), super::int(it)))
                    }
                    "abs" if no_args(args) => {
                        let sign = if f == FloatTy::F32 { 1u64 << 31 } else { 1u64 << 63 };
                        Ok((ConstValue::Float(bits & !sign, f), rt))
                    }
                    "max" | "min" if args.len() == 1 => {
                        let (av, _) = self.value(cx, env, args[0], Some(rt))?;
                        let ConstValue::Float(ab, _) = av else { return Err(outside_err()) };
                        let r = match f {
                            FloatTy::F64 => {
                                let (x, y) = (f64::from_bits(bits), f64::from_bits(ab));
                                if name == "max" { x.max(y).to_bits() } else { x.min(y).to_bits() }
                            }
                            FloatTy::F32 => {
                                let (x, y) = (f32::from_bits(bits as u32), f32::from_bits(ab as u32));
                                if name == "max" { x.max(y).to_bits() as u64 } else { x.min(y).to_bits() as u64 }
                            }
                        };
                        Ok((ConstValue::Float(r, f), rt))
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Variant(variant, vals) if cx.tys_ref().option_elem(rt).is_some() => {
                let (variant, vals) = (*variant, vals.clone());
                let elem = cx.tys_ref().option_elem(rt).unwrap_or(ERROR);
                match name.as_str() {
                    "is_some" if no_args(args) => Ok((ConstValue::Bool(variant == 1), BOOL)),
                    "is_none" if no_args(args) => Ok((ConstValue::Bool(variant != 1), BOOL)),
                    "unwrap" if no_args(args) => {
                        if variant == 1 && vals.len() == 1 {
                            Ok((vals.into_iter().next().unwrap(), elem))
                        } else {
                            Err(outside(span, "this `unwrap` on `None`"))
                        }
                    }
                    "expect" if args.len() == 1 => {
                        let _ = self.value(cx, env, args[0], None)?;
                        if variant == 1 && vals.len() == 1 {
                            Ok((vals.into_iter().next().unwrap(), elem))
                        } else {
                            Err(outside(span, "this `expect` on `None`"))
                        }
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Bytes(_) | ConstValue::Ref(_) => {
                // A slice or array receiver. The element type comes
                // from the receiver type, through its reference.
                let elem = match cx.tys_ref().kind(rt) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    TyKind::Ref(_, _, inner) => match cx.tys_ref().kind(inner) {
                        TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(elem) = elem else { return Err(outside_err()) };
                let _ = elem;
                match name.as_str() {
                    "len" if no_args(args) => match self.seq_len(&rv) {
                        Some(n) => Ok((ConstValue::Int(n as i128), USIZE)),
                        None => Err(outside_err()),
                    },
                    "is_empty" if no_args(args) => match self.seq_len(&rv) {
                        Some(n) => Ok((ConstValue::Bool(n == 0), BOOL)),
                        None => Err(outside_err()),
                    },
                    "is_ascii" if no_args(args) && self.int_ty_of(cx, elem) == Some(IntTy::U8) => match self.seq_bytes(&rv) {
                        Some(bs) => Ok((ConstValue::Bool(bs.iter().all(|b| b.is_ascii())), BOOL)),
                        None => Err(outside_err()),
                    },
                    // `split_at` is a const fn in core; a mid past
                    // the end panics there, so it rejects here. A
                    // blob receiver splits by moving two windows.
                    "split_at" if args.len() == 1 => {
                        let len = self.seq_len(&rv).ok_or_else(outside_err)?;
                        let mid = self.int_arg(cx, env, args[0], USIZE, span)?;
                        let mid = usize::try_from(mid).map_err(|_| outside_err())?;
                        let lo_v = self.sub_seq(&rv, 0, mid).ok_or_else(|| outside(span, "this `split_at` (out of bounds)"))?;
                        let hi_v = self.sub_seq(&rv, mid, len).ok_or_else(outside_err)?;
                        let sref = {
                            let s = cx.tys().intern(TyKind::Slice(elem));
                            cx.tys().mk_ref(false, s)
                        };
                        let tt = cx.tys().intern_tys(&[sref, sref]);
                        let t = cx.tys().intern(TyKind::Tuple(tt));
                        Ok((ConstValue::Aggregate(vec![lo_v, hi_v]), t))
                    }
                    _ => Err(outside_err()),
                }
            }
            _ => Err(outside_err()),
        }
    }

    /// The receiver value a const method's `self` parameter takes:
    /// `recv` (the value of `recv_e`, behind `refs` references) with
    /// one shared borrow for `&self`, or by value for `self`. A by-value
    /// receiver behind a reference must be `Copy` (rustc E0507); one
    /// that is not moves out of its local, and any other non-`Copy`
    /// place (a field, a static) stays outside the bound.
    #[allow(clippy::too_many_arguments)]
    fn method_receiver<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        recv_e: ExprId,
        recv: TypedValue,
        refs: u32,
        body: &ConstFnBody,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let by_ref = body.param_tys.first().is_some_and(|&t| matches!(cx.tys_ref().kind(t), TyKind::Ref(..)));
        let (mut v, mut t) = recv;
        let keep = usize::from(by_ref && refs > 0) as u32;
        for _ in keep..refs {
            match (v, cx.tys_ref().kind(t)) {
                (ConstValue::Ref(inner), TyKind::Ref(_, _, it)) => (v, t) = (*inner, it),
                _ => return Err(outside(span, "this method receiver")),
            }
        }
        if by_ref {
            // `&mut T` reborrows as `&T`.
            let inner = match cx.tys_ref().kind(t) {
                TyKind::Ref(_, _, it) => it,
                _ => {
                    v = ConstValue::Ref(Box::new(v));
                    t
                }
            };
            return Ok((v, cx.tys().mk_ref(false, inner)));
        }
        if cx.is_copy(t) {
            return Ok((v, t));
        }
        if refs > 0 {
            return Err(Diag::new(
                "L0305",
                span,
                format!("cannot move out of a shared reference: `{}` is not `Copy`", cx.ty_text(t)),
                "Take `&self` in the method, or clone the value first.",
            ));
        }
        // A non-`Copy` receiver by value: a fresh value, or a move out
        // of a local (or `self`).
        let local = match cx.ast().expr(recv_e) {
            Expr::Path(segs) if segs.len() == 1 && !segs[0].has_args() => Some(segs[0].name),
            Expr::SelfValue => self.self_sym,
            _ => None,
        };
        if let Some(slot) = local.and_then(|n| env.iter_mut().rev().find(|(m, _, _, _)| *m == n)) {
            slot.3 = true;
        } else if self.is_place(cx, env, recv_e) {
            return Err(outside(span, "a by-value method receiver that moves out of a place"));
        }
        Ok((v, t))
    }

    /// One integer argument of a const method call, evaluated at
    /// the argument's own type.
    fn int_arg<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        e: ExprId,
        ty: Ty,
        span: Span,
    ) -> Result<i128, Diag> {
        let (v, _) = self.value(cx, env, e, Some(ty))?;
        match v {
            ConstValue::Int(i) => Ok(i),
            _ => Err(outside(span, "method calls")),
        }
    }

    /// Inherent integer methods in const position. Every operation
    /// runs at the receiver's own width, like `int_op`: the plain
    /// forms error on overflow (rustc E0080), the `checked_` forms
    /// answer `None`, and the `saturating_` and `wrapping_` forms
    /// clamp and wrap. Signed-only methods reject unsigned
    /// receivers and the reverse, so a call rustc would not type
    /// never evaluates here either.
    fn int_method<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        x: i128,
        rt: Ty,
        name: &str,
        args: &[ExprId],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        // `u8` methods that are not integer methods at all.
        if self.int_ty_of(cx, rt) == Some(IntTy::U8) && (name.starts_with("is_ascii") || name.starts_with("to_ascii")) {
            if args.is_empty() {
                let b = x as u8;
                let bool_v = |v: bool| Ok((ConstValue::Bool(v), BOOL));
                return match name {
                    "is_ascii" => bool_v(b.is_ascii()),
                    "is_ascii_alphabetic" => bool_v(b.is_ascii_alphabetic()),
                    "is_ascii_alphanumeric" => bool_v(b.is_ascii_alphanumeric()),
                    "is_ascii_digit" => bool_v(b.is_ascii_digit()),
                    "is_ascii_whitespace" => bool_v(b.is_ascii_whitespace()),
                    "is_ascii_uppercase" => bool_v(b.is_ascii_uppercase()),
                    "is_ascii_lowercase" => bool_v(b.is_ascii_lowercase()),
                    "is_ascii_hexdigit" => bool_v(b.is_ascii_hexdigit()),
                    "is_ascii_punctuation" => bool_v(b.is_ascii_punctuation()),
                    "is_ascii_graphic" => bool_v(b.is_ascii_graphic()),
                    "is_ascii_control" => bool_v(b.is_ascii_control()),
                    "to_ascii_lowercase" => Ok((ConstValue::Int(b.to_ascii_lowercase() as i128), rt)),
                    "to_ascii_uppercase" => Ok((ConstValue::Int(b.to_ascii_uppercase() as i128), rt)),
                    _ => Err(outside_err()),
                };
            }
        }
        // The receiver type runs the operation. A wide (i128)
        // receiver from an unsuffixed literal keeps running wide,
        // like `int_op`; the item coercion range-checks the result
        // where it meets its declared type.
        let _ = expected;
        let it = self.int_ty_of(cx, rt).unwrap_or(IntTy::I128);
        let signed = it.signed();
        let width = it.bits();
        let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
        let xb = int_bits(x, it);
        let xs = truncate_to_int(x, it);
        let lo = int_min(it);
        let hi_s: i128 = if width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        let over = || outside(span, "this method call (overflow or division by zero)");
        let int_v = |v: i128| Ok((ConstValue::Int(v), rt));
        let bits_v = |u: u128| Ok((ConstValue::Int(int_from_bits(u & mask, it)), rt));
        let bool_v = |b: bool| Ok((ConstValue::Bool(b), BOOL));
        let u32_v = |v: u32| Ok((ConstValue::Int(v as i128), super::int(IntTy::U32)));
        // The unsigned counterpart type, for `unsigned_abs` and `abs_diff`.
        let unsigned_it = match it {
            IntTy::I8 => IntTy::U8,
            IntTy::I16 => IntTy::U16,
            IntTy::I32 => IntTy::U32,
            IntTy::I64 => IntTy::U64,
            IntTy::Isize => IntTy::Usize,
            IntTy::I128 => IntTy::U128,
            u => u,
        };
        if args.is_empty() {
            return match name {
                "abs" if signed => {
                    if xs == lo {
                        Err(over())
                    } else {
                        int_v(xs.abs())
                    }
                }
                "unsigned_abs" if signed => Ok((ConstValue::Int(int_from_bits(xs.unsigned_abs(), unsigned_it)), super::int(unsigned_it))),
                "signum" if signed => int_v(xs.signum()),
                "is_positive" if signed => bool_v(xs > 0),
                "is_negative" if signed => bool_v(xs < 0),
                "count_ones" => u32_v(xb.count_ones()),
                "count_zeros" => u32_v(width - xb.count_ones()),
                "leading_zeros" => u32_v(xb.leading_zeros() - (128 - width)),
                "trailing_zeros" => u32_v(if xb == 0 { width } else { xb.trailing_zeros() }),
                "leading_ones" => u32_v((!xb & mask).leading_zeros() - (128 - width)),
                "trailing_ones" => u32_v(if (!xb & mask) == 0 { width } else { (!xb & mask).trailing_zeros() }),
                "reverse_bits" => bits_v(xb.reverse_bits() >> (128 - width)),
                "swap_bytes" => bits_v(xb.swap_bytes() >> (128 - width)),
                "to_be" => bits_v(if cfg!(target_endian = "little") { xb.swap_bytes() >> (128 - width) } else { xb }),
                "to_le" => bits_v(if cfg!(target_endian = "little") { xb } else { xb.swap_bytes() >> (128 - width) }),
                "to_be_bytes" | "to_le_bytes" | "to_ne_bytes" => {
                    let n = (width / 8) as usize;
                    let be = name == "to_be_bytes" || (name == "to_ne_bytes" && cfg!(target_endian = "big"));
                    let vals: Vec<ConstValue> = (0..n)
                        .map(|i| {
                            let shift = if be { 8 * (n - 1 - i) } else { 8 * i };
                            ConstValue::Int(((xb >> shift) & 0xFF) as i128)
                        })
                        .collect();
                    let c = cx.tys().intern_const(super::ConstKind::Int(n as u128));
                    let t = cx.tys().intern(TyKind::Array(super::int(IntTy::U8), c));
                    Ok((ConstValue::Aggregate(vals), t))
                }
                "checked_neg" => {
                    let r = if signed {
                        if xs == lo { None } else { Some(-xs) }
                    } else if xb == 0 {
                        Some(0)
                    } else {
                        None
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                // Signed only in std (rustc E0599 on unsigned types).
                "saturating_neg" if signed => int_v(if xs == lo { hi_s } else { -xs }),
                "wrapping_neg" => bits_v(0u128.wrapping_sub(xb)),
                "strict_neg" => {
                    if (signed && xs == lo) || (!signed && xb != 0) {
                        Err(over())
                    } else if signed {
                        int_v(-xs)
                    } else {
                        int_v(0)
                    }
                }
                "strict_abs" if signed => {
                    if xs == lo {
                        Err(over())
                    } else {
                        int_v(xs.abs())
                    }
                }
                "checked_abs" if signed => {
                    let r = if xs == lo { None } else { Some(xs.abs()) };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "saturating_abs" if signed => int_v(if xs == lo { hi_s } else { xs.abs() }),
                "wrapping_abs" if signed => int_v(if xs == lo { lo } else { xs.abs() }),
                "isqrt" if !signed => bits_v(xb.isqrt()),
                "isqrt" if signed => {
                    if xs < 0 {
                        Err(over())
                    } else {
                        int_v((xs as u128).isqrt() as i128)
                    }
                }
                "checked_isqrt" if signed => {
                    let r = if xs < 0 { None } else { Some((xs as u128).isqrt() as i128) };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "cast_signed" if !signed => Ok((ConstValue::Int(int_from_bits(xb, it.counterpart())), super::int(it.counterpart()))),
                "cast_unsigned" if signed => Ok((ConstValue::Int(int_from_bits(xb, it.counterpart())), super::int(it.counterpart()))),
                "bit_width" if !signed => u32_v(width - (xb.leading_zeros() - (128 - width))),
                "highest_one" => {
                    let r = if xb == 0 { None } else { Some(width - 1 - (xb.leading_zeros() - (128 - width))) };
                    Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                }
                "lowest_one" => {
                    let r = if xb == 0 { None } else { Some(xb.trailing_zeros()) };
                    Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                }
                "isolate_lowest_one" => bits_v(xb & 0u128.wrapping_sub(xb)),
                "isolate_highest_one" => {
                    if xb == 0 {
                        bits_v(0)
                    } else {
                        bits_v(1u128 << (width - 1 - (xb.leading_zeros() - (128 - width))))
                    }
                }
                "is_power_of_two" if !signed => bool_v(xb != 0 && (xb & (xb - 1)) == 0),
                "next_power_of_two" if !signed => {
                    if xb == 0 {
                        bits_v(1)
                    } else {
                        let p = 1u128.checked_shl(128 - (xb - 1).leading_zeros()).unwrap_or(0);
                        if p == 0 || p > mask {
                            Err(over())
                        } else {
                            bits_v(p)
                        }
                    }
                }
                "ilog2" | "ilog10" => {
                    if xb == 0 || (signed && xs < 0) {
                        Err(outside(span, "this method call (logarithm of a non-positive value)"))
                    } else if name == "ilog2" {
                        u32_v(127 - xb.leading_zeros())
                    } else {
                        u32_v(xb.ilog10())
                    }
                }
                "checked_ilog2" | "checked_ilog10" => {
                    let r = if xb == 0 || (signed && xs < 0) {
                        None
                    } else if name == "checked_ilog2" {
                        Some(127 - xb.leading_zeros())
                    } else {
                        Some(xb.ilog10())
                    };
                    Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                }
                _ => Err(outside_err()),
            };
        }
        if args.len() != 1 {
            return Err(outside_err());
        }
        self.int_method_arg(cx, env, it, rt, xs, xb, name, args[0], span)
    }

    /// The one-argument integer methods: the arithmetic families,
    /// shifts and rotates, and the euclid and difference forms.
    #[allow(clippy::too_many_arguments)]
    fn int_method_arg<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        it: IntTy,
        rt: Ty,
        xs: i128,
        xb: u128,
        name: &str,
        arg: ExprId,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        let over = || outside(span, "this method call (overflow or division by zero)");
        let signed = it.signed();
        let width = it.bits();
        let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
        let lo = int_min(it);
        let hi_s: i128 = if width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        let int_v = |v: i128| Ok((ConstValue::Int(v), rt));
        let bits_v = |u: u128| Ok((ConstValue::Int(int_from_bits(u & mask, it)), rt));
        // The mixed-sign families and `checked_signed_diff`: the
        // argument has the other signedness, and the exact result
        // runs in i128 (exact below 128-bit widths, where the
        // checker keeps these). The overflowing forms give the
        // wrapped value and whether it overflowed.
        // std has the `_unsigned` forms on signed types only and the
        // `_signed` forms on unsigned types only (rustc E0599 otherwise).
        let suffix_ok = if signed { name.ends_with("_unsigned") } else { name.ends_with("_signed") && name != "checked_signed_diff" };
        let mixed_kind = ["checked_", "wrapping_", "saturating_", "strict_", "overflowing_"]
            .iter()
            .find(|p| suffix_ok && (name.starts_with(&format!("{p}add_")) || name.starts_with(&format!("{p}sub_"))));
        if let Some(kind) = mixed_kind {
            if width >= 128 {
                return Err(outside_err());
            }
            let sub = name.contains("_sub_");
            let other = it.counterpart();
            let y = self.int_arg(cx, env, arg, super::int(other), span)?;
            let exact: i128 = if signed {
                let mag = int_bits(y, other) as i128;
                if sub { xs - mag } else { xs + mag }
            } else {
                let sv = truncate_to_int(y, other);
                if sub { xb as i128 - sv } else { xb as i128 + sv }
            };
            let fits = if signed { exact >= lo && exact <= hi_s } else { exact >= 0 && (exact as u128) <= mask };
            return match *kind {
                "checked_" => Ok(self.opt_value(cx, rt, fits.then_some(ConstValue::Int(int_from_bits(exact as u128 & mask, it))))),
                "wrapping_" => bits_v(exact as u128),
                "overflowing_" => {
                    let ts = cx.tys().intern_tys(&[rt, BOOL]);
                    let t = cx.tys().intern(TyKind::Tuple(ts));
                    let v = ConstValue::Int(int_from_bits(exact as u128 & mask, it));
                    Ok((ConstValue::Aggregate(vec![v, ConstValue::Bool(!fits)]), t))
                }
                "saturating_" => {
                    if signed {
                        int_v(exact.clamp(lo, hi_s))
                    } else if exact < 0 {
                        bits_v(0)
                    } else {
                        bits_v((exact as u128).min(mask))
                    }
                }
                _ => {
                    if fits {
                        bits_v(exact as u128)
                    } else {
                        Err(over())
                    }
                }
            };
        }
        if name == "checked_signed_diff" && !signed && width < 128 {
            let other = it.counterpart();
            let y = self.int_arg(cx, env, arg, rt, span)?;
            let exact = xb as i128 - int_bits(y, it) as i128;
            let slo: i128 = -(1i128 << (width - 1));
            let shi: i128 = (1i128 << (width - 1)) - 1;
            let r = (exact >= slo && exact <= shi).then_some(ConstValue::Int(exact));
            return Ok(self.opt_value(cx, super::int(other), r));
        }
        // Shifts, rotates, powers, and logarithms take a `u32`.
        if matches!(
            name,
            "pow" | "checked_pow" | "saturating_pow" | "wrapping_pow" | "checked_shl" | "checked_shr" | "wrapping_shl"
                | "wrapping_shr" | "unbounded_shl" | "unbounded_shr" | "strict_pow" | "strict_shl" | "strict_shr" | "rotate_left" | "rotate_right" | "ilog" | "checked_ilog"
        ) {
            let a = self.int_arg(cx, env, arg, super::int(IntTy::U32), span)?;
            let amt = u32::try_from(a).map_err(|_| outside_err())?;
            return match name {
                "pow" => {
                    let r = if signed { xs.checked_pow(amt).filter(|&r| fits(r, it)) } else { None };
                    let r = if signed { r } else { xb.checked_pow(amt).filter(|&r| r <= mask).map(|r| int_from_bits(r, it)) };
                    match r {
                        Some(r) => int_v(r),
                        None => Err(over()),
                    }
                }
                "checked_pow" => {
                    let r = if signed {
                        xs.checked_pow(amt).filter(|&r| fits(r, it))
                    } else {
                        xb.checked_pow(amt).filter(|&r| r <= mask).map(|r| int_from_bits(r, it))
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "strict_pow" => {
                    let r = if signed {
                        xs.checked_pow(amt).filter(|&r| fits(r, it))
                    } else {
                        xb.checked_pow(amt).filter(|&r| r <= mask).map(|r| int_from_bits(r, it))
                    };
                    match r {
                        Some(r) => int_v(r),
                        None => Err(over()),
                    }
                }
                "strict_shl" => {
                    if amt >= width {
                        Err(over())
                    } else {
                        bits_v(xb << amt)
                    }
                }
                "strict_shr" => {
                    if amt >= width {
                        Err(over())
                    } else if signed {
                        int_v(xs >> amt)
                    } else {
                        bits_v(xb >> amt)
                    }
                }
                "saturating_pow" => {
                    if signed {
                        match xs.checked_pow(amt) {
                            Some(r) if fits(r, it) => int_v(r),
                            _ => int_v(if xs < 0 && amt % 2 == 1 { lo } else { hi_s }),
                        }
                    } else {
                        match xb.checked_pow(amt) {
                            Some(r) if r <= mask => bits_v(r),
                            _ => bits_v(mask),
                        }
                    }
                }
                "wrapping_pow" => {
                    let (mut base, mut acc, mut e) = (xb, 1u128, amt);
                    while e > 0 {
                        if e & 1 == 1 {
                            acc = acc.wrapping_mul(base) & mask;
                        }
                        base = base.wrapping_mul(base) & mask;
                        e >>= 1;
                    }
                    bits_v(acc)
                }
                "checked_shl" => {
                    let r = if amt >= width { None } else { Some(int_from_bits(xb << amt, it)) };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "checked_shr" => {
                    let r = if amt >= width {
                        None
                    } else if signed {
                        Some(xs >> amt)
                    } else {
                        Some(int_from_bits(xb >> amt, it))
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "wrapping_shl" => bits_v(xb << (amt % width)),
                "wrapping_shr" => {
                    if signed {
                        int_v(xs >> (amt % width))
                    } else {
                        bits_v(xb >> (amt % width))
                    }
                }
                "unbounded_shl" => {
                    if amt >= width {
                        bits_v(0)
                    } else {
                        bits_v(xb << amt)
                    }
                }
                "unbounded_shr" => {
                    if signed {
                        int_v(if amt >= width { if xs < 0 { -1 } else { 0 } } else { xs >> amt })
                    } else if amt >= width {
                        bits_v(0)
                    } else {
                        bits_v(xb >> amt)
                    }
                }
                "rotate_left" | "rotate_right" => {
                    let r = amt % width;
                    if r == 0 {
                        bits_v(xb)
                    } else if name == "rotate_left" {
                        bits_v((xb << r) | (xb >> (width - r)))
                    } else {
                        bits_v((xb >> r) | (xb << (width - r)))
                    }
                }
                "ilog" | "checked_ilog" => {
                    let ok = amt >= 2 && xb != 0 && (!signed || xs > 0);
                    if name == "ilog" {
                        if ok {
                            Ok((ConstValue::Int(xb.ilog(amt as u128) as i128), super::int(IntTy::U32)))
                        } else {
                            Err(outside(span, "this method call (logarithm of a non-positive value)"))
                        }
                    } else {
                        let r = if ok { Some(xb.ilog(amt as u128)) } else { None };
                        Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                    }
                }
                _ => Err(outside_err()),
            };
        }
        let y = self.int_arg(cx, env, arg, rt, span)?;
        let yb = int_bits(y, it);
        let ys = truncate_to_int(y, it);
        // One checked operation per family letter: `a`dd, `s`ub,
        // `m`ul, `d`iv, `r`em, each at the receiver width.
        let checked = |op: u8| -> Option<i128> {
            if signed {
                let r = match op {
                    b'a' => xs.checked_add(ys),
                    b's' => xs.checked_sub(ys),
                    b'm' => xs.checked_mul(ys),
                    b'd' => {
                        if ys == 0 || (xs == lo && ys == -1) {
                            None
                        } else {
                            Some(xs / ys)
                        }
                    }
                    b'r' => {
                        if ys == 0 || (xs == lo && ys == -1) {
                            None
                        } else {
                            Some(xs % ys)
                        }
                    }
                    _ => None,
                };
                r.filter(|&r| fits(r, it))
            } else {
                let r = match op {
                    b'a' => xb.checked_add(yb),
                    b's' => xb.checked_sub(yb),
                    b'm' => xb.checked_mul(yb),
                    b'd' => xb.checked_div(yb),
                    b'r' => xb.checked_rem(yb),
                    _ => None,
                };
                r.filter(|&r| r <= mask).map(|r| int_from_bits(r, it))
            }
        };
        let fam = |name: &str| -> Option<(u8, u8)> {
            let (kind, op) = name.split_once('_')?;
            let k = match kind {
                "checked" => b'c',
                "saturating" => b't',
                "wrapping" => b'w',
                "strict" => b's',
                _ => return None,
            };
            let o = match op {
                "add" => b'a',
                "sub" => b's',
                "mul" => b'm',
                "div" => b'd',
                "rem" => b'r',
                _ => return None,
            };
            Some((k, o))
        };
        if let Some((kind, op)) = fam(name) {
            return match kind {
                b's' => match checked(op) {
                    Some(r) => int_v(r),
                    None => Err(over()),
                },
                b'c' => Ok(self.opt_value(cx, rt, checked(op).map(ConstValue::Int))),
                b'w' => {
                    match op {
                        b'a' => bits_v(xb.wrapping_add(yb)),
                        b's' => bits_v(xb.wrapping_sub(yb)),
                        b'm' => bits_v(xb.wrapping_mul(yb)),
                        b'd' => {
                            if yb == 0 {
                                Err(over())
                            } else if signed {
                                int_v(if xs == lo && ys == -1 { lo } else { xs / ys })
                            } else {
                                bits_v(xb / yb)
                            }
                        }
                        _ => {
                            if yb == 0 {
                                Err(over())
                            } else if signed {
                                int_v(if xs == lo && ys == -1 { 0 } else { xs % ys })
                            } else {
                                bits_v(xb % yb)
                            }
                        }
                    }
                }
                _ => {
                    // Saturating: division by zero still panics in
                    // rustc, so it stays an error here.
                    if matches!(op, b'd' | b'r') && yb == 0 {
                        return Err(over());
                    }
                    match checked(op) {
                        Some(r) => int_v(r),
                        None => {
                            if signed {
                                // Overflow direction: a negative
                                // operand pairing saturates low.
                                let low = match op {
                                    b'a' => xs < 0,
                                    b's' => xs < 0 || ys > 0 && xs < ys,
                                    b'm' => (xs < 0) != (ys < 0),
                                    b'd' => (xs < 0) != (ys < 0),
                                    _ => false,
                                };
                                int_v(if low { lo } else { hi_s })
                            } else {
                                bits_v(if op == b's' { 0 } else { mask })
                            }
                        }
                    }
                }
            };
        }
        match name {
            "div_ceil" => {
                if signed || yb == 0 {
                    return Err(over());
                }
                int_v(int_from_bits(xb / yb + u128::from(xb % yb != 0), it))
            }
            "div_euclid" | "rem_euclid" | "checked_div_euclid" | "checked_rem_euclid" | "strict_div_euclid" | "strict_rem_euclid" => {
                let r: Option<i128> = if yb == 0 || (signed && xs == lo && ys == -1) {
                    None
                } else if signed {
                    Some(if name.ends_with("div_euclid") { xs.div_euclid(ys) } else { xs.rem_euclid(ys) })
                } else {
                    Some(int_from_bits(if name.ends_with("div_euclid") { xb / yb } else { xb % yb }, it))
                };
                if name.starts_with("checked") {
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                } else {
                    match r {
                        Some(r) => int_v(r),
                        None => Err(over()),
                    }
                }
            }
            "abs_diff" => {
                let d = xb.abs_diff(yb);
                // For signed receivers the bits difference equals
                // the value difference, at the unsigned counterpart.
                let d = if signed { xs.abs_diff(ys) } else { d };
                let ut = match it {
                    IntTy::I8 => IntTy::U8,
                    IntTy::I16 => IntTy::U16,
                    IntTy::I32 => IntTy::U32,
                    IntTy::I64 => IntTy::U64,
                    IntTy::Isize => IntTy::Usize,
                    IntTy::I128 => IntTy::U128,
                    u => u,
                };
                Ok((ConstValue::Int(int_from_bits(d, ut)), super::int(ut)))
            }
            "midpoint" => {
                if signed {
                    int_v(xs.midpoint(ys))
                } else {
                    bits_v(xb.midpoint(yb))
                }
            }
            "is_multiple_of" if !signed => Ok((ConstValue::Bool(if yb == 0 { xb == 0 } else { xb % yb == 0 }), BOOL)),
            "next_multiple_of" | "checked_next_multiple_of" if !signed => {
                let r: Option<u128> = if yb == 0 {
                    None
                } else {
                    let rem = xb % yb;
                    let add = if rem == 0 { 0 } else { yb - rem };
                    if add > mask - xb { None } else { Some(xb + add) }
                };
                if name.starts_with("checked") {
                    Ok(self.opt_value(cx, rt, r.map(|u| ConstValue::Int(int_from_bits(u & mask, it)))))
                } else {
                    match r {
                        Some(u) => bits_v(u),
                        None => Err(over()),
                    }
                }
            }
            "eq_ignore_ascii_case" if it == IntTy::U8 => Ok((ConstValue::Bool((xb as u8).eq_ignore_ascii_case(&(yb as u8))), BOOL)),
            _ => Err(outside_err()),
        }
    }

    /// `char` and `u8` ASCII predicates and case maps, plus the
    /// other const `char` methods. The host `char` and `u8`
    /// implementations carry rustc's own results.
    fn char_method<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        c: char,
        name: &str,
        args: &[ExprId],
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        let bool_v = |b: bool| Ok((ConstValue::Bool(b), BOOL));
        match name {
            "is_ascii" if args.is_empty() => bool_v(c.is_ascii()),
            "is_ascii_alphabetic" if args.is_empty() => bool_v(c.is_ascii_alphabetic()),
            "is_ascii_alphanumeric" if args.is_empty() => bool_v(c.is_ascii_alphanumeric()),
            "is_ascii_digit" if args.is_empty() => bool_v(c.is_ascii_digit()),
            "is_ascii_whitespace" if args.is_empty() => bool_v(c.is_ascii_whitespace()),
            "is_ascii_uppercase" if args.is_empty() => bool_v(c.is_ascii_uppercase()),
            "is_ascii_lowercase" if args.is_empty() => bool_v(c.is_ascii_lowercase()),
            "is_ascii_hexdigit" if args.is_empty() => bool_v(c.is_ascii_hexdigit()),
            "is_ascii_punctuation" if args.is_empty() => bool_v(c.is_ascii_punctuation()),
            "is_ascii_graphic" if args.is_empty() => bool_v(c.is_ascii_graphic()),
            "is_ascii_control" if args.is_empty() => bool_v(c.is_ascii_control()),
            // The const Unicode predicates. is_alphabetic, is_numeric, and
            // is_alphanumeric are not const fns in rustc 1.99, so they stay
            // outside the evaluator and reject, as rustc does.
            "is_lowercase" if args.is_empty() => bool_v(c.is_lowercase()),
            "is_uppercase" if args.is_empty() => bool_v(c.is_uppercase()),
            "is_whitespace" if args.is_empty() => bool_v(c.is_whitespace()),
            "is_control" if args.is_empty() => bool_v(c.is_control()),
            "to_ascii_lowercase" if args.is_empty() => Ok((ConstValue::Char(c.to_ascii_lowercase()), CHAR)),
            "to_ascii_uppercase" if args.is_empty() => Ok((ConstValue::Char(c.to_ascii_uppercase()), CHAR)),
            "len_utf8" if args.is_empty() => Ok((ConstValue::Int(c.len_utf8() as i128), USIZE)),
            "len_utf16" if args.is_empty() => Ok((ConstValue::Int(c.len_utf16() as i128), USIZE)),
            "to_digit" if args.len() == 1 => {
                let (av, _) = self.value(cx, env, args[0], Some(super::int(IntTy::U32)))?;
                let ConstValue::Int(r) = av else { return Err(outside_err()) };
                // `to_digit` panics outside radix 2..=36; a const panic is
                // a reject here (and the host call must not run).
                let radix = u32::try_from(r).map_err(|_| outside_err())?;
                if !(2..=36).contains(&radix) {
                    return Err(outside(span, "this `to_digit` radix (outside 2 to 36)"));
                }
                let v = c.to_digit(radix).map(|d| ConstValue::Int(d as i128));
                Ok(self.opt_value(cx, super::int(IntTy::U32), v))
            }
            "is_digit" if args.len() == 1 => {
                let (av, _) = self.value(cx, env, args[0], Some(super::int(IntTy::U32)))?;
                let ConstValue::Int(r) = av else { return Err(outside_err()) };
                let radix = u32::try_from(r).map_err(|_| outside_err())?;
                if !(2..=36).contains(&radix) {
                    return Err(outside(span, "this `is_digit` radix (outside 2 to 36)"));
                }
                bool_v(c.is_digit(radix))
            }
            _ => Err(outside_err()),
        }
    }

    fn macro_<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[ast::FmtPiece],
        span: Span,
    ) -> Result<TypedValue, Diag> {
        match kind {
            MacroKind::Assert => {
                // A formatting message is a non-const call even when
                // the assertion passes (rustc E0015); the one-`{}`
                // form needs a `&str` argument.
                let msg_arg = match const_macro_form(kind, fmt) {
                    ConstMacroForm::Bad => return Err(nonconst_fmt_macro(span)),
                    ConstMacroForm::OneStrArg(index) => Some(index),
                    ConstMacroForm::Plain => None,
                };
                if let Some(index) = msg_arg {
                    if is_fmt_capture(cx.ast(), args[index], |s| cx.sym_text(s).len()) {
                        return Err(nonconst_fmt_macro(span));
                    }
                    let (av, _) = self.value(cx, env, args[index], Some(REF_STR))?;
                    if !matches!(av, ConstValue::Str(_)) {
                        return Err(Diag::new(
                            C_NONCONST,
                            span,
                            "argument to `panic!()` in a const context must have type `&str`",
                            "Use a `&str` message, or move the macro out of the const context.",
                        ));
                    }
                }
                let (v, _) = self.value(cx, env, args[0], Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this assert")) };
                if b {
                    Ok((ConstValue::Unit, UNIT))
                } else {
                    // The parser gives a message-less assert rustc's
                    // "assertion failed: <cond>" text as its format string.
                    let msg = fmt_text(fmt).unwrap_or_else(|| "assertion failed".into());
                    let msg = msg.strip_prefix("assertion failed: ").unwrap_or(&msg);
                    let msg = if msg == crate::expand::builtin::ASSERT_TEXT_UNKNOWN { "the condition is false" } else { msg };
                    Err(Diag::new(C_OUTSIDE, span, format!("const assertion failed: {msg}"), "Fix the asserted condition."))
                }
            }
            // `assert_eq!` and `assert_ne!` call the non-const
            // `assert_failed` in every form (rustc E0015).
            MacroKind::AssertEq | MacroKind::AssertNe => Err(nonconst_fmt_macro(span)),
            MacroKind::Panic => {
                match const_macro_form(kind, fmt) {
                    ConstMacroForm::Bad => return Err(nonconst_fmt_macro(span)),
                    ConstMacroForm::OneStrArg(index) => {
                        if is_fmt_capture(cx.ast(), args[index], |s| cx.sym_text(s).len()) {
                            return Err(nonconst_fmt_macro(span));
                        }
                        let (av, _) = self.value(cx, env, args[index], Some(REF_STR))?;
                        let ConstValue::Str(i) = av else {
                            return Err(Diag::new(
                                C_NONCONST,
                                span,
                                "argument to `panic!()` in a const context must have type `&str`",
                                "Use a `&str` message, or move the macro out of the const context.",
                            ));
                        };
                        let msg = cx.ast().strings[i as usize].clone();
                        return Err(Diag::new(C_OUTSIDE, span, format!("const panic: {msg}"), "Remove the panic from the const item."));
                    }
                    ConstMacroForm::Plain => {}
                }
                let msg = fmt_text(fmt).unwrap_or_else(|| "explicit panic".into());
                Err(Diag::new(C_OUTSIDE, span, format!("const panic: {msg}"), "Remove the panic from the const item."))
            }
            MacroKind::Vec => Err(outside(span, "`vec!`")),
            _ => Err(outside(span, "this macro")),
        }
    }

    fn match_expr<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        scrut: ExprId,
        arms: &[ast::Arm],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<Flow, Diag> {
        let (sv, st) = self.value_moved(cx, env, scrut, None)?;
        // Destructuring a drop scrutinee destroys what the pattern
        // does not move out (E0493), even out of a place.
        if cx.needs_drop(st) && arms.iter().any(|arm| pat_destructures(cx.ast(), arm.pat)) {
            return Err(drop_diag(cx, st, span));
        }
        for arm in arms {
            let mut binds = Vec::new();
            if self.match_pat(cx, env, arm.pat, &sv, st, true, &mut binds)? {
                let saved = env.len();
                env.extend(binds);
                let guard_ok = match arm.guard {
                    None => true,
                    Some(g) => {
                        let (gv, _) = self.value(cx, env, g, Some(BOOL))?;
                        matches!(gv, ConstValue::Bool(true))
                    }
                };
                if guard_ok {
                    let prev = self.move_read;
                    self.move_read = true;
                    let r = self.expr(cx, env, arm.body, expected);
                    self.move_read = prev;
                    if r.is_ok() {
                        self.check_scope_drops(cx, env, saved, span)?;
                    }
                    env.truncate(saved);
                    if r.is_ok() {
                        // The other arms are dead here, but rustc's
                        // drop check is static: scan them too.
                        for other in arms {
                            if !std::ptr::eq(other, arm) {
                                let denv = self.dead_env(cx, env, other.pat, st);
                                if let Some(g) = other.guard {
                                    self.scan_dead_expr(cx, &denv, g)?;
                                }
                                self.scan_dead_expr(cx, &denv, other.body)?;
                            }
                        }
                    }
                    return r;
                }
                env.truncate(saved);
            }
        }
        Err(outside(span, "this match (no arm matched)"))
    }

    /// Matches a pattern against a value. On a match, appends the bindings
    /// (name, value, mutable) to `binds`. `in_match` is kept for parity with
    /// the checker's signature; refutable patterns simply do not match here.
    /// The value a binding of `v` (type `t`) takes: `v` itself, or a
    /// shared reference to it under a by-reference default binding
    /// mode, where edition 2024 forbids a `mut` binding.
    fn bind_value<'a, C: ConstCx<'a>>(&self, cx: &mut C, v: &ConstValue, t: Ty, mutable: bool, span: Span) -> Result<TypedValue, Diag> {
        if !self.ref_bind {
            return Ok((v.clone(), t));
        }
        if mutable {
            return Err(outside(span, "a `mut` binding below a matched reference"));
        }
        Ok((ConstValue::Ref(Box::new(v.clone())), cx.tys().mk_ref(false, t)))
    }

    /// Matches `v` (of type `t`) against `pat`, pushing its bindings.
    /// A struct, variant, or tuple pattern against a reference value
    /// matches through it and binds by reference below it (rustc's
    /// default binding mode, `ref_bind`).
    #[allow(clippy::too_many_arguments)]
    fn match_pat<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        pat: PatId,
        v: &ConstValue,
        t: Ty,
        in_match: bool,
        binds: &mut Vec<(Sym, TypedValue, bool, bool)>,
    ) -> Result<bool, Diag> {
        let prev = self.ref_bind;
        let r = self.match_pat_at(cx, env, pat, v, t, in_match, binds);
        self.ref_bind = prev;
        r
    }

    #[allow(clippy::too_many_arguments)]
    fn match_pat_at<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        pat: PatId,
        v: &ConstValue,
        t: Ty,
        _in_match: bool,
        binds: &mut Vec<(Sym, TypedValue, bool, bool)>,
    ) -> Result<bool, Diag> {
        let span = cx.ast().pat_span(pat);
        match cx.ast().pat(pat) {
            Pat::Wild | Pat::Rest => Ok(true),
            Pat::Binding { name, mutable, by_ref } => {
                if *by_ref {
                    return Err(outside(span, "`ref` bindings in const"));
                }
                // A plain name that resolves to a const item compares
                // against it, as the checker resolves it; a unit
                // struct name matches its only value. After name
                // resolution only a block const or the prelude's `None`
                // can be such a name: a module item in scope is a path
                // pattern by then, and one out of scope (the root's `N`
                // in module `m`) leaves a fresh binding, as in rustc.
                if !mutable && !env.iter().any(|(n, _, _, _)| n == name) {
                    let resolved = cx.patterns_resolved();
                    let item = if resolved { cx.block_const_item(*name, span) } else { cx.const_item(*name, span) };
                    if let Some((cv, _)) = item {
                        return Ok(values_eq(v, &cv));
                    }
                    let segs = [ast::PathSeg::plain(*name)];
                    if (!resolved || cx.sym_text(*name) == "None")
                        && let Some((_, variant, _)) = cx.unit_variant(&segs, Some(t))
                    {
                        return Ok(matches!(v, ConstValue::Variant(got, _) if *got == variant)
                            || matches!(v, ConstValue::Aggregate(_)));
                    }
                }
                if holds_mut_ref(cx, t, &mut Vec::new()) {
                    return Err(mut_ref_outside(span, "a binding that holds a `&mut` reference"));
                }
                binds.push((*name, self.bind_value(cx, v, t, *mutable, span)?, *mutable, false));
                Ok(true)
            }
            Pat::At { name, mutable, by_ref, inner } => {
                if *by_ref {
                    return Err(outside(span, "`ref` bindings in const"));
                }
                if holds_mut_ref(cx, t, &mut Vec::new()) {
                    return Err(mut_ref_outside(span, "a binding that holds a `&mut` reference"));
                }
                let bv = self.bind_value(cx, v, t, *mutable, span)?;
                if self.match_pat(cx, env, *inner, v, t, _in_match, binds)? {
                    binds.push((*name, bv, *mutable, false));
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            Pat::Paren(inner) => self.match_pat(cx, env, *inner, v, t, _in_match, binds),
            // Edition 2024: no `&` pattern under a by-reference
            // default binding mode.
            Pat::Ref { .. } if self.ref_bind => Err(outside(span, "a `&` pattern below a matched reference")),
            Pat::Ref { inner, .. } => match v {
                ConstValue::Ref(inner_v) => {
                    let it = match cx.tys_ref().kind(t) {
                        TyKind::Ref(_, _, it) => it,
                        _ => ERROR,
                    };
                    let inner_v = (**inner_v).clone();
                    self.match_pat(cx, env, *inner, &inner_v, it, _in_match, binds)
                }
                ConstValue::Str(_) | ConstValue::StrBytes(_) => {
                    let s = v.clone();
                    self.match_pat(cx, env, *inner, &s, t, _in_match, binds)
                }
                _ => Ok(false),
            },
            Pat::Lit(l) => {
                let (lv, _) = self.value(cx, env, *l, Some(t))?;
                // Strings compare by text: a literal and an evaluated
                // string (`StrBytes`) live in different tables.
                if let (Some(a), Some(b)) = (str_bytes(cx, v), str_bytes(cx, &lv)) {
                    return Ok(a == b);
                }
                Ok(values_eq(v, &lv))
            }
            Pat::Range { lo, hi, inclusive } => {
                // A float range compares with `partial_cmp`: a NaN
                // scrutinee matches no range, as in rustc.
                if let ConstValue::Float(bits, ft) = v {
                    let n = match ft {
                        FloatTy::F32 => f32::from_bits(*bits as u32) as f64,
                        FloatTy::F64 => f64::from_bits(*bits),
                    };
                    let fbound = |hv: &ConstValue| match hv {
                        ConstValue::Float(b, FloatTy::F32) => Some(f32::from_bits(*b as u32) as f64),
                        ConstValue::Float(b, FloatTy::F64) => Some(f64::from_bits(*b)),
                        _ => None,
                    };
                    if let Some(lo) = lo {
                        let (lv, _) = self.value(cx, env, *lo, Some(t))?;
                        let Some(l) = fbound(&lv) else { return Ok(false) };
                        if !(n >= l) {
                            return Ok(false);
                        }
                    }
                    if let Some(hi) = hi {
                        let (hv, _) = self.value(cx, env, *hi, Some(t))?;
                        let Some(h) = fbound(&hv) else { return Ok(false) };
                        if *inclusive {
                            if !(n <= h) {
                                return Ok(false);
                            }
                        } else if !(n < h) {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                let num = match v {
                    ConstValue::Int(i) => Some(*i),
                    ConstValue::Char(c) => Some(*c as i128),
                    _ => None,
                };
                let Some(n) = num else { return Ok(false) };
                let it = self.int_ty_of(cx, t);
                let bound = |hv: ConstValue| match hv {
                    ConstValue::Int(h) => Some(h),
                    ConstValue::Char(c) => Some(c as i128),
                    _ => None,
                };
                if let Some(lo) = lo {
                    let (lv, _) = self.value(cx, env, *lo, Some(t))?;
                    let Some(l) = bound(lv) else { return Ok(false) };
                    if cmp_int(n, l, it) == std::cmp::Ordering::Less {
                        return Ok(false);
                    }
                }
                if let Some(hi) = hi {
                    let (hv, _) = self.value(cx, env, *hi, Some(t))?;
                    let Some(h) = bound(hv) else { return Ok(false) };
                    let c = cmp_int(n, h, it);
                    if *inclusive {
                        if c == std::cmp::Ordering::Greater {
                            return Ok(false);
                        }
                    } else if c != std::cmp::Ordering::Less {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Or(alts) => {
                for &alt in alts {
                    let before = binds.len();
                    if self.match_pat(cx, env, alt, v, t, _in_match, binds)? {
                        return Ok(true);
                    }
                    binds.truncate(before);
                }
                Ok(false)
            }
            Pat::Tuple(elems) => {
                let (v, t) = match v {
                    ConstValue::Ref(inner) if matches!(cx.tys_ref().kind(t), TyKind::Ref(..)) => {
                        let it = match cx.tys_ref().kind(t) {
                            TyKind::Ref(_, m, _) if m.is_mut() => return Err(mut_ref_outside(span, "a pattern matched through a `&mut` reference")),
                            TyKind::Ref(_, _, it) => it,
                            _ => ERROR,
                        };
                        self.ref_bind = true;
                        (&**inner, it)
                    }
                    other => (other, t),
                };
                let vals = match v {
                    ConstValue::Aggregate(vals) => vals,
                    ConstValue::Unit if elems.is_empty() => return Ok(true),
                    _ => return Ok(false),
                };
                let tys: Vec<Ty> = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).to_vec(),
                    _ => vec![ERROR; vals.len()],
                };
                let mapped = map_rest(elems, vals.len(), cx.ast());
                let Some(mapped) = mapped else { return Ok(false) };
                for (i, sub) in mapped {
                    if !self.match_pat(cx, env, sub, &vals[i].clone(), tys.get(i).copied().unwrap_or(ERROR), _in_match, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Slice { prefix, middle, suffix } => {
                // A blob matches in place: fixed elements read single
                // bytes and the middle is an O(1) sub-window, so the
                // `[b0, .., tail @ ..]` loop shape stays linear.
                let blob_of = match v {
                    ConstValue::Bytes(b) => Some(b.clone()),
                    ConstValue::Ref(inner) => match &**inner {
                        ConstValue::Bytes(b) => Some(b.clone()),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(b) = &blob_of {
                    let len = b.len() as u64;
                    let fixed = (prefix.len() + suffix.len()) as u64;
                    if if middle.is_some() { len < fixed } else { len != fixed } {
                        return Ok(false);
                    }
                    // Matching a reference scrutinee (`&[u8]`) binds
                    // elements by reference and the middle as a
                    // slice reference, as match ergonomics does; an
                    // owned array binds by value.
                    let (elem_ty, by_ref) = match cx.tys_ref().kind(t) {
                        TyKind::Array(e, _) | TyKind::Slice(e) => (e, false),
                        TyKind::Ref(_, _, inner) => match cx.tys_ref().kind(inner) {
                            TyKind::Array(e, _) | TyKind::Slice(e) => (e, true),
                            _ => (ERROR, false),
                        },
                        _ => (ERROR, false),
                    };
                    let elem = |cx: &mut C, byte: u8| -> TypedValue {
                        let v = ConstValue::Int(byte as i128);
                        if by_ref {
                            let rt = cx.tys().mk_ref(false, elem_ty);
                            (ConstValue::Ref(Box::new(v)), rt)
                        } else {
                            (v, elem_ty)
                        }
                    };
                    for (i, &sub) in prefix.iter().enumerate() {
                        let (ev, et) = elem(cx, b.as_slice()[i]);
                        if !self.match_pat(cx, env, sub, &ev, et, _in_match, binds)? {
                            return Ok(false);
                        }
                    }
                    for (j, &sub) in suffix.iter().enumerate() {
                        let (ev, et) = elem(cx, b.as_slice()[b.len() - suffix.len() + j]);
                        if !self.match_pat(cx, env, sub, &ev, et, _in_match, binds)? {
                            return Ok(false);
                        }
                    }
                    if let Some(mid) = middle {
                        let mid_blob = b.sub(prefix.len(), b.len() - suffix.len());
                        let Some(mid_blob) = mid_blob else { return Ok(false) };
                        let mid_ty = if by_ref {
                            let s = cx.tys().intern(TyKind::Slice(elem_ty));
                            cx.tys().mk_ref(false, s)
                        } else {
                            let c = cx.tys().intern_const(super::ConstKind::Int(mid_blob.len() as u128));
                            cx.tys().intern(TyKind::Array(elem_ty, c))
                        };
                        if !self.match_pat(cx, env, *mid, &ConstValue::Bytes(mid_blob), mid_ty, _in_match, binds)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                let (vals, repeat): (Vec<ConstValue>, Option<(ConstValue, u64)>) = match v {
                    ConstValue::Aggregate(vals) => (vals.clone(), None),
                    ConstValue::Repeat(x, n) => (Vec::new(), Some(((**x).clone(), *n))),
                    _ => return Ok(false),
                };
                let len = repeat.as_ref().map_or(vals.len() as u64, |(_, n)| *n);
                let fixed = (prefix.len() + suffix.len()) as u64;
                if if middle.is_some() { len < fixed } else { len != fixed } {
                    return Ok(false);
                }
                let elem_ty = match cx.tys_ref().kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => ERROR,
                };
                let at = |i: u64| -> ConstValue {
                    match &repeat {
                        Some((x, _)) => x.clone(),
                        None => vals[i as usize].clone(),
                    }
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    if !self.match_pat(cx, env, sub, &at(i as u64), elem_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    if !self.match_pat(cx, env, sub, &at(len - suffix.len() as u64 + j as u64), elem_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                if let Some(mid) = middle
                    && matches!(cx.ast().pat(*mid), Pat::Binding { .. })
                {
                    // Owned array middle, built element by element.
                    let mid_vals: Vec<ConstValue> = (prefix.len() as u64..len - suffix.len() as u64).map(at).collect();
                    let n = mid_vals.len() as u128;
                    let mid_ty = {
                        let c = cx.tys().intern_const(super::ConstKind::Int(n));
                        cx.tys().intern(TyKind::Array(elem_ty, c))
                    };
                    if !self.match_pat(cx, env, *mid, &ConstValue::Aggregate(mid_vals), mid_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Path(segs) | Pat::TupleStruct { path: segs, .. } | Pat::Struct { path: segs, .. } => {
                let (v, t) = match v {
                    ConstValue::Ref(inner) => {
                        let it = match cx.tys_ref().kind(t) {
                            TyKind::Ref(_, m, _) if m.is_mut() => return Err(mut_ref_outside(span, "a pattern matched through a `&mut` reference")),
                            TyKind::Ref(_, _, it) => it,
                            _ => ERROR,
                        };
                        self.ref_bind = true;
                        ((**inner).clone(), it)
                    }
                    other => (other.clone(), t),
                };
                // Option patterns by name, as the checker resolves them.
                // `Some(..)` against `None` (and `None` against `Some`)
                // does not match.
                if let ConstValue::Variant(variant, fields) = &v
                    && cx.tys_ref().option_elem(t).is_some()
                    && matches!(cx.sym_text(segs[segs.len() - 1].name), "Some" | "None")
                {
                    let want_some = matches!(cx.ast().pat(pat), Pat::TupleStruct { .. });
                    if (want_some && *variant == 0) || (!want_some && *variant == 1) {
                        return Ok(false);
                    }
                    if (want_some && *variant == 1) || (!want_some && *variant == 0) {
                        if let Pat::TupleStruct { elems, .. } = cx.ast().pat(pat)
                            && elems.len() == 1
                        {
                            let elem_ty = cx.tys_ref().option_elem(t).unwrap_or(ERROR);
                            return self.match_pat(cx, env, elems[0], &fields[0].clone(), elem_ty, _in_match, binds);
                        }
                        if !want_some {
                            return Ok(true);
                        }
                    }
                }
                // Result patterns by name: Ok is variant 0, Err is 1.
                if let ConstValue::Variant(variant, fields) = &v
                    && let Some((ok_ty, err_ty)) = cx.tys_ref().result_args(t)
                {
                    let want_ok = cx.sym_text(segs[segs.len() - 1].name) == "Ok";
                    let want_err = cx.sym_text(segs[segs.len() - 1].name) == "Err";
                    if (want_ok && *variant == 0) || (want_err && *variant == 1) {
                        if let Pat::TupleStruct { elems, .. } = cx.ast().pat(pat)
                            && elems.len() == 1
                        {
                            let elem_ty = if want_ok { ok_ty } else { err_ty };
                            return self.match_pat(cx, env, elems[0], &fields[0].clone(), elem_ty, _in_match, binds);
                        }
                        return Ok(true);
                    }
                    if want_ok || want_err {
                        return Ok(false);
                    }
                }
                let Some((adt, variant)) = cx.pattern_variant(segs) else {
                    // A single name that resolves to a const item compares equal.
                    if segs.len() == 1
                        && let Some((cv, _)) = cx.const_item(segs[0].name, span)
                    {
                        return Ok(values_eq(&v, &cv));
                    }
                    return Err(outside(span, "this pattern"));
                };
                let field_defs = cx.variant_fields(adt, variant);
                // Privacy of the fields this pattern names. A tuple
                // struct pattern names its constructor, so any
                // private field rejects, rest or not; a struct
                // pattern names only its written fields.
                match cx.ast().pat(pat) {
                    Pat::TupleStruct { .. } if !cx.is_enum(adt) => {
                        self.check_tuple_ctor(cx, adt, field_defs.len(), span)?;
                        let what = cx.ne_ctor_what(adt, variant);
                        self.check_ne(what, NeKind::Ctor, span)?;
                    }
                    Pat::TupleStruct { .. } => {
                        let what = cx.ne_ctor_what(adt, variant);
                        self.check_ne(what, NeKind::Ctor, span)?;
                    }
                    Pat::Struct { fields, rest, .. } => {
                        for &(fname, _) in fields {
                            self.check_named_field(cx, adt, fname, span)?;
                        }
                        let what = cx.ne_pat_what(adt, variant, *rest);
                        self.check_ne(what, NeKind::Pat, span)?;
                    }
                    Pat::Path(_) => {
                        let what = cx.ne_ctor_what(adt, variant);
                        self.check_ne(what, NeKind::Ctor, span)?;
                    }
                    _ => {}
                }
                let vals: &Vec<ConstValue> = match &v {
                    ConstValue::Variant(got, vals) => {
                        if *got != variant {
                            return Ok(false);
                        }
                        vals
                    }
                    ConstValue::Aggregate(vals) => vals,
                    _ => return Ok(false),
                };
                match cx.ast().pat(pat) {
                    Pat::Path(_) => Ok(true),
                    Pat::TupleStruct { elems, .. } => {
                        let Some(mapped) = map_rest(elems, vals.len(), cx.ast()) else { return Ok(false) };
                        for (i, sub) in mapped {
                            let ft = field_defs.get(i).map_or(ERROR, |f| f.1);
                            if !self.match_pat(cx, env, sub, &vals[i].clone(), ft, _in_match, binds)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    Pat::Struct { fields, .. } => {
                        for &(fname, sub) in fields {
                            let Some(i) = field_defs.iter().position(|(n, _)| *n == fname) else { return Ok(false) };
                            if !self.match_pat(cx, env, sub, &vals[i].clone(), field_defs[i].1, _in_match, binds)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(false),
                }
            }
            _ => Err(outside(span, "this pattern")),
        }
    }

    /// The type of a place expression, for field assignment.
    fn place_ty<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, e: ExprId) -> Option<Ty> {
        match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => env.iter().rev().find(|(n, _, _, _)| *n == segs[0].name).map(|(_, v, _, _)| v.1),
            Expr::SelfValue => {
                let s = self.self_sym?;
                env.iter().rev().find(|(n, _, _, _)| *n == s).map(|(_, v, _, _)| v.1)
            }
            Expr::Field { base, name } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                let adt = cx.tys_ref().local_adt(bt)?;
                cx.variant_fields(adt, 0).iter().find(|(n, _)| n == name).map(|f| f.1)
            }
            Expr::TupleField { base, index } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                match cx.tys_ref().kind(bt) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).get(*index as usize).copied(),
                    _ => cx.tys_ref().local_adt(bt).and_then(|a| cx.variant_fields(a, 0).get(*index as usize).map(|f| f.1)),
                }
            }
            Expr::Deref(inner) => match cx.tys_ref().kind(self.place_ty(cx, env, *inner)?) {
                TyKind::Ref(_, _, it) => Some(it),
                _ => None,
            },
            Expr::Index { base, .. } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                match cx.tys_ref().kind(bt) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Checks every field step of an assignment place for privacy,
    /// innermost first (a read of each step is what the write does).
    fn check_place_fields<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &Env, e: ExprId, span: Span) -> Result<(), Diag> {
        match cx.ast().expr(e) {
            Expr::Field { base, name } => {
                self.check_place_fields(cx, env, *base, span)?;
                let Some(bt) = self.place_ty(cx, env, *base) else { return Ok(()) };
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                if let Some(adt) = cx.tys_ref().local_adt(bt) {
                    self.check_named_field(cx, adt, *name, span)?;
                }
                Ok(())
            }
            Expr::TupleField { base, index } => {
                self.check_place_fields(cx, env, *base, span)?;
                let Some(bt) = self.place_ty(cx, env, *base) else { return Ok(()) };
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                if !matches!(cx.tys_ref().kind(bt), TyKind::Tuple(_))
                    && let Some(adt) = cx.tys_ref().local_adt(bt)
                {
                    self.check_tuple_field(cx, adt, *index, span)?;
                }
                Ok(())
            }
            Expr::Deref(inner) => self.check_place_fields(cx, env, *inner, span),
            Expr::Index { base, .. } => self.check_place_fields(cx, env, *base, span),
            _ => Ok(()),
        }
    }

    /// Assigns `v` into the place `e` denotes in the environment.
    fn assign_place<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, v: ConstValue, span: Span) -> Result<(), Diag> {
        self.check_place_fields(cx, env, e, span)?;
        // Assigning over a live drop value destroys the old one
        // (E0493). A whole local that was moved out holds nothing,
        // so it alone may be assigned over.
        if !matches!(cx.ast().expr(e), Expr::Path(segs) if segs.len() == 1)
            && !matches!(cx.ast().expr(e), Expr::SelfValue)
            && let Some(pt) = self.place_ty(cx, env, e)
            && cx.needs_drop(pt)
        {
            return Err(drop_diag(cx, pt, span));
        }
        let whole = match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => Some(segs[0].name),
            // A `mut self` receiver, bound as a local named `self`.
            Expr::SelfValue => Some(self.self_sym.ok_or_else(|| outside(span, "`self` here"))?),
            _ => None,
        };
        match cx.ast().expr(e) {
            _ if let Some(name) = whole => {
                match env.iter_mut().rev().find(|(n, _, _, _)| *n == name) {
                    Some(slot) => {
                        if !slot.2 {
                            return Err(outside(span, "assignment to an immutable binding"));
                        }
                        if !slot.3 && cx.needs_drop(slot.1.1) {
                            return Err(drop_diag(cx, slot.1.1, span));
                        }
                        slot.1.0 = v;
                        slot.3 = false;
                        Ok(())
                    }
                    None => Err(outside(span, "this assignment")),
                }
            }
            Expr::Field { base, name } => {
                let bt = self.place_ty(cx, env, *base).ok_or_else(|| outside(span, "this assignment"))?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                let Some(adt) = cx.tys_ref().local_adt(bt) else { return Err(outside(span, "this assignment")) };
                let fields = cx.variant_fields(adt, 0);
                let Some(i) = fields.iter().position(|(n, _)| n == name) else {
                    return Err(outside(span, "this assignment"));
                };
                let slot = self.place_slot(cx, env, *base, span)?;
                let vals = match slot {
                    ConstValue::Aggregate(vals) => vals,
                    ConstValue::Ref(cell) => match &mut **cell {
                        ConstValue::Aggregate(vals) => vals,
                        _ => return Err(outside(span, "this assignment")),
                    },
                    _ => return Err(outside(span, "this assignment")),
                };
                match vals.get_mut(i) {
                    Some(cell) => {
                        *cell = v;
                        Ok(())
                    }
                    None => Err(outside(span, "this assignment")),
                }
            }
            Expr::TupleField { base, index } => {
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => {
                        let Some(cell) = vals.get_mut(*index as usize) else {
                            return Err(outside(span, "this assignment"));
                        };
                        *cell = v;
                        Ok(())
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Index { base, index } => {
                let (iv, _) = self.value(cx, env, *index, Some(USIZE))?;
                let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
                let slot = self.place_slot(cx, env, *base, span)?;
                // A `[x; n]` local starts as a repeat value; writing
                // one element first spreads it into an aggregate.
                if let ConstValue::Repeat(x, n) = &*slot {
                    let agg = ConstValue::Aggregate(vec![(**x).clone(); *n as usize]);
                    *slot = agg;
                }
                match slot {
                    ConstValue::Aggregate(vals) => {
                        let Some(cell) = usize::try_from(i).ok().and_then(|i| vals.get_mut(i)) else {
                            return Err(outside(span, "this assignment (index out of bounds)"));
                        };
                        *cell = v;
                        Ok(())
                    }
                    ConstValue::Bytes(b) => {
                        // Copy on write in the blob keeps other
                        // holders of the same array value unchanged.
                        let ConstValue::Int(x) = v else { return Err(outside(span, "this assignment")) };
                        let byte = u8::try_from(x).map_err(|_| outside(span, "this assignment"))?;
                        let i = usize::try_from(i).map_err(|_| outside(span, "this assignment (index out of bounds)"))?;
                        if b.set(i, byte) { Ok(()) } else { Err(outside(span, "this assignment (index out of bounds)")) }
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Deref(inner) => {
                let slot = self.place_slot(cx, env, *inner, span)?;
                match slot {
                    ConstValue::Ref(cell) => {
                        **cell = v;
                        Ok(())
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            _ => Err(outside(span, "this assignment")),
        }
    }

    /// The mutable slot an assignment place base denotes.
    fn place_slot<'a, 'e, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &'e mut Env,
        e: ExprId,
        span: Span,
    ) -> Result<&'e mut ConstValue, Diag> {
        match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                env.iter_mut().rev().find(|(n, _, _, _)| *n == name).map(|slot| &mut slot.1.0).ok_or_else(|| outside(span, "this assignment"))
            }
            Expr::SelfValue => {
                let name = self.self_sym.ok_or_else(|| outside(span, "`self` here"))?;
                env.iter_mut().rev().find(|(n, _, _, _)| *n == name).map(|slot| &mut slot.1.0).ok_or_else(|| outside(span, "this assignment"))
            }
            // A named field of a struct place (`k.a[i] = v`).
            Expr::Field { base, name } => {
                let bt = self.place_ty(cx, env, *base).ok_or_else(|| outside(span, "this assignment"))?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                let adt = cx.tys_ref().local_adt(bt).ok_or_else(|| outside(span, "this assignment"))?;
                let i = cx.variant_fields(adt, 0).iter().position(|(n, _)| n == name).ok_or_else(|| outside(span, "this assignment"))?;
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => vals.get_mut(i).ok_or_else(|| outside(span, "this assignment")),
                    ConstValue::Ref(cell) => match &mut **cell {
                        ConstValue::Aggregate(vals) => vals.get_mut(i).ok_or_else(|| outside(span, "this assignment")),
                        _ => Err(outside(span, "this assignment")),
                    },
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::TupleField { base, index } => {
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => vals.get_mut(*index as usize).ok_or_else(|| outside(span, "this assignment")),
                    ConstValue::Ref(cell) => match &mut **cell {
                        ConstValue::Aggregate(vals) => vals.get_mut(*index as usize).ok_or_else(|| outside(span, "this assignment")),
                        _ => Err(outside(span, "this assignment")),
                    },
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Deref(inner) => {
                let slot = self.place_slot(cx, env, *inner, span)?;
                match slot {
                    ConstValue::Ref(cell) => Ok(&mut **cell),
                    _ => Err(outside(span, "this assignment")),
                }
            }
            _ => Err(outside(span, "this assignment")),
        }
    }
}

/// Maps pattern elements with an optional `..` to value indexes.
fn map_rest(elems: &[PatId], n: usize, ast: &Ast) -> Option<Vec<(usize, PatId)>> {
    let rest = elems.iter().position(|&s| matches!(ast.pat(s), Pat::Rest));
    match rest {
        None => {
            if elems.len() != n {
                return None;
            }
            Some(elems.iter().enumerate().map(|(i, &s)| (i, s)).collect())
        }
        Some(r) => {
            let suffix = elems.len() - r - 1;
            if r + suffix > n {
                return None;
            }
            let mut out: Vec<(usize, PatId)> = elems[..r].iter().enumerate().map(|(i, &s)| (i, s)).collect();
            for (j, &s) in elems[r + 1..].iter().enumerate() {
                out.push((n - suffix + j, s));
            }
            Some(out)
        }
    }
}

/// The UTF-8 bytes of a string value (a literal or an evaluated one).
fn str_bytes<'a, C: ConstCx<'a>>(cx: &C, v: &ConstValue) -> Option<Vec<u8>> {
    match v {
        ConstValue::Str(i) => Some(cx.ast().strings[*i as usize].as_bytes().to_vec()),
        ConstValue::StrBytes(b) => Some(b.as_slice().to_vec()),
        _ => None,
    }
}

/// Value equality for const comparisons.
fn values_eq(a: &ConstValue, b: &ConstValue) -> bool {
    match (a, b) {
        (ConstValue::Float(x, FloatTy::F64), ConstValue::Float(y, _)) => {
            return f64::from_bits(*x) == f64::from_bits(*y);
        }
        (ConstValue::Float(x, FloatTy::F32), ConstValue::Float(y, _)) => {
            return f32::from_bits(*x as u32) == f32::from_bits(*y as u32);
        }
        (ConstValue::Repeat(x, n), ConstValue::Aggregate(vals)) => vals.len() as u64 == *n && vals.iter().all(|v| values_eq(v, x)),
        (ConstValue::Aggregate(vals), ConstValue::Repeat(x, n)) => vals.len() as u64 == *n && vals.iter().all(|v| values_eq(v, x)),
        (ConstValue::Repeat(x, xn), ConstValue::Repeat(y, yn)) => xn == yn && values_eq(x, y),
        // A blob compares by its bytes against any sequence form.
        (ConstValue::Bytes(b), other) | (other, ConstValue::Bytes(b)) => match other {
            ConstValue::Bytes(o) => b == o,
            ConstValue::Aggregate(vals) => {
                vals.len() == b.len()
                    && vals.iter().zip(b.as_slice()).all(|(v, &x)| matches!(v, ConstValue::Int(i) if *i == x as i128))
            }
            ConstValue::Repeat(x, n) => {
                *n as usize == b.len() && matches!(&**x, ConstValue::Int(i) if b.as_slice().iter().all(|&y| y as i128 == *i))
            }
            ConstValue::Ref(inner) => values_eq(&ConstValue::Bytes(b.clone()), inner),
            _ => false,
        },
        _ => a == b,
    }
}

/// A float type's own associated consts (`f64::NAN`, `f32::EPSILON`,
/// `f64::MAX_EXP`). Returns the float bits, or an integer value with
/// its integer type for the count and exponent consts.
pub fn primitive_float_assoc(f: FloatTy, item: &str) -> Option<(u64, Option<IntTy>)> {
    let flt = |v: f64| match f {
        FloatTy::F64 => (v.to_bits(), None),
        FloatTy::F32 => ((v as f32).to_bits() as u64, None),
    };
    let int = |v: i64, signed: bool| (v as u64, Some(if signed { IntTy::I32 } else { IntTy::U32 }));
    // The float consts are taken from the compiler's own std, which
    // carries the same values as the Rust the checked program means.
    let out = match (f, item) {
        (_, "NAN") => flt(f64::NAN),
        (_, "INFINITY") => flt(f64::INFINITY),
        (_, "NEG_INFINITY") => flt(f64::NEG_INFINITY),
        (FloatTy::F64, "MAX") => flt(f64::MAX),
        (FloatTy::F32, "MAX") => flt(f32::MAX as f64),
        (FloatTy::F64, "MIN") => flt(f64::MIN),
        (FloatTy::F32, "MIN") => flt(f32::MIN as f64),
        (FloatTy::F64, "MIN_POSITIVE") => flt(f64::MIN_POSITIVE),
        (FloatTy::F32, "MIN_POSITIVE") => flt(f32::MIN_POSITIVE as f64),
        (FloatTy::F64, "EPSILON") => flt(f64::EPSILON),
        (FloatTy::F32, "EPSILON") => (f32::EPSILON.to_bits() as u64, None),
        (_, "RADIX") => int(2, false),
        (FloatTy::F64, "MANTISSA_DIGITS") => int(f64::MANTISSA_DIGITS as i64, false),
        (FloatTy::F32, "MANTISSA_DIGITS") => int(f32::MANTISSA_DIGITS as i64, false),
        (FloatTy::F64, "DIGITS") => int(f64::DIGITS as i64, false),
        (FloatTy::F32, "DIGITS") => int(f32::DIGITS as i64, false),
        (FloatTy::F64, "MIN_EXP") => int(f64::MIN_EXP as i64, true),
        (FloatTy::F32, "MIN_EXP") => int(f32::MIN_EXP as i64, true),
        (FloatTy::F64, "MAX_EXP") => int(f64::MAX_EXP as i64, true),
        (FloatTy::F32, "MAX_EXP") => int(f32::MAX_EXP as i64, true),
        (FloatTy::F64, "MIN_10_EXP") => int(f64::MIN_10_EXP as i64, true),
        (FloatTy::F32, "MIN_10_EXP") => int(f32::MIN_10_EXP as i64, true),
        (FloatTy::F64, "MAX_10_EXP") => int(f64::MAX_10_EXP as i64, true),
        (FloatTy::F32, "MAX_10_EXP") => int(f32::MAX_10_EXP as i64, true),
        _ => return None,
    };
    Some(out)
}

/// The `std::f32::consts` and `std::f64::consts` values, as bits.
pub fn float_consts_value(f: FloatTy, item: &str) -> Option<u64> {
    use std::f64::consts as d;
    let v = match item {
        "PI" => d::PI,
        "TAU" => d::TAU,
        "FRAC_PI_2" => d::FRAC_PI_2,
        "FRAC_PI_3" => d::FRAC_PI_3,
        "FRAC_PI_4" => d::FRAC_PI_4,
        "FRAC_PI_6" => d::FRAC_PI_6,
        "FRAC_PI_8" => d::FRAC_PI_8,
        "FRAC_1_PI" => d::FRAC_1_PI,
        "FRAC_2_PI" => d::FRAC_2_PI,
        "FRAC_2_SQRT_PI" => d::FRAC_2_SQRT_PI,
        "SQRT_2" => d::SQRT_2,
        "FRAC_1_SQRT_2" => d::FRAC_1_SQRT_2,
        "E" => d::E,
        "LOG2_E" => d::LOG2_E,
        "LOG10_E" => d::LOG10_E,
        "LN_2" => d::LN_2,
        "LN_10" => d::LN_10,
        "LOG2_10" => d::LOG2_10,
        "LOG10_2" => d::LOG10_2,
        _ => return None,
    };
    Some(match f {
        FloatTy::F64 => v.to_bits(),
        // std::f32::consts holds each value rounded to f32, which is
        // the f64 value cast to f32 (the values are not near ties).
        FloatTy::F32 => (v as f32).to_bits() as u64,
    })
}

/// How a panic-family macro form stands in a const context (rustc
/// E0015). A plain literal message is a const panic; a message that
/// is exactly one `{}` placeholder is a const panic too, but only
/// with a `&str` argument (the `index` here). Every other use of
/// format arguments, and any message at all on `todo!` or
/// `unreachable!`, calls the non-const formatting machinery. The
/// `&str` argument check needs types or values, so callers that
/// have neither (the syntactic walk below) let `OneStrArg` pass and
/// rely on the checker or the evaluator to judge the argument.
pub enum ConstMacroForm {
    /// A const panic form: no message, or a literal message.
    Plain,
    /// Exactly one `{}`: const only with a `&str` argument.
    OneStrArg(usize),
    /// A non-const formatting macro form.
    Bad,
}

/// Classifies one panic-family macro (`panic!`, `assert!`, `todo!`,
/// `unreachable!`) by its format pieces; see `ConstMacroForm`.
pub fn const_macro_form(kind: MacroKind, fmt: &[ast::FmtPiece]) -> ConstMacroForm {
    match kind {
        MacroKind::Todo | MacroKind::Unreachable => {
            // With no message these are plain literal panics; any
            // written message goes through formatting.
            if fmt.is_empty() { ConstMacroForm::Plain } else { ConstMacroForm::Bad }
        }
        MacroKind::Panic | MacroKind::Assert => {
            let mut args = fmt.iter().filter_map(|p| match p {
                ast::FmtPiece::Arg { index, debug, spec } => Some((*index, *debug, *spec)),
                ast::FmtPiece::Lit(_) => None,
            });
            match (args.next(), args.next()) {
                (None, _) => ConstMacroForm::Plain,
                (Some((index, false, spec)), None) if fmt.len() == 1 && spec == ast::FmtSpec::default() => {
                    ConstMacroForm::OneStrArg(index)
                }
                _ => ConstMacroForm::Bad,
            }
        }
        _ => ConstMacroForm::Bad,
    }
}

/// True when a format argument expression is a format-string
/// capture (`panic!("{x}")`): the parser makes it a one-segment
/// path whose span is the whole format string token, wider than
/// the name plus the two bytes a raw identifier (`r#x`) or one
/// pair of parentheses adds. A captured argument never takes the
/// one-`{}` `&str` fast path in rustc, even for a `&str` local.
pub fn is_fmt_capture(ast: &Ast, e: ExprId, name_len: impl Fn(Sym) -> usize) -> bool {
    let Expr::Path(segs) = ast.expr(e) else { return false };
    let [seg] = segs.as_slice() else { return false };
    if seg.has_args() {
        return false;
    }
    let span = ast.expr_span(e);
    (span.hi - span.lo) as usize > name_len(seg.name) + 2
}

/// The E0015 error for a non-const formatting macro form in a const
/// context (an item, not a `const fn` definition; the body checker
/// words the same error for functions).
fn nonconst_fmt_macro(span: Span) -> Diag {
    Diag::new(
        C_NONCONST,
        span,
        "cannot call non-const formatting macro in a const context",
        "Use a plain literal message, such as `panic!(\"bad\")`, or move the macro out of the const context.",
    )
}

/// Rejects the panic-family macro forms rustc rejects in a const
/// context, anywhere in the expression `e` (dead branches too:
/// E0015 and E0493-style rules are static, not per-path). Closure
/// bodies are not const contexts and stay unwalked; nested items
/// are their own items. `assert_eq!` and `assert_ne!` always call
/// the non-const `assert_failed`, so they reject here too.
fn check_macro_forms(ast: &Ast, e: ExprId) -> Result<(), Diag> {
    fn block(ast: &Ast, b: ast::BlockId) -> Result<(), Diag> {
        let blk = ast.block(b);
        for stmt in &blk.stmts {
            match stmt {
                ast::Stmt::Let { init, els, .. } => {
                    if let Some(init) = init {
                        check_macro_forms(ast, *init)?;
                    }
                    if let Some(els) = els {
                        block(ast, *els)?;
                    }
                }
                ast::Stmt::Expr { expr, .. } => check_macro_forms(ast, *expr)?,
                ast::Stmt::Item(_) | ast::Stmt::Macro { .. } => {}
            }
        }
        if let Some(tail) = blk.tail {
            check_macro_forms(ast, tail)?;
        }
        Ok(())
    }
    fn pat(ast: &Ast, p: PatId) -> Result<(), Diag> {
        match ast.pat(p) {
            Pat::Lit(e) => check_macro_forms(ast, *e),
            Pat::Range { lo, hi, .. } => {
                for e in [lo, hi].into_iter().flatten() {
                    check_macro_forms(ast, *e)?;
                }
                Ok(())
            }
            Pat::TupleStruct { elems, .. } | Pat::Or(elems) | Pat::Tuple(elems) => {
                for &s in elems {
                    pat(ast, s)?;
                }
                Ok(())
            }
            Pat::Struct { fields, .. } => {
                for &(_, s) in fields {
                    pat(ast, s)?;
                }
                Ok(())
            }
            Pat::Slice { prefix, middle, suffix } => {
                for &s in prefix.iter().chain(suffix) {
                    pat(ast, s)?;
                }
                if let Some(m) = middle {
                    pat(ast, *m)?;
                }
                Ok(())
            }
            Pat::Ref { inner, .. } | Pat::At { inner, .. } | Pat::Paren(inner) => pat(ast, *inner),
            _ => Ok(()),
        }
    }
    let span = ast.expr_span(e);
    match ast.expr(e) {
        Expr::Macro { kind, args, fmt, .. } => {
            match kind {
                MacroKind::AssertEq | MacroKind::AssertNe => return Err(nonconst_fmt_macro(span)),
                MacroKind::Panic | MacroKind::Assert | MacroKind::Todo | MacroKind::Unreachable => {
                    match const_macro_form(*kind, fmt) {
                        ConstMacroForm::Bad => return Err(nonconst_fmt_macro(span)),
                        // A literal that is plainly not a `&str`
                        // needs no type information to reject, dead
                        // branches included. Other argument shapes
                        // are judged where types or values are known.
                        ConstMacroForm::OneStrArg(index) => {
                            let plainly_not_str = match ast.expr(args[index]) {
                                Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) => true,
                                Expr::Unary { expr, .. } => matches!(ast.expr(*expr), Expr::Int(..) | Expr::Float(_)),
                                _ => false,
                            };
                            if plainly_not_str {
                                return Err(Diag::new(
                                    C_NONCONST,
                                    span,
                                    "argument to `panic!()` in a const context must have type `&str`",
                                    "Use a `&str` message, or move the macro out of the const context.",
                                ));
                            }
                        }
                        ConstMacroForm::Plain => {}
                    }
                }
                _ => {}
            }
            for &a in args {
                check_macro_forms(ast, a)?;
            }
            Ok(())
        }
        Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::ConstBlock(b) => block(ast, *b),
        Expr::LabeledBlock { body, .. } | Expr::AsyncBlock { body, .. } => block(ast, *body),
        Expr::If { cond, then, els } => {
            check_macro_forms(ast, *cond)?;
            block(ast, *then)?;
            if let Some(els) = els {
                check_macro_forms(ast, *els)?;
            }
            Ok(())
        }
        Expr::While { cond, body, .. } => {
            check_macro_forms(ast, *cond)?;
            block(ast, *body)
        }
        Expr::Loop { body, .. } => block(ast, *body),
        Expr::For { pat: p, iter, body, .. } => {
            pat(ast, *p)?;
            check_macro_forms(ast, *iter)?;
            block(ast, *body)
        }
        Expr::Match { scrut, arms } => {
            check_macro_forms(ast, *scrut)?;
            for arm in arms {
                pat(ast, arm.pat)?;
                if let Some(g) = arm.guard {
                    check_macro_forms(ast, g)?;
                }
                check_macro_forms(ast, arm.body)?;
            }
            Ok(())
        }
        Expr::Let { pat: p, scrut } => {
            pat(ast, *p)?;
            check_macro_forms(ast, *scrut)
        }
        Expr::Call { callee, args } => {
            check_macro_forms(ast, *callee)?;
            for &a in args {
                check_macro_forms(ast, a)?;
            }
            Ok(())
        }
        Expr::MethodCall { recv, args, .. } => {
            check_macro_forms(ast, *recv)?;
            for &a in args {
                check_macro_forms(ast, a)?;
            }
            Ok(())
        }
        Expr::Field { base, .. } | Expr::TupleField { base, .. } => check_macro_forms(ast, *base),
        Expr::Index { base, index } => {
            check_macro_forms(ast, *base)?;
            check_macro_forms(ast, *index)
        }
        Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
            check_macro_forms(ast, *lhs)?;
            check_macro_forms(ast, *rhs)
        }
        Expr::Unary { expr, .. }
        | Expr::Cast { expr, .. }
        | Expr::Ref { expr, .. }
        | Expr::Deref(expr)
        | Expr::Try(expr)
        | Expr::Await(expr) => check_macro_forms(ast, *expr),
        Expr::StructLit { fields, update, .. } => {
            for &(_, _, fe) in fields {
                check_macro_forms(ast, fe)?;
            }
            if let Some(u) = update {
                check_macro_forms(ast, *u)?;
            }
            Ok(())
        }
        Expr::Tuple(elems) | Expr::Array(elems) => {
            for &el in elems {
                check_macro_forms(ast, el)?;
            }
            Ok(())
        }
        Expr::ArrayRepeat { value, len } => {
            check_macro_forms(ast, *value)?;
            check_macro_forms(ast, *len)
        }
        Expr::Range { lo, hi, .. } => {
            for x in [lo, hi].into_iter().flatten() {
                check_macro_forms(ast, *x)?;
            }
            Ok(())
        }
        Expr::Break { value, .. } | Expr::Return(value) => match value {
            Some(v) => check_macro_forms(ast, *v),
            None => Ok(()),
        },
        Expr::Int(..)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::ByteStr(_)
        | Expr::Char(_)
        | Expr::Unit
        | Expr::Float(_)
        | Expr::Path(_)
        | Expr::SelfValue
        | Expr::QPath { .. }
        | Expr::Continue(_)
        | Expr::Underscore
        | Expr::MacroCall(_)
        | Expr::OffsetOf { .. }
        | Expr::Closure { .. } => Ok(()),
    }
}

/// True for an E0493 diagnostic from `drop_diag` (the only errors
/// a dead-branch scan propagates).
pub(crate) fn is_drop_diag(d: &Diag) -> bool {
    d.code == C_NONCONST && d.message.starts_with("destructor of ")
}

/// True for the E0015 of a call to a non-const fn or method. rustc
/// checks it statically, so a dead branch scan keeps it too.
pub(crate) fn is_nonconst_call_diag(d: &Diag) -> bool {
    d.code == C_NONCONST && d.message.starts_with("cannot call non-const function")
}

/// The E0493 error for a destructor that would run during const
/// evaluation.
fn drop_diag<'a, C: ConstCx<'a>>(cx: &C, t: Ty, span: Span) -> Diag {
    Diag::new(
        C_NONCONST,
        span,
        format!("destructor of `{}` cannot be evaluated at compile-time", cx.ty_text(t)),
        "Move the value out of the const context whole, or use a type without a destructor there.",
    )
}

/// The field types to walk a const aggregate or variant value at
/// type `t`: a tuple's elements, an array's element repeated, an
/// Adt variant's fields read through the instance's args, or an
/// `Option`/`Result` payload. None when the value's parts have no
/// known types here (a builtin aggregate the walk cannot see into).
/// A value of type `t` for a dead-branch scan's placeholder
/// bindings (`Evaluator::dead_env`): zero scalars, `None`, empty
/// `Vec`/`String`, and aggregates of those. None when the type has no
/// value the evaluator can make up.
fn zero_value<'a, C: ConstCx<'a>>(cx: &mut C, t: Ty, depth: u32) -> Option<ConstValue> {
    if depth > 8 {
        return None;
    }
    let tys = cx.tys_ref();
    match tys.kind(t) {
        TyKind::Int(_) => Some(ConstValue::Int(0)),
        TyKind::Float(f) => Some(ConstValue::Float(0, f)),
        TyKind::Bool => Some(ConstValue::Bool(false)),
        TyKind::Char => Some(ConstValue::Char('\0')),
        TyKind::Ref(_, _, it) => Some(ConstValue::Ref(Box::new(zero_value(cx, it, depth + 1)?))),
        TyKind::Array(el, n) => match tys.const_kind(n) {
            super::ConstKind::Int(n) => Some(ConstValue::Repeat(Box::new(zero_value(cx, el, depth + 1)?), u64::try_from(n).ok()?)),
            _ => None,
        },
        TyKind::Tuple(ts) => {
            let parts = tys.tys_of(ts).to_vec();
            parts.into_iter().map(|p| zero_value(cx, p, depth + 1)).collect::<Option<Vec<_>>>().map(ConstValue::Aggregate)
        }
        _ if t == UNIT => Some(ConstValue::Unit),
        _ => {
            if tys.option_elem(t).is_some() {
                return Some(ConstValue::Variant(0, Vec::new()));
            }
            if matches!(tys.builtin_of(t), Some(super::BuiltinTy::Vec | super::BuiltinTy::String)) {
                return Some(ConstValue::Aggregate(Vec::new()));
            }
            let adt = tys.local_adt(t)?;
            let n = cx.variant_fields(adt, 0).len();
            let parts = part_tys(cx, t, 0, n)?;
            let vals = parts.into_iter().map(|p| zero_value(cx, p, depth + 1)).collect::<Option<Vec<_>>>()?;
            Some(if cx.is_enum(adt) { ConstValue::Variant(0, vals) } else { ConstValue::Aggregate(vals) })
        }
    }
}

fn part_tys<'a, C: ConstCx<'a>>(cx: &mut C, t: Ty, variant: u32, n: usize) -> Option<Vec<Ty>> {
    let tys = cx.tys_ref();
    match tys.kind(t) {
        TyKind::Tuple(ts) => Some(tys.tys_of(ts).to_vec()),
        TyKind::Array(elem, _) => Some(vec![elem; n]),
        _ => {
            if let Some(elem) = tys.option_elem(t) {
                return Some(vec![elem; n]);
            }
            if let Some((ok, err)) = tys.result_args(t) {
                return Some(vec![if variant == 0 { ok } else { err }; n]);
            }
            let adt = tys.local_adt(t)?;
            let args: Vec<super::GenericArg> = tys.adt_parts(t).map(|(_, a)| tys.args(a).to_vec()).unwrap_or_default();
            let fields = cx.variant_fields(adt, variant);
            Some(fields.iter().map(|f| if args.is_empty() { f.1 } else { super::subst(cx.tys(), f.1, &args) }).collect())
        }
    }
}

/// The E0492/E0764 check on a const item's final value: a borrow
/// of a temporary inside it is promoted to `'static`, which rustc
/// allows only for a shared borrow of a type without interior
/// mutability. A borrow of a static (`StaticRef`) is not a
/// temporary and always passes.
fn check_final_refs<'a, C: ConstCx<'a>>(cx: &mut C, v: &ConstValue, t: Ty, span: Span) -> Result<(), Diag> {
    match v {
        ConstValue::Ref(inner) => {
            let (mutable, inner_ty) = match cx.tys_ref().kind(t) {
                TyKind::Ref(_, m, it) => (m.is_mut(), it),
                _ => return Ok(()),
            };
            if mutable {
                return Err(Diag::new(
                    C_NONCONST,
                    span,
                    "mutable borrows of temporaries that have their lifetime extended until the end of the program are not allowed",
                    "Borrow a `static` item instead, or make the item's type the value itself.",
                ));
            }
            if cx.interior_mut(inner_ty) {
                return Err(Diag::new(
                    C_NONCONST,
                    span,
                    "interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed",
                    "Put the value in a `static` item and borrow that instead.",
                ));
            }
            check_final_refs(cx, inner, inner_ty, span)
        }
        ConstValue::Aggregate(..) | ConstValue::Repeat(..) | ConstValue::Bytes(_)
            if matches!(cx.tys_ref().kind(t), TyKind::Ref(_, _, s) if matches!(cx.tys_ref().kind(s), TyKind::Slice(_))) =>
        {
            // A slice over a promoted backing array: the backing is
            // the temporary the borrow keeps alive.
            let (mutable, elem) = match cx.tys_ref().kind(t) {
                TyKind::Ref(_, m, s) => match cx.tys_ref().kind(s) {
                    TyKind::Slice(elem) => (m.is_mut(), elem),
                    _ => return Ok(()),
                },
                _ => return Ok(()),
            };
            if mutable {
                return Err(Diag::new(
                    C_NONCONST,
                    span,
                    "mutable borrows of temporaries that have their lifetime extended until the end of the program are not allowed",
                    "Borrow a `static` item instead, or make the item's type the value itself.",
                ));
            }
            if cx.interior_mut(elem) {
                return Err(Diag::new(
                    C_NONCONST,
                    span,
                    "interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed",
                    "Put the value in a `static` item and borrow that instead.",
                ));
            }
            match v {
                ConstValue::Aggregate(vals) => {
                    for x in vals {
                        check_final_refs(cx, x, elem, span)?;
                    }
                    Ok(())
                }
                ConstValue::Repeat(x, _) => check_final_refs(cx, x, elem, span),
                _ => Ok(()),
            }
        }
        ConstValue::Aggregate(vals) => match part_tys(cx, t, 0, vals.len()) {
            Some(ftys) => {
                for (x, ft) in vals.iter().zip(ftys) {
                    check_final_refs(cx, x, ft, span)?;
                }
                Ok(())
            }
            None => Ok(()),
        },
        ConstValue::Variant(variant, vals) => match part_tys(cx, t, *variant, vals.len()) {
            Some(ftys) => {
                for (x, ft) in vals.iter().zip(ftys) {
                    check_final_refs(cx, x, ft, span)?;
                }
                Ok(())
            }
            None => Ok(()),
        },
        ConstValue::Repeat(x, _) => match cx.tys_ref().kind(t) {
            TyKind::Array(elem, _) => check_final_refs(cx, x, elem, span),
            _ => Ok(()),
        },
        _ => Ok(()),
    }
}

/// The literal text of a format string with no arguments, if it is all literal.
fn fmt_text(fmt: &[ast::FmtPiece]) -> Option<String> {
    let mut out = String::new();
    for p in fmt {
        match p {
            ast::FmtPiece::Lit(s) => out.push_str(s),
            ast::FmtPiece::Arg { .. } => out.push_str("{..}"),
        }
    }
    Some(out)
}

/// The evaluator copies a value on every borrow, so a write through a
/// `&mut` reaches its place only when the borrow is a const fn call
/// argument (the call writes it back). Every other way to hold a `&mut`
/// value is outside the bound: a borrow kept in a binding or a value, a
/// pattern matched through a `&mut`, a const fn whose parameter or
/// result holds one in another type. Such a write would be lost, a
/// wrong value (fx-constbck).
fn mut_ref_outside(span: Span, what: &str) -> Diag {
    Diag::new(C_OUTSIDE, span, format!("{what} is outside the bounded const evaluator"), "Pass `&mut place` straight to a const fn, or compute the value without a `&mut`.")
}

/// True when a const value holds a reference anywhere in it (a
/// promoted or `&mut` cell, or a reference to a static). String and
/// byte literals are shared data and count as none.
fn value_has_ref(v: &ConstValue) -> bool {
    match v {
        ConstValue::Ref(_) | ConstValue::StaticRef(_) | ConstValue::StaticPlace(..) => true,
        ConstValue::Aggregate(vs) | ConstValue::Variant(_, vs) => vs.iter().any(value_has_ref),
        ConstValue::Repeat(x, _) => value_has_ref(x),
        _ => false,
    }
}

/// True when a value of type `t` may hold a `&mut` reference: in
/// itself, an element, a field of a crate Adt (type args substituted),
/// or a type argument of any other Adt.
/// `seen` holds the types on the walk (a recursive type).
fn holds_mut_ref<'a, C: ConstCx<'a>>(cx: &mut C, t: Ty, seen: &mut Vec<Ty>) -> bool {
    if seen.contains(&t) {
        return false;
    }
    // A type that keeps growing on the walk (`L<T>` holding `L<(T, T)>`):
    // assume it may hold one.
    if seen.len() > 32 {
        return true;
    }
    seen.push(t);
    let kind = cx.tys_ref().kind(t);
    let out = match kind {
        TyKind::Ref(_, m, inner) => m.is_mut() || holds_mut_ref(cx, inner, seen),
        TyKind::Slice(e) | TyKind::Array(e, _) => holds_mut_ref(cx, e, seen),
        TyKind::Tuple(ts) => {
            let ts = cx.tys_ref().tys_of(ts).to_vec();
            ts.into_iter().any(|e| holds_mut_ref(cx, e, seen))
        }
        TyKind::Adt(_, a) => {
            let args = cx.tys_ref().args(a).to_vec();
            // A crate Adt holds what its fields hold (a `PhantomData`
            // marker over a `&mut` holds none); any other, its type args.
            match cx.tys_ref().local_adt(t) {
                None => args.iter().any(|g| g.as_ty().is_some_and(|e| holds_mut_ref(cx, e, seen))),
                Some(adt) => (0..cx.variant_count(adt)).any(|v| {
                    let fields = cx.variant_fields(adt, v);
                    fields.into_iter().any(|(_, f)| {
                        let f = if args.is_empty() { f } else { super::subst(cx.tys(), f, &args) };
                        holds_mut_ref(cx, f, seen)
                    })
                }),
            }
        }
        _ => false,
    };
    seen.pop();
    out
}
