// Syntax tree. Nodes live in flat arenas and refer to each other by u32 index, not by pointer.
//
// AST v2 (docs/ARCH.md section 9.2, S3b): this file freezes node shapes for all
// syntax of milestones 4 to 7. Existing variants keep their order; new variants are
// appended at the end of each enum and must never be renumbered. The parser still
// rejects most new forms with a stable code (see docs/errors/REGISTRY.md); each
// form's parser lands later with its feature owner, starting with W-CORELANG.
// Until then, code outside the parser never sees the new nodes in a program that
// passes parsing, but every later package codes against these shapes.
use crate::diag::Span;
use crate::intern::Sym;
use crate::lexer::{Delim, IntSuffix, TokenTree};

macro_rules! ids {
    ($($name:ident),*) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub u32);
    )*};
}
ids!(ExprId, PatId, TyId, BlockId);

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Default)]
pub struct Ast {
    /// Inner attributes at the start of the file (`#![..]`, `//!` docs).
    /// They scope over the whole file's module, never over one item.
    pub inner_attrs: Vec<Attr>,
    pub items: Vec<Item>,
    /// Items written inside function bodies, in order of appearance. A body item
    /// statement (`Stmt::Item`) holds an index into this list. These are never
    /// top-level items: collect must not treat them as module items.
    pub stmt_items: Vec<Item>,
    pub exprs: Vec<Expr>,
    pub expr_spans: Vec<Span>,
    pub pats: Vec<Pat>,
    pub pat_spans: Vec<Span>,
    pub tys: Vec<TyExpr>,
    pub ty_spans: Vec<Span>,
    pub blocks: Vec<Block>,
    pub strings: Vec<String>,
    /// Byte string literal data (`b".."`, `include_bytes!`): one buffer
    /// per literal, indexed by `Expr::ByteStr`. Large blobs stay one
    /// buffer end to end, never one node or value per byte.
    pub blobs: Vec<ByteBlob>,
    /// Byte ranges of spliced shipped std source in file 0, by crate
    /// (the driver's std splice, or a whole shipped file at std load).
    /// Set before collect, which copies it to `Program::shipped_ranges`
    /// so the impls of std source (`impl<T> Option<T>`) collect as std.
    pub shipped: Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
    /// The byte range in file 0 of the std methods of the lang enums
    /// (`impl<T> Option<T>` and kin, inside `shipped`): their own scope,
    /// where no user name is visible (`Program::in_lang_methods`).
    pub lang_methods: (u32, u32),
    /// Traits a function-local `use` brings into scope for method
    /// calls, filled by the resolver's rewrite (`Rewrite::stmt_item`)
    /// and keyed by the use item's span: a span survives flattening
    /// and chunk concatenation, so checker blocks read their own
    /// items' records. A trait import has no path in the body for
    /// the rewrite to mark (`use Trait as _;` binds no name), so the
    /// resolved targets ride here instead (`Ctx::trait_scopes`).
    pub use_traits: Vec<(Span, UseTrait)>,
    /// Expressions that were written in parentheses, sorted by id.
    /// The parser drops the parens themselves; the distinction
    /// still matters for a const parameter used as a const
    /// argument, where `(N)` is a const operation and `N` is not.
    pub paren_exprs: Vec<u32>,
    /// Types that were written in parentheses, like `paren_exprs`
    /// (the type parser returns the inner type directly, so a
    /// `(N)` generic argument is otherwise indistinguishable).
    pub paren_tys: Vec<u32>,
    /// Anonymous consts written outside fn bodies, by value id
    /// (`AnonConst`, `Ast::anon_const`).
    pub anon_consts: Vec<AnonConst>,
}

/// An anonymous const outside fn bodies (an array length in a type, a
/// const generic argument or default, an enum discriminant) with its
/// expression as a body of its own, as `ConstDef::init_fn`: collect
/// type- and borrow-checks it (check/const_body.rs). Ordered by
/// `value`; looked up by the value's id, so the entry of a node a daemon
/// patch left behind is never read. Literals and one-segment paths have
/// none (the scalar checks in collect cover them).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct AnonConst {
    pub value: ExprId,
    pub def: FnDef,
    /// The module its names resolve in, set by the resolver's rewrite.
    pub module: Option<crate::ty::defs::ModuleId>,
}

/// One trait a function-local `use` resolved to (`Ast::use_traits`).
#[derive(Clone, Debug)]
pub enum UseTrait {
    /// A crate trait, by its flat name (the checker's `trait_names` key).
    Flat(Sym),
    /// A std trait by its canonical path (`std::io::Write` segments),
    /// for names with no spliced source def at resolve time.
    Std(Vec<Sym>),
}

/// A byte buffer shared by reference, with a window into it. Cloning
/// and slicing are O(1): a sub-slice keeps the same buffer with a new
/// window. Writing one byte copies the window only when the buffer
/// is still shared (copy on write), which matches array value
/// semantics: two holders of one array value never see each other's
/// writes.
#[derive(Clone)]
pub struct ByteBlob {
    buf: std::sync::Arc<Vec<u8>>,
    start: u32,
    len: u32,
}

impl ByteBlob {
    /// A blob over all of `bytes`.
    pub fn new(bytes: Vec<u8>) -> ByteBlob {
        let len = bytes.len() as u32;
        ByteBlob { buf: std::sync::Arc::new(bytes), start: 0, len }
    }

    /// The bytes in the window.
    pub fn as_slice(&self) -> &[u8] {
        &self.buf[self.start as usize..(self.start + self.len) as usize]
    }

    pub fn len(&self) -> usize {
        self.len as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The window `lo..hi`, when it is inside this blob.
    pub fn sub(&self, lo: usize, hi: usize) -> Option<ByteBlob> {
        if lo > hi || hi > self.len() {
            return None;
        }
        Some(ByteBlob { buf: self.buf.clone(), start: self.start + lo as u32, len: (hi - lo) as u32 })
    }

    /// Sets one byte, copying the window first when it is shared or
    /// is not the whole buffer. False when `i` is out of bounds.
    pub fn set(&mut self, i: usize, b: u8) -> bool {
        if i >= self.len() {
            return false;
        }
        if self.start != 0 || self.len as usize != self.buf.len() {
            *self = ByteBlob::new(self.as_slice().to_vec());
        }
        std::sync::Arc::make_mut(&mut self.buf)[i] = b;
        true
    }
}

impl PartialEq for ByteBlob {
    fn eq(&self, other: &ByteBlob) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl Eq for ByteBlob {}

impl std::fmt::Debug for ByteBlob {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.as_slice();
        write!(f, "ByteBlob(len {}, {:?}..)", s.len(), &s[..s.len().min(8)])
    }
}

impl Ast {
    /// Reserves the node arrays for a parse of `n` tokens (an upper
    /// estimate; untouched capacity costs no memory). Growing them by
    /// doubling copied every array several times, and each copy touched
    /// fresh pages in the parallel parse.
    pub fn reserve_for_tokens(&mut self, n: usize) {
        self.exprs.reserve(n / 2);
        self.expr_spans.reserve(n / 2);
        self.pats.reserve(n / 8);
        self.pat_spans.reserve(n / 8);
        self.tys.reserve(n / 8);
        self.ty_spans.reserve(n / 8);
        self.blocks.reserve(n / 16);
    }
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.0 as usize]
    }
    pub fn expr_span(&self, id: ExprId) -> Span {
        self.expr_spans[id.0 as usize]
    }
    /// True for a closure the parser made from a std fn used as a value
    /// (`parser::eta_closure`): it, its call body, and the callee share
    /// the path's span, which no written closure can (`|` comes first).
    pub fn is_eta_closure(&self, id: ExprId) -> bool {
        let span = self.expr_span(id);
        match self.expr(id) {
            Expr::Closure { body, .. } => {
                self.expr_span(*body) == span && matches!(self.expr(*body), Expr::Call { callee, .. } if self.expr_span(*callee) == span)
            }
            _ => false,
        }
    }
    pub fn pat(&self, id: PatId) -> &Pat {
        &self.pats[id.0 as usize]
    }
    pub fn pat_span(&self, id: PatId) -> Span {
        self.pat_spans[id.0 as usize]
    }
    pub fn ty(&self, id: TyId) -> &TyExpr {
        &self.tys[id.0 as usize]
    }
    pub fn ty_span(&self, id: TyId) -> Span {
        self.ty_spans[id.0 as usize]
    }
    pub fn block(&self, id: BlockId) -> &Block {
        &self.blocks[id.0 as usize]
    }
    /// True when expression `id` was written in parentheses.
    pub fn is_parenthesized(&self, id: ExprId) -> bool {
        self.paren_exprs.binary_search(&id.0).is_ok()
    }
    /// True when type `id` was written in parentheses.
    pub fn is_parenthesized_ty(&self, id: TyId) -> bool {
        self.paren_tys.binary_search(&id.0).is_ok()
    }
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct Item {
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub kind: ItemKind,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum ItemKind {
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Impl(ImplDef),
    /// A `use` declaration. Until module resolution lands the tree is recorded
    /// but has no effect, exactly as the old payload-free `Use` behaved.
    Use(UseDef),
    // ---- AST v2 items: shapes only for now; the parser rejects each form. ----
    Mod(ModDef),
    Trait(TraitDef),
    Type(TypeAliasDef),
    Const(ConstDef),
    Static(StaticDef),
    MacroRules(MacroRulesDef),
    ExternCrate(ExternCrateDef),
    ExternBlock(ExternBlockDef),
    Union(UnionDef),
    /// A macro call in item position: `make!(...)` or `make! { ... }`.
    MacroCall(MacroCall),
}

/// Visibility as written: private, `pub`, or `pub(path)` where the path is
/// `crate`, `super`, or follows `in`. Not checked yet; recorded for resolve.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
    Restricted {
        path: Vec<PathSeg>,
        span: Span,
    },
}

/// A lifetime as written, without the leading `'`: `'a`, `'static`, or `'_`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lifetime {
    pub name: Sym,
    pub span: Span,
}

/// A loop or block label as written (`'outer`). Same token as a lifetime; the
/// syntactic position tells them apart.
pub type Label = Lifetime;

/// Whether an attribute is outer (`#[..]`, on the next item) or inner (`#![..]`,
/// on the enclosing item).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttrStyle {
    Outer,
    Inner,
}

/// The part of an attribute after its path: nothing, `= value`, or a token list.
#[derive(Clone, Debug)]
pub enum AttrInput {
    None,
    /// `#[path = "file.rs"]`: the value expression (in practice a literal).
    Eq(ExprId),
    /// `#[cfg(target_os = "linux")]`, `#[derive(Debug)]`, `#[repr(C)]`: the
    /// delimiter and the raw token trees inside. Each attribute's owner parses
    /// its own grammar from the trees (cfg in resolve, derive in collect).
    List(Delim, Vec<TokenTree>),
}

/// One attribute. `derives` on struct and enum defs stay as the fast path for
/// today's derive handling; `attrs` is the general record later stages read
/// (cfg stripping, `#[path]`, `#[repr]`, test markers, and so on).
#[derive(Clone, Debug)]
pub struct Attr {
    pub style: AttrStyle,
    pub path: Vec<PathSeg>,
    pub input: AttrInput,
    pub span: Span,
}

/// Generic parameters as written: `<` params `>`. Empty when an item has none.
#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

/// One generic parameter: a lifetime, a type, or a const, each with its
/// written bounds and default.
#[derive(Clone, Debug)]
pub enum GenericParam {
    Lifetime { lt: Lifetime, bounds: Vec<Lifetime>, attrs: Vec<Attr> },
    Type { name: Sym, span: Span, bounds: Vec<TraitBound>, default: Option<TyId>, attrs: Vec<Attr> },
    Const { name: Sym, span: Span, ty: TyId, default: Option<ExprId>, attrs: Vec<Attr> },
}

/// A `where` clause as written. Empty when an item has none.
#[derive(Clone, Debug, Default)]
pub struct WhereClause {
    pub preds: Vec<WherePred>,
    pub span: Span,
}

/// One `where` predicate. `binder` is a leading `for<'a, ..>` on a type
/// predicate (empty when absent).
#[derive(Clone, Debug)]
pub enum WherePred {
    Type { binder: Vec<Lifetime>, ty: TyId, bounds: Vec<TraitBound> },
    Lifetime { lt: Lifetime, bounds: Vec<Lifetime> },
}

/// One bound in a bound list (`T: A + B + 'a`): a trait bound (optionally
/// higher-ranked and optionally `?`-relaxed) or a lifetime bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraitBound {
    Trait { binder: Vec<Lifetime>, trait_ref: TraitRefExpr, maybe: bool },
    Lifetime(Lifetime),
}

/// A `use<..>` precise-capturing list on an `impl Trait`: the generic
/// params its hidden type may name. Without one, edition 2024 captures
/// every param in scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseCaps {
    pub args: Vec<UseArg>,
    pub span: Span,
}

/// One entry of a `use<..>` list: a lifetime (`'a`, `'_`), or a type or
/// const param (or `Self`) by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UseArg {
    Lifetime(Lifetime),
    Param(Sym, Span),
}

/// A trait reference as written in a bound or an impl header: a path whose
/// last segment may use parenthesized sugar (`Fn(A) -> B`) or angle bindings
/// (`Iterator<Item = u8>`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitRefExpr {
    pub path: Vec<PathSeg>,
}

/// Qualifiers on a function: `const`, `async`, `unsafe`, and `extern "abi"`.
/// `abi` is an index into the AST string table.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FnQual {
    pub is_const: bool,
    pub is_async: bool,
    pub is_unsafe: bool,
    pub abi: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelfKind {
    Value,
    Ref,
    RefMut,
    /// A typed receiver: `self: Box<Self>` and kin (docs/ARCH.md section 2.9).
    /// The written type is in `SelfParam::ty`.
    Typed,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct SelfParam {
    pub kind: SelfKind,
    pub mutable: bool,
    /// The lifetime on a reference receiver (`&'a self`), when written.
    pub lifetime: Option<Lifetime>,
    /// The written receiver type for `SelfKind::Typed` (`self: Rc<Self>`).
    pub ty: Option<TyId>,
    pub attrs: Vec<Attr>,
    pub span: Span,
    /// The `self` keyword alone: its context names the binding when a
    /// macro writes `&` and passes `self` in (`span` then joins two
    /// contexts and falls back to the call site).
    pub self_span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct Param {
    /// The binding name for a plain `name: Ty` parameter. When `pat` is set it
    /// holds the pattern instead and `name` and `mutable` are not used.
    pub name: Sym,
    pub mutable: bool,
    pub pat: Option<PatId>,
    pub ty: TyId,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct FnDef {
    pub name: Sym,
    pub name_span: Span,
    /// True for `#[test]` functions. Used by `lust test`; ignored by normal builds.
    pub is_test: bool,
    /// Visibility and attributes as written. A top-level fn repeats its item's
    /// visibility here so impl and trait methods carry their own the same way.
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub qual: FnQual,
    pub generics: Generics,
    pub self_param: Option<SelfParam>,
    pub params: Vec<Param>,
    /// True for a trailing `...` variadic marker (extern fns only).
    pub variadic: bool,
    pub ret: Option<TyId>,
    pub where_clause: WhereClause,
    /// The body block, or None for a declaration without a body (a trait
    /// method signature or a foreign fn). Every fn the parser accepts today
    /// has a body.
    pub body: Option<BlockId>,
    /// Expressions and patterns of this function are contiguous: `exprs.0..exprs.1`.
    pub exprs: (u32, u32),
    pub pats: (u32, u32),
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct FieldDef {
    pub name: Sym,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub ty: TyId,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct StructDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    /// Unit, tuple, or named fields, in the same shape as enum variants.
    /// For tuple fields, `FieldDef::name` is meaningless and must not be read.
    pub fields: VariantFields,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum VariantFields {
    Unit,
    Tuple(Vec<FieldDef>),
    Struct(Vec<FieldDef>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct VariantDef {
    pub name: Sym,
    pub attrs: Vec<Attr>,
    pub fields: VariantFields,
    /// An explicit discriminant (`A = 3`), when written.
    pub discriminant: Option<ExprId>,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct EnumDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub variants: Vec<VariantDef>,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ImplDef {
    /// Inner attributes at the start of the impl body (`#![..]`).
    pub inner_attrs: Vec<Attr>,
    pub generics: Generics,
    pub is_unsafe: bool,
    /// True for a negative impl (`impl !Send for T`).
    pub is_negative: bool,
    /// The trait being implemented, or None for an inherent impl.
    pub trait_ref: Option<TraitRefExpr>,
    pub self_ty: TyId,
    pub where_clause: WhereClause,
    pub fns: Vec<FnDef>,
    pub consts: Vec<AssocConstDef>,
    pub types: Vec<AssocTypeDef>,
    pub span: Span,
    /// True for an impl written inside a fn body, once the resolver hoisted
    /// it to its module's items (`worklist::hoist_block_impls`): its
    /// header and bodies see the block items around its span (R18).
    pub in_body: bool,
}

/// A `use` declaration: one tree (`use a::{b, c as d, self};`, `use a::*;`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct UseDef {
    pub tree: UseTree,
    pub span: Span,
}

/// One use tree node. `prefix` is the path written before this node: for
/// `a::b::{c, d}` the group node has prefix `a::b` and each child has an
/// empty prefix and one name. A node's own name, when it has one, is the
/// last prefix segment.
#[derive(Clone, Debug)]
pub struct UseTree {
    /// True when the tree was written with a leading `::` (`use ::a::b;`).
    pub leading_colon: bool,
    pub prefix: Vec<PathSeg>,
    pub kind: UseKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum UseKind {
    /// Imports the prefix's last segment, renamed with `as` when present.
    /// `self` in a group is a prefix segment naming the module itself.
    Simple {
        rename: Option<Sym>,
    },
    Glob,
    Group(Vec<UseTree>),
}

/// A `mod` item. `body` is Some for an inline module (`mod m { .. }`) and
/// None for a file module (`mod m;`); a `#[path]` attribute sits in the
/// item's attrs.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ModDef {
    pub name: Sym,
    pub name_span: Span,
    /// Inner attributes at the start of an inline body (`#![..]`).
    pub inner_attrs: Vec<Attr>,
    pub body: Option<Vec<Item>>,
    pub span: Span,
}

/// A trait definition. Method signatures are `FnDef`s with no body;
/// a method with a default body has one.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct TraitDef {
    /// Inner attributes at the start of the trait body (`#![..]`).
    pub inner_attrs: Vec<Attr>,
    pub name: Sym,
    pub name_span: Span,
    pub is_unsafe: bool,
    pub is_auto: bool,
    pub generics: Generics,
    pub bounds: Vec<TraitBound>,
    pub where_clause: WhereClause,
    pub fns: Vec<FnDef>,
    pub consts: Vec<AssocConstDef>,
    pub types: Vec<AssocTypeDef>,
    pub span: Span,
}

/// An associated const in a trait or an impl. `default` is the value in an
/// impl, and in a trait when a default is written.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct AssocConstDef {
    pub name: Sym,
    pub name_span: Span,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub ty: TyId,
    pub default: Option<ExprId>,
    pub span: Span,
    /// The value as a body of its own (`ConstDef::init_fn`).
    pub init_fn: Option<Box<FnDef>>,
}

/// An associated type in a trait or an impl. In an impl, `default` is the
/// assigned type (`type Item = u8;`); in a trait it is the written default.
/// Its own generics (a GAT) are recorded here and rejected by the trait owner.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct AssocTypeDef {
    pub name: Sym,
    pub name_span: Span,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub generics: Generics,
    pub bounds: Vec<TraitBound>,
    pub where_clause: WhereClause,
    pub default: Option<TyId>,
    pub span: Span,
}

/// A `type` alias item: `type Name<..> = Target;`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct TypeAliasDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub where_clause: WhereClause,
    pub ty: TyId,
    pub span: Span,
}

/// A `const` item. `name` is None for an unnamed const (`const _: () = ..;`).
/// `value` is None only where Rust allows a declaration without one.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ConstDef {
    pub name: Option<Sym>,
    pub name_span: Span,
    pub ty: TyId,
    pub value: Option<ExprId>,
    pub span: Span,
    /// The value as the body of a fn with no parameters (a block whose
    /// tail is `value`, over the value's expr and pat ranges), so the
    /// initializer is type- and borrow-checked like a fn body
    /// (check/const_body.rs). None when there is no value.
    pub init_fn: Option<Box<FnDef>>,
}

/// A `static` item. `value` is None only in an extern block.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct StaticDef {
    pub name: Sym,
    pub name_span: Span,
    pub mutable: bool,
    pub ty: TyId,
    pub value: Option<ExprId>,
    pub span: Span,
    /// The value as a body of its own (`ConstDef::init_fn`).
    pub init_fn: Option<Box<FnDef>>,
}

/// A `macro_rules!` definition. The rules stay as raw token trees: matching
/// and transcription belong to the macro owner (docs/ARCH.md section 6).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct MacroRulesDef {
    pub name: Sym,
    pub name_span: Span,
    pub delim: Delim,
    pub tokens: Vec<TokenTree>,
    pub span: Span,
}

/// A macro call as raw token trees, in whichever syntactic position it was
/// written. Built-in macros keep their parsed `Expr::Macro` form; this shape
/// is for user macros the expander will own.
#[derive(Clone, Debug)]
pub struct MacroCall {
    pub path: Vec<PathSeg>,
    pub delim: Delim,
    pub tokens: Vec<TokenTree>,
    pub span: Span,
}

/// An `extern crate` item, with an `as` rename when written.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ExternCrateDef {
    pub name: Sym,
    pub name_span: Span,
    pub rename: Option<Sym>,
    pub span: Span,
}

/// An `extern "abi" { .. }` block of foreign declarations.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ExternBlockDef {
    /// The ABI string as an index into the AST string table, when written.
    pub abi: Option<u32>,
    pub is_unsafe: bool,
    pub items: Vec<ForeignItem>,
    pub span: Span,
}

/// One declaration inside an extern block.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum ForeignItem {
    Fn(FnDef),
    Static(StaticDef),
    /// An opaque foreign type: `type Opaque;`.
    Type {
        name: Sym,
        name_span: Span,
        vis: Vis,
        attrs: Vec<Attr>,
        generics: Generics,
        where_clause: WhereClause,
        span: Span,
    },
    MacroCall(MacroCall),
}

/// A `union` definition: named fields, like a struct.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct UnionDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub fields: Vec<FieldDef>,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
    pub span: Span,
}

/// Generic arguments on one path segment, as written.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum GenericArgs {
    #[default]
    None,
    /// Angle arguments: `<T, 'a, 3, Item = u8>`, in written order.
    Angle(Vec<GenericArg>),
    /// Parenthesized sugar on a trait path: `Fn(A, B) -> C`.
    Parenthesized { inputs: Vec<TyId>, output: Option<TyId> },
}

/// One generic argument. A const argument is an expression: a literal, a
/// path to a const param or item, or a braced const block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GenericArg {
    Type(TyId),
    Lifetime(Lifetime),
    Const(ExprId),
    /// An associated binding: `Item = u8`, `Item: Clone`, or `Output = C`.
    Binding {
        name: Sym,
        span: Span,
        kind: BindingKind,
    },
}

/// The right side of an associated binding in generic arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingKind {
    EqTy(TyId),
    EqConst(ExprId),
    Constraint(Vec<TraitBound>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathSeg {
    pub name: Sym,
    pub args: GenericArgs,
}

impl PathSeg {
    /// A segment with no generic arguments.
    pub fn plain(name: Sym) -> PathSeg {
        PathSeg { name, args: GenericArgs::None }
    }
    /// The type arguments among the angle arguments, in written order.
    /// Lifetime, const, and binding arguments are skipped; callers that must
    /// reject those instead of skipping check `args` themselves.
    pub fn type_args(&self) -> Vec<TyId> {
        match &self.args {
            GenericArgs::Angle(args) => args
                .iter()
                .filter_map(|a| match a {
                    GenericArg::Type(t) => Some(*t),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }
    /// True when the segment carries any written generic argument.
    pub fn has_args(&self) -> bool {
        !matches!(self.args, GenericArgs::None)
    }
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum TyExpr {
    Path(Vec<PathSeg>),
    Ref {
        lifetime: Option<Lifetime>,
        mutable: bool,
        inner: TyId,
    },
    Unit,
    // ---- AST v2 types: shapes only for now; the parser rejects each form. ----
    /// A tuple type with one or more elements. The empty tuple stays `Unit`.
    Tuple(Vec<TyId>),
    /// `[T; N]`: the element type and the length expression.
    Array {
        inner: TyId,
        len: ExprId,
    },
    /// `[T]`.
    Slice(TyId),
    /// A raw pointer: `*const T` when `mutable` is false, `*mut T` when true.
    Ptr {
        mutable: bool,
        inner: TyId,
    },
    /// A function pointer type, with a leading `for<'a, ..>` binder when written.
    FnPtr {
        binder: Vec<Lifetime>,
        qual: FnQual,
        inputs: Vec<FtyParam>,
        variadic: bool,
        ret: Option<TyId>,
    },
    /// `dyn Bounds + 'a`: trait bounds plus a written lifetime bound.
    Dyn {
        binder: Vec<Lifetime>,
        bounds: Vec<TraitBound>,
        lifetime: Option<Lifetime>,
    },
    /// `impl Bounds` in argument, return, or associated position, with
    /// its `use<..>` precise-capturing list when written.
    ImplTrait {
        bounds: Vec<TraitBound>,
        captures: Option<UseCaps>,
    },
    /// A qualified path: `<SelfTy as Trait>::Segs`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// The never type `!`.
    Never,
    /// A parenthesized type `(T)`.
    Paren(TyId),
    /// The inferred type `_`.
    Infer,
    /// A macro call in type position.
    MacroCall(MacroCall),
}

/// One parameter of a function pointer type. The name (`fn(x: i64)`) is
/// optional and has no meaning beyond the signature text.
#[derive(Clone, Debug)]
pub struct FtyParam {
    pub name: Option<Sym>,
    pub ty: TyId,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct Block {
    /// Inner attributes at the start of the block (`#![..]`), where Rust
    /// permits them (a fn body, a statement block, a loop body, and kin).
    pub inner_attrs: Vec<Attr>,
    pub stmts: Vec<Stmt>,
    pub tail: Option<ExprId>,
    /// Outer attributes on the tail expression (`#[allow(..)] expr`).
    pub tail_attrs: Vec<Attr>,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum Stmt {
    /// A `let` statement. `els` is the block of a `let .. else { .. }` form.
    Let {
        pat: PatId,
        ty: Option<TyId>,
        init: Option<ExprId>,
        els: Option<BlockId>,
        attrs: Vec<Attr>,
        span: Span,
    },
    Expr {
        expr: ExprId,
        semi: bool,
        /// Outer attributes on the statement (`#[allow(..)] expr;`).
        attrs: Vec<Attr>,
    },
    /// An item inside a function body: an index into `Ast::stmt_items`.
    Item(u32),
    /// A macro call in statement position (`m!(..);`). `semi` records whether
    /// a `;` followed a `()` or `[]` call, which changes its type to unit.
    Macro {
        call: MacroCall,
        semi: bool,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn is_cmp(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
    pub fn symbol(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            BitAnd => "&",
            BitOr => "|",
            BitXor => "^",
            Shl => "<<",
            Shr => ">>",
            Eq => "==",
            Ne => "!=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
            And => "&&",
            Or => "||",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MacroKind {
    Println,
    Print,
    Eprintln,
    Eprint,
    Format,
    Panic,
    Vec,
    Assert,
    AssertEq,
    AssertNe,
    Todo,
    Unreachable,
    /// `format_args!`: an `fmt::Arguments` value (W-STD-B, R9).
    FormatArgs,
}

/// One parsed format spec (the text after `:` in a placeholder), as
/// Rust's grammar gives it: `[[fill]align][sign][#][0][width][.prec][kind]`.
/// A width or precision from an argument (`w$`, `1$`, `.*`) is the index
/// of that `usize` argument in the macro's argument list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FmtSpec {
    pub kind: FmtKind,
    /// The fill character as a Unicode scalar value; 0 means space.
    pub fill: u32,
    /// 0 = default for the type, else '<', '>', or '^' as a byte.
    pub align: u8,
    pub plus: bool,
    /// The `-` flag: no effect on std output, but `Formatter::sign_minus`
    /// reads it (W-STD-B).
    pub minus: bool,
    pub alt: bool,
    pub zero: bool,
    /// `{:x?}` (1) and `{:X?}` (2): Debug with integers in hex (W-STD-B).
    pub debug_hex: u8,
    pub width: Option<u32>,
    pub precision: Option<u32>,
    pub width_arg: Option<u32>,
    pub precision_arg: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FmtKind {
    Display,
    Debug,
    LowerHex,
    UpperHex,
    Octal,
    Binary,
    LowerExp,
    UpperExp,
    /// `{:p}`: the address a reference or raw pointer holds.
    Pointer,
}

impl Default for FmtSpec {
    fn default() -> FmtSpec {
        FmtSpec {
            kind: FmtKind::Display,
            fill: 0,
            align: 0,
            plus: false,
            minus: false,
            alt: false,
            zero: false,
            debug_hex: 0,
            width: None,
            precision: None,
            width_arg: None,
            precision_arg: None,
        }
    }
}

/// A parsed format string. `Arg` holds an index into the macro's argument list.
#[derive(Clone, Debug)]
pub enum FmtPiece {
    Lit(String),
    Arg { index: usize, debug: bool, spec: FmtSpec },
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct Arm {
    pub attrs: Vec<Attr>,
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

/// One step of an `offset_of!` field path: a named field, or a tuple
/// field by index (`offset_of!(W, 1)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OffsetField {
    Name(Sym),
    Index(u32),
}

/// One closure parameter: a pattern and an optional written type.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub struct ClosureParam {
    pub pat: PatId,
    pub ty: Option<TyId>,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum Expr {
    Int(u128, Option<IntSuffix>),
    Bool(bool),
    Str(u32),
    Char(char),
    Unit,
    Path(Vec<PathSeg>),
    SelfValue,
    Block(BlockId),
    If {
        cond: ExprId,
        then: BlockId,
        els: Option<ExprId>,
    },
    While {
        label: Option<Label>,
        cond: ExprId,
        body: BlockId,
    },
    Loop {
        label: Option<Label>,
        body: BlockId,
    },
    For {
        label: Option<Label>,
        pat: PatId,
        iter: ExprId,
        body: BlockId,
    },
    Match {
        scrut: ExprId,
        arms: Vec<Arm>,
    },
    Call {
        callee: ExprId,
        args: Vec<ExprId>,
    },
    /// A method call. `generic_args` is the turbofish (`recv.m::<T>(..)`),
    /// with lifetime, const, and binding arguments in written order.
    MethodCall {
        recv: ExprId,
        name: Sym,
        name_span: Span,
        generic_args: Vec<GenericArg>,
        args: Vec<ExprId>,
    },
    Field {
        base: ExprId,
        name: Sym,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Binary {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Unary {
        op: UnOp,
        expr: ExprId,
    },
    Cast {
        expr: ExprId,
        ty: TyId,
    },
    /// A borrow. `raw` marks `&raw const` and `&raw mut`, where `mutable`
    /// says which of the two was written.
    Ref {
        mutable: bool,
        raw: bool,
        expr: ExprId,
    },
    Deref(ExprId),
    Assign {
        lhs: ExprId,
        rhs: ExprId,
    },
    AssignOp {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    /// A struct literal. `update` is the base in `S { a: 1, ..base }`.
    StructLit {
        path: Vec<PathSeg>,
        fields: Vec<(Sym, Span, ExprId)>,
        update: Option<ExprId>,
    },
    Range {
        lo: Option<ExprId>,
        hi: Option<ExprId>,
        inclusive: bool,
    },
    Break {
        label: Option<Label>,
        value: Option<ExprId>,
    },
    Continue(Option<Label>),
    Return(Option<ExprId>),
    Macro {
        kind: MacroKind,
        args: Vec<ExprId>,
        fmt: Vec<FmtPiece>,
        repeat: bool,
    },
    // ---- AST v2 expressions: shapes only for now; the parser rejects each form. ----
    /// A float literal: an index into the AST string table holding its text.
    Float(u32),
    /// A tuple expression with one or more elements. `()` stays `Unit`.
    Tuple(Vec<ExprId>),
    /// An array literal `[a, b, c]`.
    Array(Vec<ExprId>),
    /// An array repeat literal `[value; len]`.
    ArrayRepeat {
        value: ExprId,
        len: ExprId,
    },
    /// A closure: `move |params| -> Ret body`, with `async` when written.
    /// The body is an expression (a block body is `Expr::Block`).
    Closure {
        is_move: bool,
        is_async: bool,
        params: Vec<ClosureParam>,
        ret: Option<TyId>,
        body: ExprId,
    },
    /// The `?` operator.
    Try(ExprId),
    /// An `.await` postfix.
    Await(ExprId),
    /// An `async` block: `async move { .. }`.
    AsyncBlock {
        is_move: bool,
        body: BlockId,
    },
    /// An `unsafe { .. }` block.
    UnsafeBlock(BlockId),
    /// A labeled block: `'a: { .. }`.
    LabeledBlock {
        label: Label,
        body: BlockId,
    },
    /// A `let` in an `if` or `while` condition, including let chains joined
    /// by `&&`. Only valid as (part of) a condition.
    Let {
        pat: PatId,
        scrut: ExprId,
    },
    /// A tuple field access: `value.0`.
    TupleField {
        base: ExprId,
        index: u32,
    },
    /// A qualified path: `<SelfTy as Trait>::Segs`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// An inline const block: `const { .. }`.
    ConstBlock(BlockId),
    /// The inferred expression `_` (const generic arguments and the like).
    Underscore,
    /// A user macro call in expression position, as raw token trees.
    MacroCall(MacroCall),
    /// An `offset_of!` query: a type and a field path (W-CORELANG, wave A).
    OffsetOf {
        ty: TyId,
        fields: Vec<OffsetField>,
    },
    /// A byte string literal's array value (`[u8; N]`): an index into
    /// the AST blob table. The parser wraps it in `Ref`, which is the
    /// literal's Rust type (`&[u8; N]`).
    ByteStr(u32),
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum Pat {
    Wild,
    Binding {
        name: Sym,
        mutable: bool,
        by_ref: bool,
    },
    Lit(ExprId),
    /// A path pattern: a unit variant such as `Kind::C`.
    Path(Vec<PathSeg>),
    TupleStruct {
        path: Vec<PathSeg>,
        elems: Vec<PatId>,
    },
    Struct {
        path: Vec<PathSeg>,
        fields: Vec<(Sym, PatId)>,
        rest: bool,
    },
    Or(Vec<PatId>),
    /// A range pattern. `lo` is None for `..hi` and `..=hi`; `hi` is None
    /// for `lo..`; `inclusive` marks `..=`.
    Range {
        lo: Option<ExprId>,
        hi: Option<ExprId>,
        inclusive: bool,
    },
    // ---- AST v2 patterns: shapes only for now; the parser rejects each form. ----
    /// A tuple pattern: `(a, b, ..)`. A `..` element is `Pat::Rest`.
    Tuple(Vec<PatId>),
    /// A slice pattern: `[first, rest @ .., last]`. `middle`, when present,
    /// is the pattern bound to the middle slice (a binding or `_`).
    Slice {
        prefix: Vec<PatId>,
        middle: Option<PatId>,
        suffix: Vec<PatId>,
    },
    /// A reference pattern: `&pat` or `&mut pat`.
    Ref {
        mutable: bool,
        inner: PatId,
    },
    /// An `@` binding: `name @ pat`, with `ref` and `mut` as written.
    At {
        name: Sym,
        mutable: bool,
        by_ref: bool,
        inner: PatId,
    },
    /// A rest pattern `..` inside a tuple, tuple-struct, or slice pattern.
    Rest,
    /// A parenthesized pattern `(pat)`.
    Paren(PatId),
    /// A qualified path pattern: `<SelfTy as Trait>::CONST`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// A macro call in pattern position, as raw token trees.
    MacroCall(MacroCall),
}

/// Index offsets for merging one chunk's arenas after another's. They add
/// with wraparound, so a negated offset takes a chunk back out of a merged
/// Ast (`Ast::chunk_at`).
#[derive(Clone, Copy)]
struct Shift {
    e: u32,
    p: u32,
    t: u32,
    b: u32,
    s: u32,
    /// Offset of this chunk's byte blobs in the merged `blobs`.
    bl: u32,
    /// Offset of this chunk's body items in the merged `stmt_items`.
    si: u32,
}

impl Shift {
    fn e(&self, x: ExprId) -> ExprId {
        ExprId(x.0.wrapping_add(self.e))
    }
    fn p(&self, x: PatId) -> PatId {
        PatId(x.0.wrapping_add(self.p))
    }
    fn t(&self, x: TyId) -> TyId {
        TyId(x.0.wrapping_add(self.t))
    }
    fn b(&self, x: BlockId) -> BlockId {
        BlockId(x.0.wrapping_add(self.b))
    }
    fn es(&self, xs: &mut [ExprId]) {
        xs.iter_mut().for_each(|x| *x = self.e(*x));
    }
    fn ts(&self, xs: &mut [TyId]) {
        xs.iter_mut().for_each(|x| *x = self.t(*x));
    }
    fn ps(&self, xs: &mut [PatId]) {
        xs.iter_mut().for_each(|x| *x = self.p(*x));
    }
    fn str_id(&self, x: &mut u32) {
        *x = x.wrapping_add(self.s);
    }
    fn trees(&self, trees: &mut [TokenTree]) {
        for tree in trees {
            match tree {
                TokenTree::Token(tok) => tok.tok.shift_strings(self.s),
                TokenTree::Delim(_, inner, _) => self.trees(inner),
            }
        }
    }
    fn generic_arg(&self, a: &mut GenericArg) {
        match a {
            GenericArg::Type(t) => *t = self.t(*t),
            GenericArg::Lifetime(_) => {}
            GenericArg::Const(e) => *e = self.e(*e),
            GenericArg::Binding { kind, .. } => match kind {
                BindingKind::EqTy(t) => *t = self.t(*t),
                BindingKind::EqConst(e) => *e = self.e(*e),
                BindingKind::Constraint(bounds) => self.bounds(bounds),
            },
        }
    }
    fn args(&self, args: &mut GenericArgs) {
        match args {
            GenericArgs::None => {}
            GenericArgs::Angle(args) => {
                for a in args {
                    self.generic_arg(a);
                }
            }
            GenericArgs::Parenthesized { inputs, output } => {
                self.ts(inputs);
                *output = output.map(|t| self.t(t));
            }
        }
    }
    fn path(&self, segs: &mut [PathSeg]) {
        segs.iter_mut().for_each(|s| self.args(&mut s.args));
    }
    fn vis(&self, v: &mut Vis) {
        if let Vis::Restricted { path, .. } = v {
            self.path(path);
        }
    }
    fn attrs(&self, attrs: &mut [Attr]) {
        for a in attrs {
            self.path(&mut a.path);
            match &mut a.input {
                AttrInput::None => {}
                AttrInput::Eq(e) => *e = self.e(*e),
                AttrInput::List(_, trees) => self.trees(trees),
            }
        }
    }
    fn bounds(&self, bounds: &mut [TraitBound]) {
        for b in bounds {
            if let TraitBound::Trait { trait_ref, .. } = b {
                self.path(&mut trait_ref.path);
            }
        }
    }
    fn generics(&self, g: &mut Generics) {
        for p in &mut g.params {
            match p {
                GenericParam::Lifetime { attrs, .. } => self.attrs(attrs),
                GenericParam::Type { bounds, default, attrs, .. } => {
                    self.bounds(bounds);
                    *default = default.map(|t| self.t(t));
                    self.attrs(attrs);
                }
                GenericParam::Const { ty, default, attrs, .. } => {
                    *ty = self.t(*ty);
                    *default = default.map(|e| self.e(e));
                    self.attrs(attrs);
                }
            }
        }
    }
    fn where_clause(&self, w: &mut WhereClause) {
        for p in &mut w.preds {
            match p {
                WherePred::Type { ty, bounds, .. } => {
                    *ty = self.t(*ty);
                    self.bounds(bounds);
                }
                WherePred::Lifetime { .. } => {}
            }
        }
    }
    fn macro_call(&self, m: &mut MacroCall) {
        self.path(&mut m.path);
        self.trees(&mut m.tokens);
    }
    fn use_tree(&self, t: &mut UseTree) {
        self.path(&mut t.prefix);
        if let UseKind::Group(trees) = &mut t.kind {
            trees.iter_mut().for_each(|c| self.use_tree(c));
        }
    }
    fn assoc_consts(&self, cs: &mut [AssocConstDef]) {
        for c in cs {
            self.vis(&mut c.vis);
            self.attrs(&mut c.attrs);
            c.ty = self.t(c.ty);
            c.default = c.default.map(|e| self.e(e));
            if let Some(f) = &mut c.init_fn {
                self.fn_def(f);
            }
        }
    }
    fn assoc_types(&self, ts: &mut [AssocTypeDef]) {
        for t in ts {
            self.vis(&mut t.vis);
            self.attrs(&mut t.attrs);
            self.generics(&mut t.generics);
            self.bounds(&mut t.bounds);
            self.where_clause(&mut t.where_clause);
            t.default = t.default.map(|x| self.t(x));
        }
    }
    fn fn_def(&self, f: &mut FnDef) {
        self.vis(&mut f.vis);
        self.attrs(&mut f.attrs);
        if let Some(a) = &mut f.qual.abi {
            self.str_id(a);
        }
        self.generics(&mut f.generics);
        if let Some(sp) = &mut f.self_param {
            sp.ty = sp.ty.map(|t| self.t(t));
            self.attrs(&mut sp.attrs);
        }
        f.params.iter_mut().for_each(|p| {
            p.ty = self.t(p.ty);
            p.pat = p.pat.map(|x| self.p(x));
            self.attrs(&mut p.attrs);
        });
        f.ret = f.ret.map(|t| self.t(t));
        self.where_clause(&mut f.where_clause);
        f.body = f.body.map(|b| self.b(b));
        f.exprs = (f.exprs.0.wrapping_add(self.e), f.exprs.1.wrapping_add(self.e));
        f.pats = (f.pats.0.wrapping_add(self.p), f.pats.1.wrapping_add(self.p));
    }
    fn fields(&self, fs: &mut [FieldDef]) {
        fs.iter_mut().for_each(|f| {
            f.ty = self.t(f.ty);
            self.vis(&mut f.vis);
            self.attrs(&mut f.attrs);
        });
    }
    fn variant_fields(&self, vf: &mut VariantFields) {
        match vf {
            VariantFields::Unit => {}
            VariantFields::Tuple(fs) | VariantFields::Struct(fs) => self.fields(fs),
        }
    }
    fn item(&self, item: &mut Item) {
        self.vis(&mut item.vis);
        self.attrs(&mut item.attrs);
        match &mut item.kind {
            ItemKind::Fn(f) => self.fn_def(f),
            ItemKind::Struct(s) => {
                self.generics(&mut s.generics);
                self.variant_fields(&mut s.fields);
                self.where_clause(&mut s.where_clause);
            }
            ItemKind::Enum(e) => {
                self.generics(&mut e.generics);
                self.where_clause(&mut e.where_clause);
                for v in &mut e.variants {
                    self.attrs(&mut v.attrs);
                    self.variant_fields(&mut v.fields);
                    v.discriminant = v.discriminant.map(|x| self.e(x));
                }
            }
            ItemKind::Impl(imp) => {
                self.attrs(&mut imp.inner_attrs);
                self.generics(&mut imp.generics);
                if let Some(tr) = &mut imp.trait_ref {
                    self.path(&mut tr.path);
                }
                imp.self_ty = self.t(imp.self_ty);
                self.where_clause(&mut imp.where_clause);
                imp.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut imp.consts);
                self.assoc_types(&mut imp.types);
            }
            ItemKind::Use(u) => self.use_tree(&mut u.tree),
            ItemKind::Mod(m) => {
                self.attrs(&mut m.inner_attrs);
                if let Some(items) = &mut m.body {
                    items.iter_mut().for_each(|i| self.item(i));
                }
            }
            ItemKind::Trait(tr) => {
                self.attrs(&mut tr.inner_attrs);
                self.generics(&mut tr.generics);
                self.bounds(&mut tr.bounds);
                self.where_clause(&mut tr.where_clause);
                tr.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut tr.consts);
                self.assoc_types(&mut tr.types);
            }
            ItemKind::Type(a) => {
                self.generics(&mut a.generics);
                self.where_clause(&mut a.where_clause);
                a.ty = self.t(a.ty);
            }
            ItemKind::Const(c) => {
                c.ty = self.t(c.ty);
                c.value = c.value.map(|e| self.e(e));
                if let Some(f) = &mut c.init_fn {
                    self.fn_def(f);
                }
            }
            ItemKind::Static(s) => {
                s.ty = self.t(s.ty);
                s.value = s.value.map(|e| self.e(e));
                if let Some(f) = &mut s.init_fn {
                    self.fn_def(f);
                }
            }
            ItemKind::MacroRules(m) => self.trees(&mut m.tokens),
            ItemKind::ExternCrate(_) => {}
            ItemKind::ExternBlock(b) => {
                if let Some(a) = &mut b.abi {
                    self.str_id(a);
                }
                for fi in &mut b.items {
                    match fi {
                        ForeignItem::Fn(f) => self.fn_def(f),
                        ForeignItem::Static(s) => {
                            s.ty = self.t(s.ty);
                            s.value = s.value.map(|e| self.e(e));
                        }
                        ForeignItem::Type { vis, attrs, generics, where_clause, .. } => {
                            self.vis(vis);
                            self.attrs(attrs);
                            self.generics(generics);
                            self.where_clause(where_clause);
                        }
                        ForeignItem::MacroCall(m) => self.macro_call(m),
                    }
                }
            }
            ItemKind::Union(u) => {
                self.generics(&mut u.generics);
                self.fields(&mut u.fields);
                self.where_clause(&mut u.where_clause);
            }
            ItemKind::MacroCall(m) => self.macro_call(m),
        }
    }
}

/// Where one chunk sits in a merged Ast (`Ast::concat_parts`): the start and
/// length of its part of each list. The resolve's cache keeps this instead of
/// a copy of the chunk, and the next merge copies the chunk from there
/// (`ChunkPart::Old`).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ChunkSpan {
    exprs: (u32, u32),
    pats: (u32, u32),
    tys: (u32, u32),
    blocks: (u32, u32),
    strings: (u32, u32),
    blobs: (u32, u32),
    stmt_items: (u32, u32),
    items: (u32, u32),
    inner_attrs: (u32, u32),
    use_traits: (u32, u32),
    paren_exprs: (u32, u32),
    paren_tys: (u32, u32),
    anon_consts: (u32, u32),
}

impl ChunkSpan {
    /// The place right after `self` of a chunk of lengths `lens` (its `.1`s).
    fn after(&self, lens: &ChunkSpan) -> ChunkSpan {
        let next = |a: (u32, u32), l: (u32, u32)| (a.0 + a.1, l.1);
        ChunkSpan {
            exprs: next(self.exprs, lens.exprs),
            pats: next(self.pats, lens.pats),
            tys: next(self.tys, lens.tys),
            blocks: next(self.blocks, lens.blocks),
            strings: next(self.strings, lens.strings),
            blobs: next(self.blobs, lens.blobs),
            stmt_items: next(self.stmt_items, lens.stmt_items),
            items: next(self.items, lens.items),
            inner_attrs: next(self.inner_attrs, lens.inner_attrs),
            use_traits: next(self.use_traits, lens.use_traits),
            paren_exprs: next(self.paren_exprs, lens.paren_exprs),
            paren_tys: next(self.paren_tys, lens.paren_tys),
            anon_consts: next(self.anon_consts, lens.anon_consts),
        }
    }
}

impl Shift {
    /// The shift that moves a chunk's indexes from place `from` to place `to`.
    fn between(from: &ChunkSpan, to: &ChunkSpan) -> Shift {
        let d = |f: (u32, u32), t: (u32, u32)| t.0.wrapping_sub(f.0);
        Shift {
            e: d(from.exprs, to.exprs),
            p: d(from.pats, to.pats),
            t: d(from.tys, to.tys),
            b: d(from.blocks, to.blocks),
            s: d(from.strings, to.strings),
            bl: d(from.blobs, to.blobs),
            si: d(from.stmt_items, to.stmt_items),
        }
    }
}

/// One chunk for `Ast::concat_parts`: an Ast of its own, or the chunk at a place in an older
/// merged Ast.
pub enum ChunkPart {
    Own(Ast),
    Old(ChunkSpan),
}

impl Ast {
    /// Merges chunk ASTs in order. Index shifting runs in parallel, one chunk per task.
    pub fn concat(chunks: Vec<Ast>) -> Ast {
        Ast::concat_spans(chunks).0
    }

    /// `concat`, with where each chunk sits in the merged Ast.
    pub fn concat_spans(chunks: Vec<Ast>) -> (Ast, Vec<ChunkSpan>) {
        Ast::concat_parts(chunks.into_iter().map(ChunkPart::Own).collect(), None)
    }

    /// `concat_spans` of chunks that are Asts of their own or parts of the
    /// merged Ast `old` (`ChunkPart::Old`): an old part is copied from there
    /// straight to its new place, its indexes shifted once.
    pub fn concat_parts(parts: Vec<ChunkPart>, old: Option<&Ast>) -> (Ast, Vec<ChunkSpan>) {
        let mut spans = Vec::with_capacity(parts.len());
        let mut at = ChunkSpan::default();
        for p in &parts {
            at = at.after(&match p {
                ChunkPart::Own(c) => c.lens(),
                ChunkPart::Old(from) => *from,
            });
            spans.push(at);
        }
        // Each part takes its place on the compiler's thread pool: an own chunk shifts by its
        // place, an old one is copied out of `old` with its shift from the old place to the
        // new. A part sits behind its own lock, taken once, so one task can own it.
        let cells: Vec<std::sync::Mutex<Option<ChunkPart>>> = parts.into_iter().map(|p| std::sync::Mutex::new(Some(p))).collect();
        let order: Vec<usize> = (0..cells.len()).collect();
        let mut chunks: Vec<Ast> = crate::pool::par_map(&order, |&i| match cells[i].lock().unwrap().take() {
            Some(ChunkPart::Own(mut c)) => {
                if i > 0 {
                    c.shift(Shift::between(&ChunkSpan::default(), &spans[i]));
                }
                c
            }
            Some(ChunkPart::Old(from)) => old.expect("an old chunk part needs the old merged Ast").moved_chunk(&from, &spans[i]),
            None => Ast::default(),
        });
        // The merged sizes: the end of the last place.
        let end = |a: (u32, u32)| a.0 + a.1;
        let sh = Shift { e: end(at.exprs), p: end(at.pats), t: end(at.tys), b: end(at.blocks), s: end(at.strings), bl: end(at.blobs), si: end(at.stmt_items) };
        // Room past the merged size: the daemon's body and item patches
        // append nodes, and an exact fit copied every arena on the first
        // patch after each full resolve (sigedit P1.2). Untouched
        // capacity costs no memory.
        let room = |n: u32| n as usize + n as usize / 16 + 1024;
        let mut out = Ast {
            inner_attrs: Vec::new(),
            items: Vec::with_capacity(chunks.iter().map(|c| c.items.len()).sum()),
            stmt_items: Vec::with_capacity(room(sh.si)),
            exprs: Vec::with_capacity(room(sh.e)),
            expr_spans: Vec::with_capacity(room(sh.e)),
            pats: Vec::with_capacity(room(sh.p)),
            pat_spans: Vec::with_capacity(room(sh.p)),
            tys: Vec::with_capacity(room(sh.t)),
            ty_spans: Vec::with_capacity(room(sh.t)),
            blocks: Vec::with_capacity(room(sh.b)),
            strings: Vec::with_capacity(room(sh.s)),
            blobs: Vec::with_capacity(sh.bl as usize),
            shipped: Vec::new(),
            lang_methods: (0, 0),
            use_traits: Vec::new(),
            paren_exprs: Vec::new(),
            paren_tys: Vec::new(),
            anon_consts: Vec::new(),
        };
        fn cat<T>(parts: Vec<Vec<T>>, mut out: Vec<T>) -> Vec<T> {
            for mut p in parts {
                out.append(&mut p);
            }
            out
        }
        // The expression, pattern and type arenas move out of the chunks first. A large Ast
        // (a tsgo resolve: 1.2M exprs, 60+ ms on one thread, much of it the first-touch
        // faults of the merged arenas) moves them on three scoped threads (exprs, their
        // spans, patterns and types) while this thread moves the rest.
        let wide = sh.e > 1 << 18;
        let n = chunks.len();
        let (mut exprs, mut expr_spans, mut pats_tys) = (Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n));
        for c in &mut chunks {
            exprs.push(std::mem::take(&mut c.exprs));
            expr_spans.push(std::mem::take(&mut c.expr_spans));
            pats_tys.push((std::mem::take(&mut c.pats), std::mem::take(&mut c.pat_spans), std::mem::take(&mut c.tys), std::mem::take(&mut c.ty_spans)));
        }
        let (e_out, es_out) = (std::mem::take(&mut out.exprs), std::mem::take(&mut out.expr_spans));
        let mut pt_out = (std::mem::take(&mut out.pats), std::mem::take(&mut out.pat_spans), std::mem::take(&mut out.tys), std::mem::take(&mut out.ty_spans));
        let pats_tys_into = move || {
            for (mut p, mut ps, mut t, mut ts) in pats_tys {
                pt_out.0.append(&mut p);
                pt_out.1.append(&mut ps);
                pt_out.2.append(&mut t);
                pt_out.3.append(&mut ts);
            }
            pt_out
        };
        let rest = |out: &mut Ast| {
            for mut c in chunks {
                out.inner_attrs.append(&mut c.inner_attrs);
                out.items.append(&mut c.items);
                out.stmt_items.append(&mut c.stmt_items);
                out.blocks.append(&mut c.blocks);
                out.strings.append(&mut c.strings);
                out.blobs.append(&mut c.blobs);
                out.use_traits.append(&mut c.use_traits);
                out.paren_exprs.append(&mut c.paren_exprs);
                out.paren_tys.append(&mut c.paren_tys);
                out.anon_consts.append(&mut c.anon_consts);
            }
        };
        let (e, es, pt) = if wide {
            std::thread::scope(|s| {
                let e = s.spawn(move || cat(exprs, e_out));
                let es = s.spawn(move || cat(expr_spans, es_out));
                let pt = s.spawn(pats_tys_into);
                rest(&mut out);
                let e = e.join().unwrap_or_else(|p| std::panic::resume_unwind(p));
                let es = es.join().unwrap_or_else(|p| std::panic::resume_unwind(p));
                (e, es, pt.join().unwrap_or_else(|p| std::panic::resume_unwind(p)))
            })
        } else {
            rest(&mut out);
            (cat(exprs, e_out), cat(expr_spans, es_out), pats_tys_into())
        };
        (out.exprs, out.expr_spans) = (e, es);
        (out.pats, out.pat_spans, out.tys, out.ty_spans) = pt;
        (out, spans)
    }

    /// The lengths of this Ast's lists, as a chunk at place 0 (`ChunkSpan`).
    fn lens(&self) -> ChunkSpan {
        let n = |l: usize| (0, l as u32);
        ChunkSpan {
            exprs: n(self.exprs.len()),
            pats: n(self.pats.len()),
            tys: n(self.tys.len()),
            blocks: n(self.blocks.len()),
            strings: n(self.strings.len()),
            blobs: n(self.blobs.len()),
            stmt_items: n(self.stmt_items.len()),
            items: n(self.items.len()),
            inner_attrs: n(self.inner_attrs.len()),
            use_traits: n(self.use_traits.len()),
            paren_exprs: n(self.paren_exprs.len()),
            paren_tys: n(self.paren_tys.len()),
            anon_consts: n(self.anon_consts.len()),
        }
    }

    /// A copy of the chunk at place `at` (`concat_parts`), its indexes shifted as for place
    /// `to` (place 0: the chunk as it was before the merge). Only a chunk's own lists come
    /// (`concat` keeps no chunk's `shipped` or `lang_methods`).
    fn moved_chunk(&self, at: &ChunkSpan, to: &ChunkSpan) -> Ast {
        fn part<T: Clone>(xs: &[T], at: (u32, u32)) -> Vec<T> {
            xs[at.0 as usize..(at.0 + at.1) as usize].to_vec()
        }
        let mut c = Ast {
            inner_attrs: part(&self.inner_attrs, at.inner_attrs),
            items: part(&self.items, at.items),
            stmt_items: part(&self.stmt_items, at.stmt_items),
            exprs: part(&self.exprs, at.exprs),
            expr_spans: part(&self.expr_spans, at.exprs),
            pats: part(&self.pats, at.pats),
            pat_spans: part(&self.pat_spans, at.pats),
            tys: part(&self.tys, at.tys),
            ty_spans: part(&self.ty_spans, at.tys),
            blocks: part(&self.blocks, at.blocks),
            strings: part(&self.strings, at.strings),
            blobs: part(&self.blobs, at.blobs),
            shipped: Vec::new(),
            lang_methods: (0, 0),
            use_traits: part(&self.use_traits, at.use_traits),
            paren_exprs: part(&self.paren_exprs, at.paren_exprs),
            paren_tys: part(&self.paren_tys, at.paren_tys),
            anon_consts: part(&self.anon_consts, at.anon_consts),
        };
        c.shift(Shift::between(at, to));
        c
    }

    /// True for an anonymous const value with no body of its own: a
    /// literal or a one-segment path, braced or not (the scalar checks
    /// cover it).
    pub fn is_plain_const(&self, e: ExprId) -> bool {
        match self.expr(e) {
            Expr::Int(..) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) => true,
            Expr::Path(segs) => segs.len() == 1 && matches!(segs[0].args, GenericArgs::None),
            // `{ N }` names a const param as `N` does (rustc).
            Expr::Block(b) => {
                let b = self.block(*b);
                b.stmts.is_empty() && b.tail.is_some_and(|t| matches!(self.expr(t), Expr::Path(segs) if segs.len() == 1))
            }
            _ => false,
        }
    }

    /// The `anon_consts` index of the anonymous const whose value is `e`.
    pub fn anon_const(&self, e: ExprId) -> Option<u32> {
        self.anon_consts.binary_search_by_key(&e.0, |a| a.value.0).ok().map(|i| i as u32)
    }

    /// Moves another chunk's arena nodes into this AST (shifting their indexes) and returns
    /// its per-chunk lists (items, body items, inner attrs) for the caller to place. Arena
    /// nodes are only ever appended, so existing items stay valid; the returned lists are
    /// not merged here, because a caller that re-parses one chunk must replace that chunk's
    /// lists, not append to them (collect enumerates `stmt_items` and `inner_attrs`, so a
    /// stale copy would stay live). `stmt_base` is where the caller will place the returned
    /// body items in the merged `stmt_items`: `Stmt::Item` indexes in the chunk's blocks
    /// are shifted to that base.
    pub fn append_chunk(&mut self, mut o: Ast, stmt_base: u32) -> (Vec<Item>, Vec<Item>, Vec<Attr>) {
        let sh = Shift {
            e: self.exprs.len() as u32,
            p: self.pats.len() as u32,
            t: self.tys.len() as u32,
            b: self.blocks.len() as u32,
            s: self.strings.len() as u32,
            bl: self.blobs.len() as u32,
            si: stmt_base,
        };
        o.shift(sh);
        self.exprs.append(&mut o.exprs);
        self.expr_spans.append(&mut o.expr_spans);
        self.pats.append(&mut o.pats);
        self.pat_spans.append(&mut o.pat_spans);
        self.tys.append(&mut o.tys);
        self.ty_spans.append(&mut o.ty_spans);
        self.blocks.append(&mut o.blocks);
        self.strings.append(&mut o.strings);
        self.blobs.append(&mut o.blobs);
        self.use_traits.append(&mut o.use_traits);
        self.paren_exprs.append(&mut o.paren_exprs);
        self.paren_tys.append(&mut o.paren_tys);
        self.anon_consts.append(&mut o.anon_consts);
        (o.items, o.stmt_items, o.inner_attrs)
    }

    /// Adds `sh` to every index stored in this chunk's nodes.
    fn shift(&mut self, sh: Shift) {
        let o = self;
        for id in &mut o.paren_exprs {
            *id = id.wrapping_add(sh.e);
        }
        for id in &mut o.paren_tys {
            *id = id.wrapping_add(sh.t);
        }
        for a in &mut o.anon_consts {
            a.value = sh.e(a.value);
            sh.fn_def(&mut a.def);
        }
        sh.attrs(&mut o.inner_attrs);
        for item in o.items.iter_mut().chain(o.stmt_items.iter_mut()) {
            sh.item(item);
        }
        for e in &mut o.exprs {
            match e {
                Expr::Int(..) | Expr::Bool(_) | Expr::Char(_) | Expr::Unit | Expr::SelfValue | Expr::Continue(_) | Expr::Underscore => {}
                Expr::Str(i) | Expr::Float(i) => *i = i.wrapping_add(sh.s),
                Expr::ByteStr(i) => *i = i.wrapping_add(sh.bl),
                Expr::Path(segs) => sh.path(segs),
                Expr::Block(b)
                | Expr::Loop { body: b, .. }
                | Expr::UnsafeBlock(b)
                | Expr::LabeledBlock { body: b, .. }
                | Expr::AsyncBlock { body: b, .. }
                | Expr::ConstBlock(b) => *b = sh.b(*b),
                Expr::If { cond, then, els } => {
                    *cond = sh.e(*cond);
                    *then = sh.b(*then);
                    *els = els.map(|x| sh.e(x));
                }
                Expr::While { cond, body, .. } => {
                    *cond = sh.e(*cond);
                    *body = sh.b(*body);
                }
                Expr::For { pat, iter, body, .. } => {
                    *pat = sh.p(*pat);
                    *iter = sh.e(*iter);
                    *body = sh.b(*body);
                }
                Expr::Match { scrut, arms } => {
                    *scrut = sh.e(*scrut);
                    for a in arms {
                        sh.attrs(&mut a.attrs);
                        a.pat = sh.p(a.pat);
                        a.guard = a.guard.map(|g| sh.e(g));
                        a.body = sh.e(a.body);
                    }
                }
                Expr::Call { callee, args } => {
                    *callee = sh.e(*callee);
                    sh.es(args);
                }
                Expr::MethodCall { recv, generic_args, args, .. } => {
                    *recv = sh.e(*recv);
                    generic_args.iter_mut().for_each(|a| sh.generic_arg(a));
                    sh.es(args);
                }
                Expr::Field { base, .. } | Expr::TupleField { base, .. } => *base = sh.e(*base),
                Expr::Index { base, index } => {
                    *base = sh.e(*base);
                    *index = sh.e(*index);
                }
                Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
                    *lhs = sh.e(*lhs);
                    *rhs = sh.e(*rhs);
                }
                Expr::Unary { expr, .. } | Expr::Ref { expr, .. } | Expr::Deref(expr) | Expr::Try(expr) | Expr::Await(expr) => {
                    *expr = sh.e(*expr)
                }
                Expr::Cast { expr, ty } => {
                    *expr = sh.e(*expr);
                    *ty = sh.t(*ty);
                }
                Expr::StructLit { path, fields, update } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.2 = sh.e(f.2));
                    *update = update.map(|x| sh.e(x));
                }
                Expr::Range { lo, hi, .. } => {
                    *lo = lo.map(|x| sh.e(x));
                    *hi = hi.map(|x| sh.e(x));
                }
                Expr::Break { value, .. } => *value = value.map(|x| sh.e(x)),
                Expr::Return(v) => *v = v.map(|x| sh.e(x)),
                Expr::Macro { args, .. } => sh.es(args),
                Expr::Tuple(elems) | Expr::Array(elems) => sh.es(elems),
                Expr::ArrayRepeat { value, len } => {
                    *value = sh.e(*value);
                    *len = sh.e(*len);
                }
                Expr::Closure { params, ret, body, .. } => {
                    for p in params {
                        p.pat = sh.p(p.pat);
                        p.ty = p.ty.map(|t| sh.t(t));
                        sh.attrs(&mut p.attrs);
                    }
                    *ret = ret.map(|t| sh.t(t));
                    *body = sh.e(*body);
                }
                Expr::Let { pat, scrut } => {
                    *pat = sh.p(*pat);
                    *scrut = sh.e(*scrut);
                }
                Expr::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                Expr::MacroCall(m) => sh.macro_call(m),
                Expr::OffsetOf { ty, .. } => *ty = sh.t(*ty),
            }
        }
        for p in &mut o.pats {
            match p {
                Pat::Wild | Pat::Binding { .. } | Pat::Rest => {}
                Pat::Lit(e) => *e = sh.e(*e),
                Pat::Range { lo, hi, .. } => {
                    *lo = lo.map(|x| sh.e(x));
                    *hi = hi.map(|x| sh.e(x));
                }
                Pat::Path(segs) => sh.path(segs),
                Pat::TupleStruct { path, elems } => {
                    sh.path(path);
                    sh.ps(elems);
                }
                Pat::Struct { path, fields, .. } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.1 = sh.p(f.1));
                }
                Pat::Or(alts) | Pat::Tuple(alts) => sh.ps(alts),
                Pat::Slice { prefix, middle, suffix } => {
                    sh.ps(prefix);
                    *middle = middle.map(|x| sh.p(x));
                    sh.ps(suffix);
                }
                Pat::Ref { inner, .. } | Pat::Paren(inner) => *inner = sh.p(*inner),
                Pat::At { inner, .. } => *inner = sh.p(*inner),
                Pat::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                Pat::MacroCall(m) => sh.macro_call(m),
            }
        }
        for t in &mut o.tys {
            match t {
                TyExpr::Path(segs) => sh.path(segs),
                TyExpr::Ref { inner, .. } | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } | TyExpr::Paren(inner) => {
                    *inner = sh.t(*inner)
                }
                TyExpr::Unit | TyExpr::Never | TyExpr::Infer => {}
                TyExpr::Tuple(ts) => sh.ts(ts),
                TyExpr::Array { inner, len } => {
                    *inner = sh.t(*inner);
                    *len = sh.e(*len);
                }
                TyExpr::FnPtr { qual, inputs, ret, .. } => {
                    if let Some(a) = &mut qual.abi {
                        sh.str_id(a);
                    }
                    for p in inputs {
                        p.ty = sh.t(p.ty);
                        sh.attrs(&mut p.attrs);
                    }
                    *ret = ret.map(|x| sh.t(x));
                }
                TyExpr::Dyn { bounds, .. } => sh.bounds(bounds),
                TyExpr::ImplTrait { bounds, .. } => sh.bounds(bounds),
                TyExpr::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                TyExpr::MacroCall(m) => sh.macro_call(m),
            }
        }
        for b in &mut o.blocks {
            sh.attrs(&mut b.inner_attrs);
            sh.attrs(&mut b.tail_attrs);
            b.tail = b.tail.map(|x| sh.e(x));
            for st in &mut b.stmts {
                match st {
                    Stmt::Let { pat, ty, init, els, attrs, .. } => {
                        *pat = sh.p(*pat);
                        *ty = ty.map(|t| sh.t(t));
                        *init = init.map(|x| sh.e(x));
                        *els = els.map(|x| sh.b(x));
                        sh.attrs(attrs);
                    }
                    Stmt::Expr { expr, attrs, .. } => {
                        *expr = sh.e(*expr);
                        sh.attrs(attrs);
                    }
                    Stmt::Item(i) => *i = i.wrapping_add(sh.si),
                    Stmt::Macro { call, .. } => sh.macro_call(call),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Merging two chunks shifts indexes inside AST v2 nodes the parser does
    /// not build yet (tuple types, closures, qualified paths, generic args),
    /// not only inside the nodes of the current subset.
    #[test]
    fn concat_shifts_v2_nodes() {
        let span = Span::default();
        let mut a = Ast::default();
        a.tys.push(TyExpr::Unit);
        a.ty_spans.push(span);
        a.exprs.push(Expr::Unit);
        a.expr_spans.push(span);
        a.strings.push("a".into());

        let mut b = Ast::default();
        // b-local ids: ty 0 = path type, ty 1 = tuple of it; expr 0 = tuple of unit.
        b.tys.push(TyExpr::Path(vec![PathSeg {
            name: Sym(7),
            args: GenericArgs::Angle(vec![
                GenericArg::Type(TyId(1)),
                GenericArg::Const(ExprId(0)),
                GenericArg::Binding { name: Sym(8), span, kind: BindingKind::EqTy(TyId(1)) },
            ]),
        }]));
        b.tys.push(TyExpr::Tuple(vec![TyId(0)]));
        b.ty_spans = vec![span, span];
        b.exprs.push(Expr::Tuple(vec![ExprId(0)]));
        b.exprs.push(Expr::Closure { is_move: true, is_async: false, params: Vec::new(), ret: Some(TyId(1)), body: ExprId(0) });
        b.expr_spans = vec![span, span];
        b.strings.push("b".into());

        let (a_copy, b_copy) = (a.clone(), b.clone());
        let out = Ast::concat(vec![a, b]);
        // After chunk a (1 ty, 1 expr), b's ty 1 is out ty 2 and expr 0 is out expr 1.
        match &out.tys[1] {
            TyExpr::Path(segs) => match &segs[0].args {
                GenericArgs::Angle(args) => {
                    assert!(matches!(args[0], GenericArg::Type(TyId(2))));
                    assert!(matches!(args[1], GenericArg::Const(ExprId(1))));
                    assert!(matches!(&args[2], GenericArg::Binding { kind: BindingKind::EqTy(TyId(2)), .. }));
                }
                other => panic!("want angle args, got {other:?}"),
            },
            _ => panic!("want path type"),
        }
        assert!(matches!(&out.tys[2], TyExpr::Tuple(ts) if ts == &vec![TyId(1)]));
        assert!(matches!(&out.exprs[1], Expr::Tuple(es) if es == &vec![ExprId(1)]));
        assert!(matches!(&out.exprs[2], Expr::Closure { ret: Some(TyId(2)), body: ExprId(1), .. }));
        // Each chunk comes back out of the merged Ast as it went in, its indexes
        // shifted back, and a merge of old parts in another order equals a merge
        // of the chunks in that order.
        let (merged, spans) = Ast::concat_spans(vec![a_copy.clone(), b_copy.clone()]);
        for (chunk, at) in [&a_copy, &b_copy].into_iter().zip(&spans) {
            assert_eq!(format!("{:?}", merged.moved_chunk(at, &ChunkSpan::default())), format!("{chunk:?}"));
        }
        let parts = vec![ChunkPart::Old(spans[1]), ChunkPart::Own(a_copy.clone())];
        let (again, _) = Ast::concat_parts(parts, Some(&merged));
        assert_eq!(format!("{:?}", again), format!("{:?}", Ast::concat(vec![b_copy, a_copy])));
    }

    /// `append_chunk` merges only the id arenas: the chunk's items, body
    /// items, and inner attrs come back for the caller to place, and the
    /// lists already in the base Ast stay as they are. A caller that
    /// re-parses one chunk can then replace that chunk's lists instead
    /// of appending a second copy next to the stale one.
    #[test]
    fn append_chunk_returns_per_chunk_lists() {
        let span = Span::default();
        let item = |name: u32| Item {
            vis: Vis::Private,
            attrs: Vec::new(),
            kind: ItemKind::ExternCrate(ExternCrateDef { name: Sym(name), name_span: span, rename: None, span }),
            span,
        };
        let mut base = Ast::default();
        base.stmt_items.push(item(1));
        base.blocks.push(Block { inner_attrs: Vec::new(), stmts: vec![Stmt::Item(0)], tail: None, tail_attrs: Vec::new(), span });

        let mut chunk = Ast::default();
        chunk.items.push(item(2));
        chunk.stmt_items.push(item(3));
        chunk.stmt_items.push(item(4));
        chunk.blocks.push(Block {
            inner_attrs: Vec::new(),
            stmts: vec![Stmt::Item(0), Stmt::Item(1)],
            tail: None,
            tail_attrs: Vec::new(),
            span,
        });

        let (items, stmt_items, inner_attrs) = base.append_chunk(chunk, 5);
        assert_eq!(items.len(), 1);
        assert_eq!(stmt_items.len(), 2);
        assert!(inner_attrs.is_empty());
        assert_eq!(base.stmt_items.len(), 1, "base body items are not appended to");
        assert!(base.inner_attrs.is_empty(), "base inner attrs are not appended to");
        assert_eq!(base.blocks.len(), 2, "arena blocks are appended");
        // The chunk's block (now at index 1) points at the caller's base.
        assert!(matches!(&base.blocks[1].stmts[..], [Stmt::Item(5), Stmt::Item(6)]));
        assert!(matches!(&base.blocks[0].stmts[..], [Stmt::Item(0)]), "old blocks keep their indexes");
    }
}
