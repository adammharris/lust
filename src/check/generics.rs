// Generic collection (docs/ARCH.md sections 2.1 to 2.3, W-TRAITS-CORE):
// lang trait defs, scoped type resolution over generic parameters,
// bounds to predicates, param environments, and the templates mono
// materializes instances from.
//
// A *template* is a generic Adt, fn, or trait method in signature
// form: types may contain `Param` and `Projection`, never `Infer`.
// Non-generic items are templates with no parameters, and their one
// instance is themselves, so the old concrete pipeline is the
// degenerate case of this one. Codegen only ever sees concrete
// instances (mono materializes them into the compat `AdtDef`/`FnInfo`
// tables). Each generic fn template is also checked once as written,
// with its `Param` types rigid under its bounds (`template_check`).
use crate::ast::{self, Ast, GenericArg as AstArg, GenericArgs, TraitBound, TyExpr};
use crate::check::collect::Program;
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span, not_yet};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::traits::index::{ImplIndex, TraitRecord};
use crate::traits::solve::{Selection, Solver};
use crate::ty::*;

/// The defs of the lang traits lust knows without source std: the
/// derive and marker traits, the operator traits, and the iterator
/// family the trait corpus and the MGP use by name. Their records
/// live in the impl index like user traits; their impls for builtin
/// types are synthetic index entries (see `synthetic_lang_impls` in
/// collect), and user impls of them are ordinary impls. Source std
/// (wave A2) replaces these defs with real ones under the same
/// names.
#[derive(Clone, Copy, Debug)]
pub struct LangTraits {
    pub sized: DefId,
    pub copy: DefId,
    pub clone: DefId,
    pub debug: DefId,
    pub display: DefId,
    pub partial_eq: DefId,
    pub eq: DefId,
    pub partial_ord: DefId,
    pub ord: DefId,
    pub hash: DefId,
    pub default: DefId,
    pub drop: DefId,
    pub send: DefId,
    pub sync: DefId,
    pub unpin: DefId,
    pub add: DefId,
    pub sub: DefId,
    pub mul: DefId,
    pub div: DefId,
    pub rem: DefId,
    pub neg: DefId,
    pub not: DefId,
    pub bit_and: DefId,
    pub bit_or: DefId,
    pub bit_xor: DefId,
    pub shl: DefId,
    pub shr: DefId,
    pub add_assign: DefId,
    pub sub_assign: DefId,
    pub mul_assign: DefId,
    pub div_assign: DefId,
    pub rem_assign: DefId,
    pub bit_and_assign: DefId,
    pub bit_or_assign: DefId,
    pub bit_xor_assign: DefId,
    pub shl_assign: DefId,
    pub shr_assign: DefId,
    pub index: DefId,
    pub index_mut: DefId,
    pub deref: DefId,
    pub deref_mut: DefId,
    pub iterator: DefId,
    pub into_iterator: DefId,
    pub from_iterator: DefId,
    pub from: DefId,
    pub into: DefId,
    /// `core::convert::TryFrom` and `TryInto`, each with its `Error`
    /// assoc (fx-tryfrom; check/tryfrom.rs).
    pub try_from: DefId,
    pub try_into: DefId,
    pub assoc_try_from_error: DefId,
    pub assoc_try_into_error: DefId,
    pub fn_: DefId,
    pub fn_mut: DefId,
    pub fn_once: DefId,
    pub exact_size_iterator: DefId,
    /// `DoubleEndedIterator` and `Extend<A>` (W-STD-B): for user impls
    /// (`rev` over a user iterator calls its `next_back`).
    pub double_ended_iterator: DefId,
    pub extend: DefId,
    /// `core::ops::RangeBounds` (fx-vec-drain).
    pub range_bounds: DefId,
    /// The conversion traits of `core::convert` and `core::borrow`
    /// (W-STD-B, check/convert.rs), and `ToOwned` with its `Owned`.
    pub as_ref: DefId,
    pub as_mut: DefId,
    pub borrow: DefId,
    pub borrow_mut: DefId,
    pub to_owned: DefId,
    /// `alloc::string::ToString`, with core's one blanket impl over
    /// `T: Display`; calls stay the builtin `to_string`.
    pub to_string: DefId,
    /// `core::any::Any` (check/any.rs): every `'static` type has it
    /// through one synthetic blanket impl.
    pub any: DefId,
    pub assoc_owned: DefId,
    /// `core::hash::Hasher` and `BuildHasher` with its `Hasher` assoc
    /// (W-STD-B, the hashed collections).
    pub hasher: DefId,
    pub build_hasher: DefId,
    pub assoc_hasher: DefId,
    /// `Iterator::Item`.
    pub assoc_item: DefId,
    /// `IntoIterator::IntoIter` (its `Item` is a distinct def).
    pub assoc_into_iter: DefId,
    pub assoc_into_item: DefId,
    /// `ops::*::Output`, one def per operator trait is not needed:
    /// projections key on the assoc def, so each operator trait
    /// gets its own entry in `outputs` below instead.
    pub outputs: [(DefId, DefId); 14],
    /// `Deref::Target` and `Index::Output`-style single assocs.
    pub assoc_target: DefId,
    pub assoc_index_output: DefId,
    /// `core::str::FromStr` and its `Err` (W-STD-C phase 2).
    pub from_str: DefId,
    pub assoc_from_str_err: DefId,
}

/// One lang def under the builtin crate identity, hashed from its
/// std path like the builtin Adt defs in `ty`.
fn lang_def(module: &[&str], kind: crate::def::DefKind, name: &str) -> DefId {
    static CRATE: std::sync::OnceLock<crate::def::StableCrateHash> = std::sync::OnceLock::new();
    let hash = *CRATE.get_or_init(|| crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false));
    DefId { krate: BUILTIN_CRATE, hash: crate::def::item_hash(hash, module, kind, name, 0) }
}

fn lang_trait(module: &[&str], name: &str) -> DefId {
    lang_def(module, crate::def::DefKind::Trait, name)
}

/// The def of `core::any::Any`, for type resolution outside a
/// `LangTraits` (the flat resolver's `std::thread::Result`, R26).
/// The same deterministic def `LangTraits::new` records.
pub fn any_trait_def() -> DefId {
    lang_trait(&["core", "any"], "Any")
}

fn lang_assoc(trait_def: DefId, name: &str) -> DefId {
    DefId { krate: BUILTIN_CRATE, hash: crate::def::child_hash(trait_def.hash, crate::def::DefKind::Assoc, name, 0) }
}

impl LangTraits {
    /// All lang trait and assoc defs, deterministic across sessions.
    pub fn new() -> LangTraits {
        let marker = &["core", "marker"];
        let ops = &["core", "ops"];
        let sized = lang_trait(marker, "Sized");
        let copy = lang_trait(marker, "Copy");
        let send = lang_trait(marker, "Send");
        let sync = lang_trait(marker, "Sync");
        let unpin = lang_trait(marker, "Unpin");
        let clone = lang_trait(&["core", "clone"], "Clone");
        let debug = lang_trait(&["core", "fmt"], "Debug");
        let display = lang_trait(&["core", "fmt"], "Display");
        let partial_eq = lang_trait(&["core", "cmp"], "PartialEq");
        let eq = lang_trait(&["core", "cmp"], "Eq");
        let partial_ord = lang_trait(&["core", "cmp"], "PartialOrd");
        let ord = lang_trait(&["core", "cmp"], "Ord");
        let hash = lang_trait(&["core", "hash"], "Hash");
        let default = lang_trait(&["core", "default"], "Default");
        let drop = lang_trait(ops, "Drop");
        let add = lang_trait(ops, "Add");
        let sub = lang_trait(ops, "Sub");
        let mul = lang_trait(ops, "Mul");
        let div = lang_trait(ops, "Div");
        let rem = lang_trait(ops, "Rem");
        let neg = lang_trait(ops, "Neg");
        let not = lang_trait(ops, "Not");
        let bit_and = lang_trait(ops, "BitAnd");
        let bit_or = lang_trait(ops, "BitOr");
        let bit_xor = lang_trait(ops, "BitXor");
        let shl = lang_trait(ops, "Shl");
        let shr = lang_trait(ops, "Shr");
        let add_assign = lang_trait(ops, "AddAssign");
        let sub_assign = lang_trait(ops, "SubAssign");
        let mul_assign = lang_trait(ops, "MulAssign");
        let div_assign = lang_trait(ops, "DivAssign");
        let rem_assign = lang_trait(ops, "RemAssign");
        let bit_and_assign = lang_trait(ops, "BitAndAssign");
        let bit_or_assign = lang_trait(ops, "BitOrAssign");
        let bit_xor_assign = lang_trait(ops, "BitXorAssign");
        let shl_assign = lang_trait(ops, "ShlAssign");
        let shr_assign = lang_trait(ops, "ShrAssign");
        let index = lang_trait(ops, "Index");
        let index_mut = lang_trait(ops, "IndexMut");
        let deref = lang_trait(ops, "Deref");
        let deref_mut = lang_trait(ops, "DerefMut");
        let fn_ = lang_trait(ops, "Fn");
        let fn_mut = lang_trait(ops, "FnMut");
        let fn_once = lang_trait(ops, "FnOnce");
        let iterator = lang_trait(&["core", "iter"], "Iterator");
        let into_iterator = lang_trait(&["core", "iter"], "IntoIterator");
        let from_iterator = lang_trait(&["core", "iter"], "FromIterator");
        let extend = lang_trait(&["core", "iter"], "Extend");
        let from_str = lang_trait(&["core", "str"], "FromStr");
        let exact_size_iterator = lang_trait(&["core", "iter"], "ExactSizeIterator");
        let double_ended_iterator = lang_trait(&["core", "iter"], "DoubleEndedIterator");
        let extend = lang_trait(&["core", "iter"], "Extend");
        let range_bounds = lang_trait(ops, "RangeBounds");
        let as_ref = lang_trait(&["core", "convert"], "AsRef");
        let as_mut = lang_trait(&["core", "convert"], "AsMut");
        let borrow = lang_trait(&["core", "borrow"], "Borrow");
        let borrow_mut = lang_trait(&["core", "borrow"], "BorrowMut");
        let to_owned = lang_trait(&["alloc", "borrow"], "ToOwned");
        let to_string = to_string_defs().0;
        let hasher = lang_trait(&["core", "hash"], "Hasher");
        let build_hasher = lang_trait(&["core", "hash"], "BuildHasher");
        let from = lang_trait(&["core", "convert"], "From");
        let into = lang_trait(&["core", "convert"], "Into");
        let try_from = lang_trait(&["core", "convert"], "TryFrom");
        let try_into = lang_trait(&["core", "convert"], "TryInto");
        let any = lang_trait(&["core", "any"], "Any");
        let assoc_out = |t: DefId| lang_assoc(t, "Output");
        LangTraits {
            sized,
            copy,
            clone,
            debug,
            display,
            partial_eq,
            eq,
            partial_ord,
            ord,
            hash,
            default,
            drop,
            send,
            sync,
            unpin,
            add,
            sub,
            mul,
            div,
            rem,
            neg,
            not,
            bit_and,
            bit_or,
            bit_xor,
            shl,
            shr,
            add_assign,
            sub_assign,
            mul_assign,
            div_assign,
            rem_assign,
            bit_and_assign,
            bit_or_assign,
            bit_xor_assign,
            shl_assign,
            shr_assign,
            index,
            index_mut,
            deref,
            deref_mut,
            iterator,
            into_iterator,
            from_iterator,
            from,
            into,
            try_from,
            try_into,
            assoc_try_from_error: lang_assoc(try_from, "Error"),
            assoc_try_into_error: lang_assoc(try_into, "Error"),
            fn_,
            fn_mut,
            fn_once,
            exact_size_iterator,
            double_ended_iterator,
            extend,
            range_bounds,
            as_ref,
            as_mut,
            borrow,
            borrow_mut,
            to_owned,
            to_string,
            any,
            assoc_owned: lang_assoc(to_owned, "Owned"),
            hasher,
            build_hasher,
            assoc_hasher: lang_assoc(build_hasher, "Hasher"),
            assoc_item: lang_assoc(iterator, "Item"),
            assoc_into_iter: lang_assoc(into_iterator, "IntoIter"),
            assoc_into_item: lang_assoc(into_iterator, "Item"),
            outputs: [
                (add, assoc_out(add)),
                (sub, assoc_out(sub)),
                (mul, assoc_out(mul)),
                (div, assoc_out(div)),
                (rem, assoc_out(rem)),
                (neg, assoc_out(neg)),
                (not, assoc_out(not)),
                (bit_and, assoc_out(bit_and)),
                (bit_or, assoc_out(bit_or)),
                (bit_xor, assoc_out(bit_xor)),
                (shl, assoc_out(shl)),
                (shr, assoc_out(shr)),
                // One `Output` def for the whole Fn family, declared on
                // FnOnce as in std (see `output_of`).
                (fn_once, assoc_out(fn_once)),
                (fn_mut, assoc_out(fn_once)),
            ],
            assoc_target: lang_assoc(deref, "Target"),
            assoc_index_output: lang_assoc(index, "Output"),
            from_str,
            assoc_from_str_err: lang_assoc(from_str, "Err"),
        }
    }

    /// The `Output` assoc def of an operator or `Fn` trait. The Fn
    /// family shares one def, `FnOnce::Output`, as in std: `Fn` and
    /// `FnMut` declare no `Output` of their own and `F: Fn() -> R`
    /// binds `<F as FnOnce<()>>::Output`. A projection of it selects
    /// `FnOnce`, which every closure and every Fn-bounded parameter
    /// implements (supertrait elaboration).
    pub fn output_of(&self, trait_def: DefId) -> Option<DefId> {
        if self.is_fn_family(trait_def) {
            return Some(self.outputs[12].1);
        }
        self.outputs.iter().find(|(t, _)| *t == trait_def).map(|(_, a)| *a)
    }

    /// True for `Fn`, `FnMut`, and `FnOnce`.
    pub fn is_fn_family(&self, trait_def: DefId) -> bool {
        trait_def == self.fn_ || trait_def == self.fn_mut || trait_def == self.fn_once
    }

    /// A lang trait by its Rust name, for bound resolution.
    pub fn by_name(&self, name: &str) -> Option<DefId> {
        Some(match name {
            "Sized" => self.sized,
            "Copy" => self.copy,
            "Clone" => self.clone,
            "Debug" => self.debug,
            "Display" => self.display,
            "PartialEq" => self.partial_eq,
            "Eq" => self.eq,
            "PartialOrd" => self.partial_ord,
            "Ord" => self.ord,
            "Hash" => self.hash,
            "Default" => self.default,
            "Drop" => self.drop,
            "Send" => self.send,
            "Sync" => self.sync,
            "Unpin" => self.unpin,
            "Add" => self.add,
            "Sub" => self.sub,
            "Mul" => self.mul,
            "Div" => self.div,
            "Rem" => self.rem,
            "Neg" => self.neg,
            "Not" => self.not,
            "BitAnd" => self.bit_and,
            "BitOr" => self.bit_or,
            "BitXor" => self.bit_xor,
            "Shl" => self.shl,
            "Shr" => self.shr,
            "AddAssign" => self.add_assign,
            "SubAssign" => self.sub_assign,
            "MulAssign" => self.mul_assign,
            "DivAssign" => self.div_assign,
            "RemAssign" => self.rem_assign,
            "BitAndAssign" => self.bit_and_assign,
            "BitOrAssign" => self.bit_or_assign,
            "BitXorAssign" => self.bit_xor_assign,
            "ShlAssign" => self.shl_assign,
            "ShrAssign" => self.shr_assign,
            "Index" => self.index,
            "IndexMut" => self.index_mut,
            "Deref" => self.deref,
            "DerefMut" => self.deref_mut,
            "Iterator" => self.iterator,
            "IntoIterator" => self.into_iterator,
            "FromIterator" => self.from_iterator,
            "Extend" => self.extend,
            "FromStr" => self.from_str,
            "ExactSizeIterator" => self.exact_size_iterator,
            "DoubleEndedIterator" => self.double_ended_iterator,
            "Extend" => self.extend,
            "RangeBounds" => self.range_bounds,
            "AsRef" => self.as_ref,
            "AsMut" => self.as_mut,
            "Borrow" => self.borrow,
            "BorrowMut" => self.borrow_mut,
            "ToOwned" => self.to_owned,
            "ToString" => self.to_string,
            "Hasher" => self.hasher,
            "BuildHasher" => self.build_hasher,
            "From" => self.from,
            "Into" => self.into,
            "TryFrom" => self.try_from,
            "TryInto" => self.try_into,
            "Fn" => self.fn_,
            "FnMut" => self.fn_mut,
            "FnOnce" => self.fn_once,
            "Any" => self.any,
            _ => return None,
        })
    }

    /// True for lang traits whose last input defaults to Self
    /// (`PartialEq<Rhs = Self>`, the binary and assignment operators).
    pub fn input_defaults_to_self(&self, def: DefId) -> bool {
        [
            self.partial_eq,
            self.partial_ord,
            self.add,
            self.sub,
            self.mul,
            self.div,
            self.rem,
            self.bit_and,
            self.bit_or,
            self.bit_xor,
            self.shl,
            self.shr,
            self.add_assign,
            self.sub_assign,
            self.mul_assign,
            self.div_assign,
            self.rem_assign,
            self.bit_and_assign,
            self.bit_or_assign,
            self.bit_xor_assign,
            self.shl_assign,
            self.shr_assign,
        ]
        .contains(&def)
    }

    /// True for the auto traits, which selection answers
    /// structurally, never through the impl index (section 2.7).
    pub fn is_auto(&self, def: DefId) -> bool {
        def == self.send || def == self.sync || def == self.unpin
    }
}

/// Builds the index records of the lang traits. A record's
/// generics start with `Self` (the module convention in
/// `traits/mod.rs`); supertrait predicates name that Self.
/// Method defs are synthetic: user impl methods are matched to
/// trait methods by name, so these defs only carry identity for
/// normalization and diagnostics.
pub fn lang_trait_records(lang: &LangTraits, interner: &Interner, tys: &mut impl TyIntern) -> Vec<TraitRecord> {
    let sym = |n: &str| interner.intern(n);
    // A supertrait predicate over this trait's own parameters:
    // `extra` lists the parameter indexes after Self (for example
    // `Eq: PartialEq<Self>` is [0], `IndexMut<I>: Index<I>` is [1]).
    let self_pred = |tys: &mut dyn TyIntern, trait_def: DefId, extra: &[u32]| -> Predicate {
        let mut all = vec![GenericArg::Ty(tys.intern(TyKind::Param(ParamId(0))))];
        for &i in extra {
            all.push(GenericArg::Ty(tys.intern(TyKind::Param(ParamId(i)))));
        }
        let args = tys.intern_args(&all);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    };
    let rec = |def: DefId, name: &str, n_inputs: usize, supers: Vec<Predicate>, assocs: Vec<(DefId, &str)>, methods: &[&str]| {
        let mut params: Vec<ParamDef> =
            (0..=n_inputs).map(|_| ParamDef { name: sym("T"), kind: ParamKind::Type, span: Span::default() }).collect();
        params[0].name = sym("Self");
        TraitRecord {
            def,
            name: sym(name),
            generics: Generics { parent: None, params, predicates: supers },
            assoc_items: assocs.iter().map(|&(d, n)| (d, sym(n), true)).collect(),
            methods: methods.iter().map(|&m| (lang_assoc(def, m), sym(m))).collect(),
            local: false,
            span: Span::default(),
        }
    };
    let binop = |def: DefId, name: &str, method: &str| rec(def, name, 1, vec![], vec![(lang.output_of(def).unwrap(), "Output")], &[method]);
    let unop = |def: DefId, name: &str, method: &str| rec(def, name, 0, vec![], vec![(lang.output_of(def).unwrap(), "Output")], &[method]);
    let assign = |def: DefId, name: &str, method: &str| rec(def, name, 1, vec![], vec![], &[method]);
    vec![
        rec(lang.sized, "Sized", 0, vec![], vec![], &[]),
        rec(lang.copy, "Copy", 0, vec![self_pred(tys, lang.clone, &[])], vec![], &[]),
        rec(lang.clone, "Clone", 0, vec![self_pred(tys, lang.sized, &[])], vec![], &["clone", "clone_from"]),
        rec(lang.debug, "Debug", 0, vec![], vec![], &["fmt"]),
        rec(lang.display, "Display", 0, vec![], vec![], &["fmt"]),
        rec(lang.partial_eq, "PartialEq", 1, vec![], vec![], &["eq", "ne"]),
        rec(lang.eq, "Eq", 0, vec![self_pred(tys, lang.partial_eq, &[0])], vec![], &[]),
        rec(
            lang.partial_ord,
            "PartialOrd",
            1,
            vec![self_pred(tys, lang.partial_eq, &[1])],
            vec![],
            &["partial_cmp", "lt", "le", "gt", "ge"],
        ),
        rec(
            lang.ord,
            "Ord",
            0,
            vec![self_pred(tys, lang.eq, &[]), self_pred(tys, lang.partial_ord, &[0])],
            vec![],
            &["cmp", "max", "min", "clamp"],
        ),
        rec(lang.hash, "Hash", 0, vec![], vec![], &["hash", "hash_slice"]),
        rec(lang.default, "Default", 0, vec![self_pred(tys, lang.sized, &[])], vec![], &["default"]),
        rec(lang.drop, "Drop", 0, vec![], vec![], &["drop"]),
        rec(lang.send, "Send", 0, vec![], vec![], &[]),
        rec(lang.sync, "Sync", 0, vec![], vec![], &[]),
        rec(lang.unpin, "Unpin", 0, vec![], vec![], &[]),
        binop(lang.add, "Add", "add"),
        binop(lang.sub, "Sub", "sub"),
        binop(lang.mul, "Mul", "mul"),
        binop(lang.div, "Div", "div"),
        binop(lang.rem, "Rem", "rem"),
        unop(lang.neg, "Neg", "neg"),
        unop(lang.not, "Not", "not"),
        binop(lang.bit_and, "BitAnd", "bitand"),
        binop(lang.bit_or, "BitOr", "bitor"),
        binop(lang.bit_xor, "BitXor", "bitxor"),
        binop(lang.shl, "Shl", "shl"),
        binop(lang.shr, "Shr", "shr"),
        assign(lang.add_assign, "AddAssign", "add_assign"),
        assign(lang.sub_assign, "SubAssign", "sub_assign"),
        assign(lang.mul_assign, "MulAssign", "mul_assign"),
        assign(lang.div_assign, "DivAssign", "div_assign"),
        assign(lang.rem_assign, "RemAssign", "rem_assign"),
        assign(lang.bit_and_assign, "BitAndAssign", "bitand_assign"),
        assign(lang.bit_or_assign, "BitOrAssign", "bitor_assign"),
        assign(lang.bit_xor_assign, "BitXorAssign", "bitxor_assign"),
        assign(lang.shl_assign, "ShlAssign", "shl_assign"),
        assign(lang.shr_assign, "ShrAssign", "shr_assign"),
        rec(lang.index, "Index", 1, vec![], vec![(lang.assoc_index_output, "Output")], &["index"]),
        rec(lang.index_mut, "IndexMut", 1, vec![self_pred(tys, lang.index, &[1])], vec![], &["index_mut"]),
        rec(lang.deref, "Deref", 0, vec![], vec![(lang.assoc_target, "Target")], &["deref"]),
        rec(lang.deref_mut, "DerefMut", 0, vec![self_pred(tys, lang.deref, &[])], vec![], &["deref_mut"]),
        rec(lang.iterator, "Iterator", 0, vec![], vec![(lang.assoc_item, "Item")], &["next", "size_hint"]),
        rec(
            lang.into_iterator,
            "IntoIterator",
            0,
            vec![into_iter_item_bound(lang, tys)],
            vec![(lang.assoc_into_item, "Item"), (lang.assoc_into_iter, "IntoIter")],
            &["into_iter"],
        ),
        rec(lang.from_iterator, "FromIterator", 1, vec![], vec![], &["from_iter"]),
        rec(lang.from_str, "FromStr", 0, vec![self_pred(tys, lang.sized, &[])], vec![(lang.assoc_from_str_err, "Err")], &["from_str"]),
        rec(lang.exact_size_iterator, "ExactSizeIterator", 0, vec![self_pred(tys, lang.iterator, &[])], vec![], &["len"]),
        rec(lang.double_ended_iterator, "DoubleEndedIterator", 0, vec![self_pred(tys, lang.iterator, &[])], vec![], &["next_back"]),
        rec(lang.extend, "Extend", 1, vec![], vec![], &["extend"]),
        rec(lang.range_bounds, "RangeBounds", 1, vec![], vec![], &["start_bound", "end_bound", "contains"]),
        rec(lang.as_ref, "AsRef", 1, vec![], vec![], &["as_ref"]),
        rec(lang.as_mut, "AsMut", 1, vec![], vec![], &["as_mut"]),
        rec(lang.borrow, "Borrow", 1, vec![], vec![], &["borrow"]),
        rec(lang.borrow_mut, "BorrowMut", 1, vec![self_pred(tys, lang.borrow, &[1])], vec![], &["borrow_mut"]),
        rec(lang.to_owned, "ToOwned", 0, vec![], vec![(lang.assoc_owned, "Owned")], &["to_owned", "clone_into"]),
        rec(lang.to_string, "ToString", 0, vec![], vec![], &["to_string"]),
        rec(lang.hasher, "Hasher", 0, vec![], vec![], &crate::check::hashmap::HASHER_METHODS),
        rec(lang.build_hasher, "BuildHasher", 0, vec![], vec![(lang.assoc_hasher, "Hasher")], &["build_hasher", "hash_one"]),
        rec(lang.from, "From", 1, vec![self_pred(tys, lang.sized, &[])], vec![], &["from"]),
        rec(lang.into, "Into", 1, vec![self_pred(tys, lang.sized, &[])], vec![], &["into"]),
        rec(
            lang.try_from,
            "TryFrom",
            1,
            vec![self_pred(tys, lang.sized, &[])],
            vec![(lang.assoc_try_from_error, "Error")],
            &["try_from"],
        ),
        rec(
            lang.try_into,
            "TryInto",
            1,
            vec![self_pred(tys, lang.sized, &[])],
            vec![(lang.assoc_try_into_error, "Error")],
            &["try_into"],
        ),
        rec(lang.fn_, "Fn", 1, vec![self_pred(tys, lang.fn_mut, &[1])], vec![], &["call"]),
        rec(lang.fn_mut, "FnMut", 1, vec![self_pred(tys, lang.fn_once, &[1])], vec![], &["call_mut"]),
        rec(lang.fn_once, "FnOnce", 1, vec![], vec![(lang.output_of(lang.fn_once).unwrap(), "Output")], &["call_once"]),
        // `trait Any: 'static`: a bound `T: Any` elaborates to `T: 'static`.
        rec(lang.any, "Any", 0, vec![Predicate::TypeOutlives(tys.intern(TyKind::Param(ParamId(0))), Region::Static)], vec![], &["type_id"]),
    ]
}

/// core's item bound on `IntoIterator::IntoIter` (`type IntoIter:
/// Iterator<Item = Self::Item>`), as a predicate of the trait like a
/// user trait's assoc type bounds: an env with `I: IntoIterator`
/// elaborates it, so `i.into_iter().next()` checks in a template, and
/// every impl must satisfy it.
fn into_iter_item_bound(lang: &LangTraits, tys: &mut impl TyIntern) -> Predicate {
    let self_ty = tys.intern(TyKind::Param(ParamId(0)));
    let self_args = tys.intern_args(&[GenericArg::Ty(self_ty)]);
    let into_iter = tys.intern(TyKind::Projection(AssocId(lang.assoc_into_iter), self_args));
    let item = tys.intern(TyKind::Projection(AssocId(lang.assoc_into_item), self_args));
    let args = tys.intern_args(&[GenericArg::Ty(into_iter)]);
    let bindings = tys.intern_bindings(&[(lang.assoc_item, GenericArg::Ty(item))]);
    Predicate::Trait(Binder::plain(TraitRef { def: lang.iterator, args, bindings }))
}

/// The defs of `TryFrom::Error` and `TryInto::Error`, recomputed
/// from their std paths for callers without a `LangTraits` at hand
/// (the solver's pure context, fx-tryfrom).
pub fn try_from_error_assoc() -> DefId {
    lang_assoc(lang_trait(&["core", "convert"], "TryFrom"), "Error")
}

/// `TryInto::Error`'s def (see `try_from_error_assoc`).
pub fn try_into_error_assoc() -> DefId {
    lang_assoc(lang_trait(&["core", "convert"], "TryInto"), "Error")
}

/// The defs of `alloc::string::ToString` and its `to_string`
/// method, recomputed from their std paths (see
/// `try_from_error_assoc`). `ToString` is not a lang trait: when
/// the shipped std source brings the real trait its def differs,
/// and these name only the marker `check/traitpath.rs` puts on a
/// `ToString::to_string` value when no record exists.
pub fn to_string_defs() -> (DefId, DefId) {
    let tr = lang_trait(&["alloc", "string"], "ToString");
    (tr, lang_assoc(tr, "to_string"))
}

/// The def of `core::cmp::Ordering`, the fieldless enum lang
/// signatures below name. Collect registers a local Adt for it
/// (its variants, layout, and derives are the ordinary enum
/// machinery); this def is its stable identity.
pub fn ordering_def() -> DefId {
    std_adt_table()[0].2
}

/// The `core::cmp::Ordering` type.
pub fn ordering_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(ordering_def(), EMPTY_ARGS))
}

/// The def of `core::fmt::Error`, the unit struct of `fmt::Result`
/// (W-STD-B). Collect registers a local Adt for it like `Ordering`,
/// but never under a bare name: only `fmt::Error` paths reach it.
pub fn fmt_error_def() -> DefId {
    std_adt_table()[1].2
}

/// The def of `alloc::borrow::Cow` (W-STD-B): a synthetic generic enum
/// collect registers like `Ordering`, reached only through std paths
/// (`std::borrow::Cow` and imports of it), never by a bare name.
pub fn cow_def() -> DefId {
    std_adt_table()[9].2
}

/// The `core::fmt::Error` type.
pub fn fmt_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(fmt_error_def(), EMPTY_ARGS))
}

/// The def of `core::any::TypeId` (check/any.rs). Collect registers a
/// local Adt for it like `fmt::Error`: a struct of two `u64` words of
/// the type's hash, with field names source text cannot write. Only
/// `any::TypeId` paths reach it.
pub fn type_id_def() -> DefId {
    std_adt_table()[7].2
}

/// The defs of `core::cell::BorrowError` and `BorrowMutError`, the
/// errors of `RefCell::try_borrow` and `try_borrow_mut`: synthetic unit
/// structs (W-STD-B).
pub fn borrow_error_def() -> DefId {
    std_adt_table()[10].2
}

pub fn borrow_mut_error_def() -> DefId {
    std_adt_table()[11].2
}

/// The def of `core::panic::Location` (check/caller.rs): a synthetic std
/// Adt of `file: &str, line: u32, column: u32`, reached by path only.
pub fn location_def() -> DefId {
    std_adt_table()[8].2
}

/// The `core::any::TypeId` type.
pub fn type_id_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(type_id_def(), EMPTY_ARGS))
}

/// `fmt::Result`: `Result<(), fmt::Error>`.
pub fn fmt_result_ty(tys: &mut impl TyIntern) -> Ty {
    let e = fmt_error_ty(tys);
    tys.mk_result(UNIT, e)
}

/// The def of `core::str::Utf8Error`, a synthetic struct Adt like
/// `Ordering` (W-STD-A): `valid_up_to: usize, error_len: Option<u8>`.
pub fn utf8_error_def() -> DefId {
    std_adt_table()[2].2
}

/// The def of `alloc::string::FromUtf8Error`, a synthetic struct Adt:
/// `bytes: Vec<u8>, error: Utf8Error`.
pub fn from_utf8_error_def() -> DefId {
    std_adt_table()[3].2
}

/// The def of `core::sync::atomic::Ordering`, the memory ordering
/// enum of the atomics (W-THREADS): a synthetic Adt like `cmp::Ordering`,
/// with Rust's variant order (Relaxed, Release, Acquire, AcqRel, SeqCst).
pub fn atomic_ordering_def() -> DefId {
    std_adt_table()[4].2
}

/// The def of `std::sync::mpsc::RecvError`, a synthetic unit struct
/// (W-THREADS).
pub fn recv_error_def() -> DefId {
    std_adt_table()[5].2
}

/// The def of `std::sync::mpsc::TryRecvError`, a synthetic enum
/// (`Empty`, `Disconnected`; W-THREADS).
pub fn try_recv_error_def() -> DefId {
    std_adt_table()[6].2
}

/// The def of `core::num::TryFromIntError` (fx-tryfrom), a synthetic
/// tuple struct over `IntErrorKind` like `Ordering`. Only `num::`
/// paths reach it (no flat name, like `fmt::Error`).
pub fn try_from_int_error_def() -> DefId {
    std_adt_table()[13].2
}

/// The `core::num::TryFromIntError` type.
pub fn try_from_int_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(try_from_int_error_def(), EMPTY_ARGS))
}

/// The def of `core::num::IntErrorKind`, the kind field of
/// `TryFromIntError` (fx-tryfrom): `Empty`, `InvalidDigit`,
/// `PosOverflow`, `NegOverflow`, `Zero`, in core's order.
pub fn int_error_kind_def() -> DefId {
    std_adt_table()[14].2
}

/// The `core::num::IntErrorKind` type.
pub fn int_error_kind_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(int_error_kind_def(), EMPTY_ARGS))
}

/// The def of `core::char::CharTryFromError` (fx-tryfrom), the error
/// of `char: TryFrom<u32>`: a tuple struct over `()`.
pub fn char_try_from_error_def() -> DefId {
    std_adt_table()[15].2
}

/// The `core::char::CharTryFromError` type.
pub fn char_try_from_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(char_try_from_error_def(), EMPTY_ARGS))
}

/// The def of `core::char::TryFromCharError` (fx-tryfrom), the error
/// of `u8`/`u16`/`usize: TryFrom<char>`: a tuple struct over `()`.
pub fn try_from_char_error_def() -> DefId {
    std_adt_table()[16].2
}

/// The `core::char::TryFromCharError` type.
pub fn try_from_char_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(try_from_char_error_def(), EMPTY_ARGS))
}

/// The def of `core::convert::Infallible` (fx-tryfrom), core's empty
/// enum: the `Error` of the blanket `TryFrom` through `Into`.
pub fn infallible_def() -> DefId {
    std_adt_table()[17].2
}

/// The `core::convert::Infallible` type.
pub fn infallible_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(infallible_def(), EMPTY_ARGS))
}

/// The def of `core::num::ParseIntError` (tf-str), the error of int
/// `FromStr`: a struct over an `IntErrorKind` field named `kind`.
pub fn parse_int_error_def() -> DefId {
    std_adt_table()[18].2
}

/// The `core::num::ParseIntError` type.
pub fn parse_int_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(parse_int_error_def(), EMPTY_ARGS))
}

/// The def of `core::num::ParseFloatError` (tf-str).
pub fn parse_float_error_def() -> DefId {
    std_adt_table()[19].2
}

/// The `core::num::ParseFloatError` type.
pub fn parse_float_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(parse_float_error_def(), EMPTY_ARGS))
}

/// The def of core's float parse kind enum (`Empty`, `Invalid`):
/// not nameable in source, but `ParseFloatError`'s Debug prints it.
pub fn float_error_kind_def() -> DefId {
    std_adt_table()[20].2
}

/// The def of `core::str::ParseBoolError` (tf-str), a unit struct.
pub fn parse_bool_error_def() -> DefId {
    std_adt_table()[21].2
}

/// The `core::str::ParseBoolError` type.
pub fn parse_bool_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(parse_bool_error_def(), EMPTY_ARGS))
}

/// The def of `core::char::ParseCharError` (tf-str).
pub fn parse_char_error_def() -> DefId {
    std_adt_table()[22].2
}

/// The `core::char::ParseCharError` type.
pub fn parse_char_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(parse_char_error_def(), EMPTY_ARGS))
}

/// The def of core's char parse kind enum (`EmptyString`,
/// `TooManyChars`): not nameable in source, but Debug prints it.
pub fn char_error_kind_def() -> DefId {
    std_adt_table()[23].2
}

/// The def of `core::array::TryFromSliceError` (tf-slice), a tuple
/// struct over `()`. Only `array::` paths reach it (no flat name,
/// like `TryFromIntError`).
pub fn try_from_slice_error_def() -> DefId {
    std_adt_table()[24].2
}

/// The `core::array::TryFromSliceError` type.
pub fn try_from_slice_error_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(try_from_slice_error_def(), EMPTY_ARGS))
}

/// The `core::sync::atomic::Ordering` type.
pub fn atomic_ordering_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(atomic_ordering_def(), EMPTY_ARGS))
}

/// The def of `core::num::NonZero<T>` (TRIAGE T5): a synthetic
/// generic struct Adt over its integer, like `Bound`. The def
/// itself lives in `ty` so layout can name it.
pub fn nonzero_def() -> DefId {
    crate::ty::nonzero_def()
}

/// The `core::num::NonZero<T>` type.
pub fn nonzero_ty(tys: &mut impl TyIntern, t: Ty) -> Ty {
    tys.mk_adt(nonzero_def(), &[GenericArg::Ty(t)])
}

/// The integer inside a `NonZero<T>` type, when `t` is one.
pub fn nonzero_elem(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    let (def, _) = tys.adt_parts(t)?;
    (def == nonzero_def()).then(|| tys.adt_first_ty_arg(t)).flatten()
}

/// The def of `std::sync::mpsc::TrySendError<T>` (TRIAGE T5):
/// a synthetic generic enum Adt like `Bound`.
pub fn try_send_error_def() -> DefId {
    std_adt_table()[26].2
}

/// The `std::sync::mpsc::TrySendError<T>` type.
pub fn try_send_error_ty(tys: &mut impl TyIntern, t: Ty) -> Ty {
    tys.mk_adt(try_send_error_def(), &[GenericArg::Ty(t)])
}

/// The def of `std::sync::TryLockError<T>`, a synthetic generic enum
/// (`Poisoned(PoisonError<T>)`, `WouldBlock`): the `Err` of `try_lock`,
/// `try_read`, and `try_write`.
pub fn try_lock_error_def() -> DefId {
    std_adt_table()[30].2
}

/// The `std::sync::TryLockError<T>` type.
pub fn try_lock_error_ty(tys: &mut impl TyIntern, t: Ty) -> Ty {
    tys.mk_adt(try_lock_error_def(), &[GenericArg::Ty(t)])
}

/// The def of `std::sync::mpsc::RecvTimeoutError`, a synthetic enum
/// (`Timeout`, `Disconnected`; tf-p6 R09).
pub fn recv_timeout_error_def() -> DefId {
    std_adt_table()[29].2
}

/// The def of `std::sync::WaitTimeoutResult` (TRIAGE T5): a
/// synthetic tuple struct over its timed-out flag.
pub fn wait_timeout_result_def() -> DefId {
    std_adt_table()[27].2
}

/// The `std::sync::WaitTimeoutResult` type.
pub fn wait_timeout_result_ty(tys: &mut impl TyIntern) -> Ty {
    tys.intern(TyKind::Adt(wait_timeout_result_def(), EMPTY_ARGS))
}

/// The def of `core::mem::MaybeUninit<T>` (TRIAGE T5): a
/// synthetic generic struct Adt over its bytes. The def itself
/// lives in `ty` so layout can name it.
pub fn maybe_uninit_def() -> DefId {
    crate::ty::maybe_uninit_def()
}

/// The `core::mem::MaybeUninit<T>` type.
pub fn maybe_uninit_ty(tys: &mut impl TyIntern, t: Ty) -> Ty {
    tys.mk_adt(maybe_uninit_def(), &[GenericArg::Ty(t)])
}

/// The value type inside a `MaybeUninit<T>` type, when `t` is one.
pub fn maybe_uninit_elem(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    let (def, _) = tys.adt_parts(t)?;
    (def == maybe_uninit_def()).then(|| tys.adt_first_ty_arg(t)).flatten()
}

/// The def of `core::ops::Bound<T>`, a synthetic generic enum Adt:
/// `Included(T)`, `Excluded(T)`, `Unbounded`, in std's order.
pub fn bound_def() -> DefId {
    lang_def(&["core", "ops"], crate::def::DefKind::Adt, "Bound")
}

/// The `core::ops::Bound<T>` type.
pub fn bound_ty(tys: &mut impl TyIntern, t: Ty) -> Ty {
    tys.mk_adt(bound_def(), &[GenericArg::Ty(t)])
}

/// True when `t` is a `core::ops::Bound<T>` type, with its `T`.
pub fn bound_elem(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    let (def, _) = tys.adt_parts(t)?;
    (def == bound_def()).then(|| tys.adt_first_ty_arg(t)).flatten()
}

/// The synthetic std Adts collect always registers, as (index, name,
/// def, is_enum). A user type, alias, or trait of the same name shadows
/// only the flat name (check/collect.rs); `fmt::Error` and
/// `atomic::Ordering` never have one (see `std_adt_has_flat_name`). The
/// generic `Cow` (W-STD-B) is built apart in collect. The driver
/// predicts the same list.
pub fn std_adts() -> [(usize, &'static str, DefId, bool); 31] {
    *std_adt_table()
}

/// The `std_adts` rows, hashed once per process: the `*_def` fns above
/// read them on hot paths (field privacy, every collect run).
fn std_adt_table() -> &'static [(usize, &'static str, DefId, bool); 31] {
    static TABLE: std::sync::OnceLock<[(usize, &'static str, DefId, bool); 31]> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let adt = |module: &[&str], name: &str| lang_def(module, crate::def::DefKind::Adt, name);
        [
            (0, "Ordering", adt(&["core", "cmp"], "Ordering"), true),
            (1, "Error", adt(&["core", "fmt"], "Error"), false),
            (2, "Utf8Error", adt(&["core", "str"], "Utf8Error"), false),
            (3, "FromUtf8Error", adt(&["alloc", "string"], "FromUtf8Error"), false),
            (4, "Ordering", adt(&["core", "sync", "atomic"], "Ordering"), true),
            (5, "RecvError", adt(&["std", "sync", "mpsc"], "RecvError"), false),
            (6, "TryRecvError", adt(&["std", "sync", "mpsc"], "TryRecvError"), true),
            (7, "TypeId", adt(&["core", "any"], "TypeId"), false),
            (8, "Location", adt(&["core", "panic"], "Location"), false),
            (9, "Cow", adt(&["alloc", "borrow"], "Cow"), true),
            (10, "BorrowError", adt(&["core", "cell"], "BorrowError"), false),
            (11, "BorrowMutError", adt(&["core", "cell"], "BorrowMutError"), false),
            (12, "Bound", adt(&["core", "ops"], "Bound"), true),
            (13, "TryFromIntError", adt(&["core", "num"], "TryFromIntError"), false),
            (14, "IntErrorKind", adt(&["core", "num"], "IntErrorKind"), true),
            (15, "CharTryFromError", adt(&["core", "char"], "CharTryFromError"), false),
            (16, "TryFromCharError", adt(&["core", "char"], "TryFromCharError"), false),
            (17, "Infallible", adt(&["core", "convert"], "Infallible"), true),
            (18, "ParseIntError", adt(&["core", "num"], "ParseIntError"), false),
            (19, "ParseFloatError", adt(&["core", "num"], "ParseFloatError"), false),
            (20, "FloatErrorKind", adt(&["core", "num"], "FloatErrorKind"), true),
            (21, "ParseBoolError", adt(&["core", "str"], "ParseBoolError"), false),
            (22, "ParseCharError", adt(&["core", "char"], "ParseCharError"), false),
            (23, "CharErrorKind", adt(&["core", "char"], "CharErrorKind"), true),
            (24, "TryFromSliceError", adt(&["core", "array"], "TryFromSliceError"), false),
            (25, "NonZero", adt(&["core", "num"], "NonZero"), false),
            (26, "TrySendError", adt(&["std", "sync", "mpsc"], "TrySendError"), true),
            (27, "WaitTimeoutResult", adt(&["std", "sync"], "WaitTimeoutResult"), false),
            (28, "MaybeUninit", adt(&["core", "mem"], "MaybeUninit"), false),
            (29, "RecvTimeoutError", adt(&["std", "sync", "mpsc"], "RecvTimeoutError"), true),
            (30, "TryLockError", adt(&["std", "sync"], "TryLockError"), true),
        ]
    })
}

/// True when the synthetic std Adt at `index` (see `std_adts`) enters
/// the flat type name table. `fmt::Error` and `atomic::Ordering` do
/// not: only their std paths (after a `use`, rewritten) reach them.
pub fn std_adt_has_flat_name(index: usize) -> bool {
    !matches!(index, 1 | 4 | 5 | 6 | 7 | 8 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30)
}

/// The (Adt, variant) of a std enum variant path such as
/// `std::cmp::Ordering::Less` or `core::sync::atomic::Ordering::SeqCst`.
/// None when the path is not a canonical std variant path, or names
/// no variant of its enum.
pub fn std_variant_of(p: &crate::check::collect::Program, names: &[&str]) -> Option<(AdtId, u32)> {
    let (&variant, ty_path) = names.split_last()?;
    if names.len() < 4 || !matches!(names[0], "std" | "core") || crate::ty::lang::std_path_kind(ty_path) != Some(crate::ty::lang::StdPathKind::Type) {
        return None;
    }
    let a = p.tys.local_adt_of(std_adt_of_path(ty_path)?)?;
    if !p.adt(a).is_enum {
        return None;
    }
    let v = p.adt(a).variants.iter().position(|v| p.interner.get(v.name) == variant)?;
    Some((a, v as u32))
}

/// The synthetic std Adt a canonical std type path (`std::cmp::Ordering`,
/// `std::fmt::Error`) names, by its module and name.
pub fn std_adt_of_path(path: &[&str]) -> Option<DefId> {
    let [.., module, name] = path else { return None };
    [
        ("cmp", "Ordering", ordering_def()),
        ("fmt", "Error", fmt_error_def()),
        ("str", "Utf8Error", utf8_error_def()),
        ("string", "FromUtf8Error", from_utf8_error_def()),
        ("atomic", "Ordering", atomic_ordering_def()),
        ("mpsc", "RecvError", recv_error_def()),
        ("mpsc", "TryRecvError", try_recv_error_def()),
        ("mpsc", "RecvTimeoutError", recv_timeout_error_def()),
        ("any", "TypeId", type_id_def()),
        ("ops", "Bound", bound_def()),
        ("num", "NonZero", nonzero_def()),
        ("mpsc", "TrySendError", try_send_error_def()),
        ("sync", "WaitTimeoutResult", wait_timeout_result_def()),
        ("sync", "TryLockError", try_lock_error_def()),
        ("mem", "MaybeUninit", maybe_uninit_def()),
        ("panic", "Location", location_def()),
        ("cell", "BorrowError", borrow_error_def()),
        ("cell", "BorrowMutError", borrow_mut_error_def()),
        ("num", "TryFromIntError", try_from_int_error_def()),
        ("num", "IntErrorKind", int_error_kind_def()),
        ("char", "CharTryFromError", char_try_from_error_def()),
        ("char", "TryFromCharError", try_from_char_error_def()),
        ("convert", "Infallible", infallible_def()),
        ("num", "ParseIntError", parse_int_error_def()),
        ("num", "ParseFloatError", parse_float_error_def()),
        ("str", "ParseBoolError", parse_bool_error_def()),
        ("char", "ParseCharError", parse_char_error_def()),
        ("array", "TryFromSliceError", try_from_slice_error_def()),
    ]
        .into_iter()
        .find(|(m, n, _)| m == module && n == name)
        .map(|(_, _, d)| d)
}

/// True when the Adt is one of the synthetic std Adts: a std path may
/// name it, and code outside std sees none of its fields.
pub fn is_std_adt(tys: &impl TyIntern, a: AdtId) -> bool {
    tys.def_of_local_adt(a)
        .is_some_and(|d| d.krate == BUILTIN_CRATE && std_adt_table().iter().any(|s| s.2 == d) && tys.local_adt_of(d) == Some(a))
}

/// The signature of one lang trait method over the trait's generics
/// (Self at 0, then the inputs): receiver form, parameter types
/// with the receiver first, return type, and which parameter a
/// returned reference borrows from. This is the lang half of
/// `TraitMethodTemplate` (lang methods have no AST def or body);
/// `add_trait_method_stubs` turns each entry into the stub fn a
/// template check calls through a bound.
#[derive(Clone, Debug)]
pub struct LangMethodSig {
    pub self_kind: Option<ast::SelfKind>,
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub ret_borrows_from: Option<usize>,
}

/// Builds the lang method signatures from the lang trait records:
/// one entry per (trait, method) the records declare, keyed by
/// method def. The match is by trait and method name together, so
/// a method only ever gets its own trait's signature; the operator
/// families are the closed list of lang operator traits. Methods
/// with no entry are ones a body cannot call through a bound in
/// this subset: `hash` names a type lust has no def for yet
/// (`Hasher`), `from_iter` has a method-level
/// generic the stub form cannot state, and `drop` is not callable.
pub fn lang_method_sigs(
    lang: &LangTraits,
    interner: &Interner,
    tys: &mut impl TyIntern,
    records: &[TraitRecord],
) -> FxMap<DefId, LangMethodSig> {
    use ast::SelfKind::{Ref, RefMut, Value};
    let p0 = tys.intern(TyKind::Param(ParamId(0)));
    let p1 = tys.intern(TyKind::Param(ParamId(1)));
    let r0 = tys.mk_ref(false, p0);
    let m0 = tys.mk_ref(true, p0);
    let r1 = tys.mk_ref(false, p1);
    let ord = ordering_ty(tys);
    let proj = |tys: &mut dyn TyIntern, assoc: DefId, args: &[Ty]| {
        let a: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let a = tys.intern_args(&a);
        tys.intern(TyKind::Projection(AssocId(assoc), a))
    };
    let binops = [
        (lang.add, "add"),
        (lang.sub, "sub"),
        (lang.mul, "mul"),
        (lang.div, "div"),
        (lang.rem, "rem"),
        (lang.bit_and, "bitand"),
        (lang.bit_or, "bitor"),
        (lang.bit_xor, "bitxor"),
        (lang.shl, "shl"),
        (lang.shr, "shr"),
    ];
    let unops = [(lang.neg, "neg"), (lang.not, "not")];
    let assigns = [
        (lang.add_assign, "add_assign"),
        (lang.sub_assign, "sub_assign"),
        (lang.mul_assign, "mul_assign"),
        (lang.div_assign, "div_assign"),
        (lang.rem_assign, "rem_assign"),
        (lang.bit_and_assign, "bitand_assign"),
        (lang.bit_or_assign, "bitor_assign"),
        (lang.bit_xor_assign, "bitxor_assign"),
        (lang.shl_assign, "shl_assign"),
        (lang.shr_assign, "shr_assign"),
    ];
    let mut out: FxMap<DefId, LangMethodSig> = FxMap::default();
    for rec in records {
        for &(method_def, name) in &rec.methods {
            let name: &str = interner.get(name);
            let sig = match (rec.def, name) {
                (d, "clone") if d == lang.clone => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: p0, ret_borrows_from: None }
                }
                (d, "clone_from") if d == lang.clone => {
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0, r0], ret: UNIT, ret_borrows_from: None }
                }
                (d, "next") if d == lang.iterator => {
                    let item = proj(tys, lang.assoc_item, &[p0]);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: tys.mk_option(item), ret_borrows_from: None }
                }
                (d, "next_back") if d == lang.double_ended_iterator => {
                    let item = proj(tys, lang.assoc_item, &[p0]);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: tys.mk_option(item), ret_borrows_from: None }
                }
                (d, "size_hint") if d == lang.iterator => {
                    let ou = tys.mk_option(USIZE);
                    let pair = tys.intern_tys(&[USIZE, ou]);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: tys.intern(TyKind::Tuple(pair)), ret_borrows_from: None }
                }
                (d, "into_iter") if d == lang.into_iterator => LangMethodSig {
                    self_kind: Some(Value),
                    params: vec![p0],
                    ret: proj(tys, lang.assoc_into_iter, &[p0]),
                    ret_borrows_from: None,
                },
                (d, "deref") if d == lang.deref => {
                    let t = proj(tys, lang.assoc_target, &[p0]);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: tys.mk_ref(false, t), ret_borrows_from: Some(0) }
                }
                (d, "deref_mut") if d == lang.deref_mut => {
                    let t = proj(tys, lang.assoc_target, &[p0]);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: tys.mk_ref(true, t), ret_borrows_from: Some(0) }
                }
                (d, "from_str") if d == lang.from_str => {
                    let err = proj(tys, lang.assoc_from_str_err, &[p0]);
                    LangMethodSig { self_kind: None, params: vec![REF_STR], ret: tys.mk_result(p0, err), ret_borrows_from: None }
                }
                (d, "from") if d == lang.from => LangMethodSig { self_kind: None, params: vec![p1], ret: p0, ret_borrows_from: None },
                (d, "into") if d == lang.into => {
                    LangMethodSig { self_kind: Some(Value), params: vec![p0], ret: p1, ret_borrows_from: None }
                }
                (d, "try_from") if d == lang.try_from => {
                    let err = proj(tys, lang.assoc_try_from_error, &[p0, p1]);
                    LangMethodSig { self_kind: None, params: vec![p1], ret: tys.mk_result(p0, err), ret_borrows_from: None }
                }
                (d, "try_into") if d == lang.try_into => {
                    let err = proj(tys, lang.assoc_try_into_error, &[p0, p1]);
                    LangMethodSig { self_kind: Some(Value), params: vec![p0], ret: tys.mk_result(p1, err), ret_borrows_from: None }
                }
                (d, "default") if d == lang.default => {
                    LangMethodSig { self_kind: None, params: Vec::new(), ret: p0, ret_borrows_from: None }
                }
                (d, "eq" | "ne") if d == lang.partial_eq => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, r1], ret: BOOL, ret_borrows_from: None }
                }
                (d, "partial_cmp") if d == lang.partial_ord => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, r1], ret: tys.mk_option(ord), ret_borrows_from: None }
                }
                (d, "lt" | "le" | "gt" | "ge") if d == lang.partial_ord => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, r1], ret: BOOL, ret_borrows_from: None }
                }
                (d, "cmp") if d == lang.ord => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, r0], ret: ord, ret_borrows_from: None }
                }
                (d, "as_ref" | "borrow") if d == lang.as_ref || d == lang.borrow => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: r1, ret_borrows_from: Some(0) }
                }
                (d, "as_mut" | "borrow_mut") if d == lang.as_mut || d == lang.borrow_mut => {
                    let m1 = tys.mk_ref(true, p1);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: m1, ret_borrows_from: Some(0) }
                }
                // `Hasher` (W-STD-B): finish, write, and the write_* family.
                (d, "finish") if d == lang.hasher => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: int(IntTy::U64), ret_borrows_from: None }
                }
                (d, n) if d == lang.hasher => {
                    let arg = match crate::check::hashmap::hasher_write_arg(n) {
                        Some(Some(i)) => int(i),
                        Some(None) => {
                            let s = tys.intern(TyKind::Slice(int(IntTy::U8)));
                            tys.mk_ref(false, s)
                        }
                        None => continue,
                    };
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0, arg], ret: UNIT, ret_borrows_from: None }
                }
                (d, "build_hasher") if d == lang.build_hasher => {
                    let h = proj(tys, lang.assoc_hasher, &[p0]);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: h, ret_borrows_from: None }
                }
                (d, "to_string") if d == lang.to_string => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: STRING, ret_borrows_from: None }
                }
                (d, "to_owned") if d == lang.to_owned => {
                    let owned = proj(tys, lang.assoc_owned, &[p0]);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: owned, ret_borrows_from: None }
                }
                (d, "fmt") if d == lang.debug || d == lang.display => {
                    // `fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result` (W-STD-B).
                    let f = crate::ty::fmt::fmt_ty(tys, crate::ty::fmt::FmtTy::Formatter);
                    let fm = tys.mk_ref(true, f);
                    let ret = fmt_result_ty(tys);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, fm], ret, ret_borrows_from: None }
                }
                (d, "max" | "min") if d == lang.ord => {
                    LangMethodSig { self_kind: Some(Value), params: vec![p0, p0], ret: p0, ret_borrows_from: None }
                }
                (d, "clamp") if d == lang.ord => {
                    LangMethodSig { self_kind: Some(Value), params: vec![p0, p0, p0], ret: p0, ret_borrows_from: None }
                }
                (d, "len") if d == lang.exact_size_iterator => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: USIZE, ret_borrows_from: None }
                }
                (d, "next_back") if d == lang.double_ended_iterator => {
                    let item = proj(tys, lang.assoc_item, &[p0]);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: tys.mk_option(item), ret_borrows_from: None }
                }
                (d, "contains") if d == lang.range_bounds => {
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, r1], ret: BOOL, ret_borrows_from: None }
                }
                (d, "start_bound" | "end_bound") if d == lang.range_bounds => {
                    let r1 = tys.mk_ref(false, p1);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret: bound_ty(tys, r1), ret_borrows_from: Some(0) }
                }
                (d, "index") if d == lang.index => {
                    let o = proj(tys, lang.assoc_index_output, &[p0, p1]);
                    LangMethodSig { self_kind: Some(Ref), params: vec![r0, p1], ret: tys.mk_ref(false, o), ret_borrows_from: Some(0) }
                }
                (d, "index_mut") if d == lang.index_mut => {
                    let o = proj(tys, lang.assoc_index_output, &[p0, p1]);
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0, p1], ret: tys.mk_ref(true, o), ret_borrows_from: Some(0) }
                }
                (d, "call" | "call_mut" | "call_once") if lang.output_of(d).is_some() => {
                    let out_ty = proj(tys, lang.output_of(d).unwrap(), &[p0, p1]);
                    let (kind, recv) = match name {
                        "call" => (Some(Ref), r0),
                        "call_mut" => (Some(RefMut), m0),
                        _ => (Some(Value), p0),
                    };
                    LangMethodSig { self_kind: kind, params: vec![recv, p1], ret: out_ty, ret_borrows_from: None }
                }
                (d, n) if binops.contains(&(d, n)) => {
                    // Binary operators: `fn add(self, rhs: Rhs) -> Self::Output`.
                    let o = proj(tys, lang.output_of(d).unwrap(), &[p0, p1]);
                    LangMethodSig { self_kind: Some(Value), params: vec![p0, p1], ret: o, ret_borrows_from: None }
                }
                (d, n) if unops.contains(&(d, n)) => {
                    // Unary operators: `fn neg(self) -> Self::Output`.
                    let o = proj(tys, lang.output_of(d).unwrap(), &[p0]);
                    LangMethodSig { self_kind: Some(Value), params: vec![p0], ret: o, ret_borrows_from: None }
                }
                (d, n) if assigns.contains(&(d, n)) => {
                    // Assignment operators: `fn add_assign(&mut self, rhs: Rhs)`.
                    LangMethodSig { self_kind: Some(RefMut), params: vec![m0, p1], ret: UNIT, ret_borrows_from: None }
                }
                _ => continue,
            };
            out.insert(method_def, sig);
        }
    }
    out
}

/// One type that associated types can be projected from in a
/// signature: a Self type pattern, the trait, its full args
/// (Self first), and that trait's assoc items by name. Used to
/// resolve `Self::Assoc` and `T::Assoc` while signatures form.
#[derive(Clone, Debug)]
pub struct AssocSrc {
    pub self_ty: Ty,
    pub trait_def: DefId,
    pub args: ArgsId,
    pub assocs: Vec<(Sym, DefId)>,
}

/// The naming scope one signature resolves types under: generic
/// parameters by name, the `Self` type, and the associated-type
/// sources of `Self` and the parameters' bounds.
/// Inference variable ids at or above this base in a resolved
/// signature type are `_` markers from `resolve_scoped`, which
/// the checker replaces with real body variables on sight.
pub const INFER_MARKER_BASE: u32 = 1 << 29;

#[derive(Clone, Debug, Default)]
pub struct Scope {
    /// Type parameter name to index in the item's `Generics`.
    pub type_params: Vec<(Sym, u32)>,
    /// Const parameter name to index in the item's `Generics`, and
    /// its declared type (`ERROR` when that did not resolve).
    pub const_params: Vec<(Sym, u32, Ty)>,
    pub self_ty: Option<Ty>,
    pub assoc_srcs: Vec<AssocSrc>,
    /// Parameter names to their types in this scope instance:
    /// `Param` types in a template, concrete types in an
    /// instance. `T::assoc` paths resolve through this.
    pub param_tys: Vec<(Sym, Ty)>,
    /// A mono instance's const parameter names to their values, for
    /// body annotations that name them (`let a: [u8; N]`); a template
    /// reads `const_params` instead.
    pub const_values: Vec<(Sym, ConstId)>,
    /// The flat type name `Self` means in a const path (`[u8; Self::N]`),
    /// set only where `Self` has no generic parameter: rustc rejects a
    /// generic `Self` in an anonymous const.
    pub self_name: Option<Sym>,
    /// When set, `_` in a written type resolves to a marker
    /// inference variable (body annotations). The counter holds
    /// the next marker id, from `INFER_MARKER_BASE`. An atomic
    /// behind an `Arc` keeps `Program` shareable across the
    /// parallel body checks.
    pub infer_cell: Option<std::sync::Arc<std::sync::atomic::AtomicU32>>,
    /// How written lifetimes resolve (W-BORROW). The default erases them,
    /// as every type the checker reads is region-erased.
    pub regions: RegionMode,
    /// Named lifetime params in scope: name and universal index (the
    /// `Region::Param` index in the item's region signature). An impl's
    /// come first, then a method's own (W-BORROW).
    pub lifetimes: Vec<(Sym, u32)>,
    /// Declared `'a: 'b` facts between those params, by universal index
    /// (`'a: 'static` has `STATIC_FACT` as its target).
    pub region_facts: Vec<(u32, u32)>,
    /// W-BORROW: a `T: 'a` bound on a named lifetime is allowed here and
    /// becomes `TypeOutlives(T, Region::Param(a))`. Set for free fns and
    /// inherent methods, whose calls prove it (borrowck `call_sig_with`);
    /// every other item keeps the L0203 reject.
    pub type_outlives: bool,
    /// The regioned `Self` type of an impl, for signatures resolved in
    /// `RegionMode::Keep` (`self_ty` stays the erased one).
    pub self_ty_regioned: Option<Ty>,
    /// The regioned associated types of the impl whose items resolve here,
    /// so `Self::Assoc` keeps its regions in a region signature.
    pub assoc_regioned: Vec<(Sym, Ty)>,
    /// A `let` annotation in a body whose regions the checker records for
    /// the borrow checker: explicit lifetimes are allowed there (W-BORROW).
    pub annotation: bool,
    /// W-BORROW, `RegionMode::Keep` only: the default object lifetime of
    /// a `dyn` type right under a reference (`&'a dyn Tr` is
    /// `&'a (dyn Tr + 'a)`); none means `'static` (`Box<dyn Tr>`).
    pub obj_default: Option<Region>,
    /// Inside the trait args of a `dyn` type (R11): the default object
    /// lifetime of a nested `dyn` is kept in every region mode (`'static`,
    /// or the reference's right above it), since it is a region slot of
    /// the outer object.
    pub dyn_args: bool,
    /// Inside `dyn Fn*(..) -> R` sugar (R11): an elided reference lifetime,
    /// and the default object lifetime under it, is the object's own
    /// late-bound region, `ty::DYN_LATE`. Nested fn pointer types
    /// (`Scope::erased`) clear it: their elided lifetimes are their own.
    pub late_elided: bool,
    /// The region an elided lifetime in the output of that sugar takes
    /// (its one input lifetime, `sugar_elision`); none in the inputs.
    pub late_out: Option<Region>,
    /// W-BORROW: inside a lifetime alias's body (`type R<'a> = &'a str`),
    /// its lifetime params and the regions the use site gives them.
    pub alias_lifetimes: Vec<(Sym, Region)>,
    /// Nesting of alias bodies being resolved (a cycle guard).
    pub alias_depth: u32,
    /// How many generic parameter defaults this resolution is nested in
    /// (`check::defaults`): a default that leads back to itself stops at
    /// a limit instead of looping.
    pub default_depth: u32,
    /// `impl Trait` nested in a fn's argument types (`&impl Tr`,
    /// `&[impl Tr]`, `Option<impl Tr>`): each node's synthetic type
    /// param (rustc APIT), set by `resolve_fn_sig`.
    pub apit: Vec<(ast::TyId, Ty)>,
    /// W-BORROW: inside a fn pointer type or `dyn Fn*` sugar, a written
    /// `&'static` keeps `Region::Static` even when regions erase, so the
    /// borrow checker sees which slots of the signature are `'static`;
    /// every other region there is elided, so late-bound.
    pub static_refs: bool,
    /// W-BORROW3: a fn pointer type here may name one lifetime of the
    /// enclosing item (`FnSig::free_slots`). Fn signatures and `let`
    /// annotations set it; nested types (`Scope::erased`) and bounds
    /// clear it, so the form is L0203 there.
    pub fn_ptr_free: bool,
    /// The regioned types of an impl's header (Self and the trait's type
    /// args): their outlives requirements are implied bounds of the impl
    /// and its methods (`check::outlives`).
    pub header_regioned: Vec<Ty>,
    /// Type items declared in enclosing function-body blocks (R18),
    /// outermost first: a name here shadows the flat module tables
    /// for a written type in this scope. The generics AST rides
    /// along for argument kinds and defaults.
    pub local_types: Vec<(Sym, AdtId, Option<ast::Generics>)>,
    /// Type aliases declared in enclosing function-body blocks,
    /// already resolved (non-generic only; a generic local alias
    /// has no entry and its name stays unknown).
    pub local_aliases: Vec<(Sym, Ty)>,
    /// Traits declared in enclosing function-body blocks.
    pub local_traits: Vec<(Sym, DefId)>,
    /// Generic parameter names of enclosing functions: an item in
    /// a body may not use them (rustc E0401). A name here that is
    /// not one of this scope's own params is that error.
    pub outer_params: Vec<Sym>,
}

/// How lifetimes resolve under a scope (W-BORROW, ARCH 5). Collect
/// resolves each signature a second time in `Keep` mode for the borrow
/// checker's region signatures (`crate::borrowck::RegionTables`).
#[derive(Clone, Debug, Default)]
pub enum RegionMode {
    /// Regions erased: `'static` and `'_` resolve to `Region::Erased`.
    #[default]
    Erase,
    /// Regions kept: `'static` is `Region::Static`; an elided or `'_`
    /// region is `elided` when set (an output under Rust's elision rules),
    /// else the next `Region::Param` from `next` (each input its own), and
    /// with neither it is the missing-lifetime error (L0202, rustc E0106).
    Keep { next: Option<std::sync::Arc<std::sync::atomic::AtomicU32>>, elided: Option<Region> },
}

impl Scope {
    /// This scope with lifetimes erased: for the insides of fn pointer and
    /// `dyn` types, whose elided lifetimes are their own (late-bound).
    pub(crate) fn erased(&self) -> Scope {
        let mut s = self.clone();
        s.regions = RegionMode::Erase;
        s.fn_ptr_free = false;
        s.dyn_args = false;
        s.late_elided = false;
        s.late_out = None;
        s
    }

    /// The parameter index of a type parameter name.
    pub fn param_of(&self, name: Sym) -> Option<u32> {
        self.type_params.iter().find(|(n, _)| *n == name).map(|(_, i)| *i)
    }
}

/// What scoped resolution needs from the program being built.
/// A generic type alias (`type R<'a> = &'a str`, `type M<K, V = u32> =
/// Vec<(K, V)>`; W-BORROW). Its body resolves at each use with the alias's
/// lifetimes mapped to the use site's regions and its type params to the
/// use site's types (`resolve_generic_alias`), so a generic Adt target
/// works too.
#[derive(Clone, Debug)]
pub struct GenericAlias {
    pub lifetimes: Vec<Sym>,
    /// Type params in order, with their defaults.
    pub type_params: Vec<(Sym, Option<ast::TyId>)>,
    pub ty: ast::TyId,
    /// The erased body, once collect validated it (`ERROR` before).
    pub erased: Ty,
    /// The alias item's token hash (driver fingerprints).
    pub body_hash: u64,
}

pub struct ResolveCx<'x> {
    /// User Adt name to its session-local (template) index.
    pub type_names: &'x crate::driver::read_cover::NameMap<AdtId>,
    /// User Adt template def and declared type/const parameter
    /// count, by session-local index.
    pub adt_info: &'x [(DefId, usize)],
    /// Lifetime param names of user Adt templates (W-BORROW).
    pub adt_lifetimes: &'x FxMap<DefId, Vec<Sym>>,
    /// User trait name to its def. Lang traits answer after it.
    pub trait_names: &'x crate::driver::read_cover::NameMap<DefId>,
    /// Type aliases by name (collect pass 1.5). A generic alias's target
    /// is over its own params (`Param(i)`).
    pub aliases: &'x crate::driver::read_cover::NameMap<Ty>,
    /// Generic type aliases (W-BORROW).
    pub generic_aliases: &'x crate::driver::read_cover::NameMap<GenericAlias>,
    pub index: &'x ImplIndex,
    pub lang: &'x LangTraits,
    /// `GenTables::item_index`.
    pub item_index: &'x FxMap<Sym, u32>,
    /// `GenTables::anon_wants`; None for std source.
    pub(crate) anon_wants: Option<&'x AnonWants>,
}

/// The anonymous consts (`ast::Ast::anon_consts`) that collect met in
/// signatures, by value id, with the type each must have when the
/// position gives one. check/const_body.rs checks each as a body.
pub(crate) type AnonWants = std::sync::Mutex<FxMap<u32, Option<ConstScalar>>>;

/// Records that collect (or a body check) met anonymous const `e`, with
/// type `want` when known (`GenTables::anon_wants`). Consts with no
/// `Ast::anon_consts` entry (literals, plain names) are not recorded.
pub(crate) fn note_anon_const(ast: &Ast, sink: Option<&AnonWants>, e: ast::ExprId, want: Option<ConstScalar>) {
    let Some(sink) = sink else { return };
    // A body's own braced const argument is recorded too: its checker
    // reads the type here (`const_body::written_anon_consts`).
    if ast.anon_const(e).is_none() && !matches!(ast.expr(e), ast::Expr::Block(_)) {
        return;
    }
    // A window check keeps its notes (check/spec.rs); `Ahead::take`
    // replays them in its body's turn.
    if crate::check::spec::note_anon(e.0, want) {
        return;
    }
    put_anon_want(sink, e.0, want);
}

/// One `anon_wants` note: the expression is known; a type, when given,
/// replaces the entry's.
fn put_anon_want(sink: &AnonWants, e: u32, want: Option<ConstScalar>) {
    crate::check::spec::wrote(crate::check::spec::tab::ANON_WANTS, &e);
    let mut m = sink.lock().unwrap_or_else(|p| p.into_inner());
    let slot = m.entry(e).or_insert(None);
    if want.is_some() {
        *slot = want;
    }
}

impl ResolveCx<'_> {
    /// A trait by a bare (one-segment) name: a local trait, or a lang
    /// trait of the Rust 2024 prelude. A non-prelude std trait needs a
    /// `use`, which the resolver's rewrite turns into its full std path
    /// (W-STD-B: a bare `Display` with no import was a false accept).
    pub fn trait_by_bare_name(&self, interner: &Interner, name: Sym) -> Option<DefId> {
        self.trait_names.get(&name).copied().or_else(|| {
            let n = interner.get(name);
            crate::ty::lang::is_prelude_trait(n).then(|| self.lang.by_name(n)).flatten()
        })
    }
    /// The template def and parameter count of one user Adt.
    pub fn adt_info_of(&self, adt: AdtId) -> (DefId, usize) {
        self.adt_info[adt.0 as usize]
    }
}

/// The undeclared-lifetime error for one written name (rustc E0261).
fn lifetime_diag_undeclared(interner: &Interner, lt: ast::Lifetime) -> Diag {
    Diag::new(
        "L0203",
        lt.span,
        format!("use of undeclared lifetime name `'{}`", interner.get(lt.name)),
        "Declare it on the item (`fn f<'a>`, `struct S<'a>`, `impl<'a>`).",
    )
}

/// The reject for a lifetime name a type alias body uses: aliases
/// declare no lifetime params yet, so the name is undeclared there.
pub fn lifetime_diag(span: Span) -> Diag {
    Diag::new(
        "L0203",
        span,
        "use of undeclared lifetime name: type aliases take no lifetime params yet",
        "Write `'static`, or spell the aliased type out where it is used.",
    )
}

/// Collects every lifetime written in type `id` that no `for<..>` binder
/// inside it declares (fx-ltdecl). The flag is true inside a fn pointer
/// type or `Fn(..)` sugar, where `'_` is that signature's own elided
/// lifetime. Used where the plain resolver drops lifetimes unchecked.
pub(crate) fn written_lifetimes(ast: &Ast, id: ast::TyId, out: &mut Vec<(ast::Lifetime, bool)>) {
    lifetimes_in_ty(ast, id, &mut Vec::new(), false, out);
}

fn lifetimes_in_ty(ast: &Ast, id: ast::TyId, bound: &mut Vec<Sym>, sig: bool, out: &mut Vec<(ast::Lifetime, bool)>) {
    let mut lt = |lt: ast::Lifetime, bound: &[Sym], out: &mut Vec<(ast::Lifetime, bool)>| {
        if !bound.contains(&lt.name) {
            out.push((lt, sig));
        }
    };
    match ast.ty(id) {
        TyExpr::Ref { lifetime, inner, .. } => {
            lifetime.iter().for_each(|&l| lt(l, bound, out));
            lifetimes_in_ty(ast, *inner, bound, sig, out);
        }
        TyExpr::Path(segs) => lifetimes_in_segs(ast, segs, bound, sig, out),
        TyExpr::Tuple(elems) => elems.iter().for_each(|&e| lifetimes_in_ty(ast, e, bound, sig, out)),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } | TyExpr::Slice(inner) | TyExpr::Paren(inner) => {
            lifetimes_in_ty(ast, *inner, bound, sig, out)
        }
        TyExpr::FnPtr { binder, inputs, ret, .. } => {
            let n = bound.len();
            bound.extend(binder.iter().map(|l| l.name));
            inputs.iter().for_each(|p| lifetimes_in_ty(ast, p.ty, bound, true, out));
            ret.iter().for_each(|&r| lifetimes_in_ty(ast, r, bound, true, out));
            bound.truncate(n);
        }
        TyExpr::Dyn { binder, bounds, lifetime } => {
            let n = bound.len();
            bound.extend(binder.iter().map(|l| l.name));
            lifetimes_in_bounds(ast, bounds, bound, sig, out);
            bound.truncate(n);
            lifetime.iter().for_each(|&l| lt(l, bound, out));
        }
        TyExpr::ImplTrait { bounds, captures } => {
            lifetimes_in_bounds(ast, bounds, bound, sig, out);
            for c in captures.iter().flat_map(|c| &c.args) {
                if let ast::UseArg::Lifetime(l) = c {
                    lt(*l, bound, out);
                }
            }
        }
        TyExpr::QPath { self_ty, trait_path, segs } => {
            lifetimes_in_ty(ast, *self_ty, bound, sig, out);
            lifetimes_in_segs(ast, trait_path, bound, sig, out);
            lifetimes_in_segs(ast, segs, bound, sig, out);
        }
        TyExpr::Unit | TyExpr::Never | TyExpr::Infer | TyExpr::MacroCall(_) => {}
    }
}

fn lifetimes_in_segs(ast: &Ast, segs: &[ast::PathSeg], bound: &mut Vec<Sym>, sig: bool, out: &mut Vec<(ast::Lifetime, bool)>) {
    for seg in segs {
        match &seg.args {
            ast::GenericArgs::Angle(args) => {
                for g in args {
                    match g {
                        ast::GenericArg::Type(t) | ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => {
                            lifetimes_in_ty(ast, *t, bound, sig, out)
                        }
                        ast::GenericArg::Lifetime(l) if !bound.contains(&l.name) => out.push((*l, sig)),
                        ast::GenericArg::Binding { kind: ast::BindingKind::Constraint(bs), .. } => {
                            lifetimes_in_bounds(ast, bs, bound, sig, out)
                        }
                        _ => {}
                    }
                }
            }
            ast::GenericArgs::Parenthesized { inputs, output } => {
                inputs.iter().chain(output).for_each(|&t| lifetimes_in_ty(ast, t, bound, true, out));
            }
            ast::GenericArgs::None => {}
        }
    }
}

fn lifetimes_in_bounds(ast: &Ast, bounds: &[TraitBound], bound: &mut Vec<Sym>, sig: bool, out: &mut Vec<(ast::Lifetime, bool)>) {
    for b in bounds {
        match b {
            TraitBound::Lifetime(l) if !bound.contains(&l.name) => out.push((*l, sig)),
            TraitBound::Lifetime(_) => {}
            TraitBound::Trait { binder, trait_ref, .. } => {
                let n = bound.len();
                bound.extend(binder.iter().map(|l| l.name));
                lifetimes_in_segs(ast, &trait_ref.path, bound, sig, out);
                bound.truncate(n);
            }
        }
    }
}

/// The first lifetime in the written type `id` of an item that is not
/// `'static`, `'_` (when `elided` allows it outside fn signatures), or a
/// name in `lts` (rustc E0261, E0401 for an outer item's lifetime; E0637
/// or E0106 for `'_`). Consts and statics pass no names and allow `'_`;
/// an alias body or an impl's associated type passes its params and
/// allows `'_` only inside fn signatures.
pub(crate) fn item_ty_lifetime_err(ast: &Ast, interner: &Interner, id: ast::TyId, lts: &[Sym], elided: bool) -> Option<Diag> {
    let mut found = Vec::new();
    written_lifetimes(ast, id, &mut found);
    found.into_iter().find_map(|(lt, sig)| match interner.get(lt.name) {
        "static" => None,
        "_" if elided || sig => None,
        "_" => Some(Diag::new("L0202", lt.span, "`'_` cannot be used here", "Write `'static` or a named lifetime parameter of the item.")),
        _ if lts.contains(&lt.name) => None,
        _ => Some(lifetime_diag_undeclared(interner, lt)),
    })
}

/// Checks one written lifetime name: `'static`, `'_`, or a lifetime
/// param the scope declares. Any other name is undeclared (rustc E0261,
/// L0203). Returns the region to record in an erased type (erased).
fn check_lifetime(interner: &Interner, scope: &Scope, lt: ast::Lifetime) -> Result<Region, Diag> {
    match interner.get(lt.name) {
        "static" | "_" => Ok(Region::Erased),
        _ if scope.lifetimes.iter().any(|(n, _)| *n == lt.name) => Ok(Region::Erased),
        _ if scope.alias_lifetimes.iter().any(|(n, _)| *n == lt.name) => Ok(Region::Erased),
        name => Err(Diag::new(
            "L0203",
            lt.span,
            format!("use of undeclared lifetime name `'{name}`"),
            "Declare it on the item (`fn f<'a>`, `struct S<'a>`, `impl<'a>`), or use `'_` or `'static`.",
        )),
    }
}

/// The region of a reference's written (or elided) lifetime under the
/// scope's region mode (W-BORROW). In a body annotation an explicit
/// `'static` is not supported yet: the annotation's region would be
/// lost, and lust must not accept a borrow rustc rejects (L0203).
pub(crate) fn scope_region(interner: &Interner, scope: &Scope, lt: Option<ast::Lifetime>, span: Span) -> Result<Region, Diag> {
    if let Some(lt) = lt
        && let Some(&(_, r)) = scope.alias_lifetimes.iter().find(|(n, _)| *n == lt.name)
    {
        return Ok(r);
    }
    let name = lt.map(|lt| interner.get(lt.name));
    if let Some(lt) = lt {
        check_lifetime(interner, scope, lt)?;
    }
    let named = lt.and_then(|lt| scope.lifetimes.iter().find(|(n, _)| *n == lt.name).map(|&(_, i)| i));
    match &scope.regions {
        RegionMode::Erase => {
            if (name == Some("static") || named.is_some()) && scope.infer_cell.is_some() && !scope.annotation {
                return Err(Diag::new(
                    "L0203",
                    lt.map_or(span, |l| l.span),
                    "an explicit lifetime in a type annotation inside a body is not supported yet",
                    "Remove the annotation and let the type be inferred, or write `'_`.",
                ));
            }
            Ok(Region::Erased)
        }
        RegionMode::Keep { next, elided } => match (name, named) {
            (Some("static"), _) => Ok(Region::Static),
            (_, Some(i)) => Ok(Region::Param(i)),
            _ => match (elided, next) {
                (Some(r), _) => Ok(*r),
                (None, Some(c)) => Ok(Region::Param(c.fetch_add(1, std::sync::atomic::Ordering::Relaxed))),
                (None, None) => Err(Diag::new(
                    "L0202",
                    span,
                    "missing lifetime specifier: elision cannot tell which input this reference borrows from",
                    "Return an owned value, take exactly one reference parameter, or borrow from `self`.",
                )),
            },
        },
    }
}

/// `scope_region` for a reference or object lifetime: inside `dyn Fn*`
/// sugar (`Scope::late_elided`) an elided one is the object's own
/// late-bound region.
fn ref_region(interner: &Interner, scope: &Scope, lt: Option<ast::Lifetime>, span: Span) -> Result<Region, Diag> {
    if scope.late_elided && lt.is_none_or(|lt| interner.get(lt.name) == "_") {
        return Ok(scope.late_out.unwrap_or(crate::ty::DYN_LATE));
    }
    scope_region(interner, scope, lt, span)
}

/// True when a written type is a `dyn` type (through parens).
fn points_to_dyn(ast: &Ast, id: ast::TyId) -> bool {
    match ast.ty(id) {
        TyExpr::Dyn { .. } => true,
        TyExpr::Paren(i) => points_to_dyn(ast, *i),
        _ => false,
    }
}

/// W-BORROW: a `dyn` type's object lifetime in region signatures
/// (`RegionMode::Keep`): the written one, else the enclosing reference's
/// (`Scope::obj_default`), else `'static`. Erased types keep only a
/// written `'static` (`resolve_dyn`), so this changes nothing check reads.
fn keep_object_lifetime(
    interner: &Interner,
    tys: &mut impl TyIntern,
    scope: &Scope,
    ty: Ty,
    bounds: &[TraitBound],
    lifetime: Option<ast::Lifetime>,
    span: Span,
) -> Result<Ty, Diag> {
    if !matches!(scope.regions, RegionMode::Keep { .. }) && !scope.dyn_args {
        return Ok(ty);
    }
    let TyKind::Dyn(b, r) = tys.kind(ty) else { return Ok(ty) };
    if r == Region::Static {
        return Ok(ty);
    }
    let written = lifetime.or_else(|| bounds.iter().find_map(|tb| if let TraitBound::Lifetime(lt) = tb { Some(*lt) } else { None }));
    // With no written bound: the enclosing reference's lifetime, else
    // `'static` in a signature or another dyn's trait args, and inferred
    // in a body annotation (rustc infers the default object lifetime
    // inside expressions).
    let region = match written {
        Some(lt) => ref_region(interner, scope, Some(lt), span)?,
        None => scope.obj_default.unwrap_or(if scope.annotation && !scope.dyn_args { Region::Erased } else { Region::Static }),
    };
    Ok(tys.intern(TyKind::Dyn(b, region)))
}

/// True when a dyn trait path's args carry a free region: a reference or
/// lifetime in angle args or bindings, or a named lifetime in `Fn` sugar.
fn dyn_args_have_regions(ast: &Ast, interner: &Interner, path: &[ast::PathSeg]) -> bool {
    fn has_ref(ast: &Ast, id: ast::TyId) -> bool {
        match ast.ty(id) {
            TyExpr::Ref { .. } | TyExpr::Dyn { .. } => true,
            TyExpr::Tuple(elems) => elems.iter().any(|&e| has_ref(ast, e)),
            TyExpr::Paren(i) | TyExpr::Slice(i) => has_ref(ast, *i),
            TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => has_ref(ast, *inner),
            TyExpr::Path(segs) => segs.iter().any(|s| match &s.args {
                GenericArgs::Angle(a) => a.iter().any(|g| match g {
                    AstArg::Lifetime(_) => true,
                    AstArg::Type(t) => has_ref(ast, *t),
                    _ => false,
                }),
                GenericArgs::Parenthesized { .. } => true,
                _ => false,
            }),
            TyExpr::FnPtr { .. } => true,
            _ => false,
        }
    }
    path.iter().any(|seg| match &seg.args {
        GenericArgs::Angle(a) => a.iter().any(|g| match g {
            AstArg::Lifetime(lt) => interner.get(lt.name) != "_",
            AstArg::Type(t) => has_ref(ast, *t),
            AstArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => has_ref(ast, *t),
            _ => false,
        }),
        // `Fn` sugar keeps its written lifetimes (R11).
        GenericArgs::Parenthesized { .. } => false,
        _ => false,
    })
}

/// The one lifetime of the enclosing item that fn pointer type `id`
/// names (W-BORROW3), if any: on a reference or as an Adt's lifetime arg,
/// through tuples, arrays, slices, raw pointers, and type args. `&'static`
/// may sit anywhere. L0203 for the cut forms: two such lifetimes, one
/// inside a nested fn pointer, `dyn`, `impl`, or `Fn` sugar type, and a
/// `'static` that is not on a reference.
fn fn_ptr_free_name(ast: &Ast, interner: &Interner, id: ast::TyId) -> Result<Option<ast::Lifetime>, Diag> {
    struct W<'x> {
        ast: &'x Ast,
        interner: &'x Interner,
        found: Option<ast::Lifetime>,
    }
    impl W<'_> {
        fn note(&mut self, lt: ast::Lifetime, plain: bool, on_ref: bool) -> Result<(), Diag> {
            let cut = |why: &str| {
                Diag::new(
                    "L0203",
                    lt.span,
                    format!("this lifetime in a fn pointer type is not supported yet: {why}"),
                    "Elide it, or name one lifetime of the enclosing fn on references and type args of the fn pointer type.",
                )
            };
            match self.interner.get(lt.name) {
                "_" => Ok(()),
                "static" if on_ref => Ok(()),
                "static" => Err(cut("a `'static` lifetime arg")),
                _ if !plain => Err(cut("it sits inside a nested fn pointer, `dyn`, or `Fn` type")),
                _ => match self.found {
                    Some(f) if f.name != lt.name => Err(cut("the type names two lifetimes")),
                    _ => {
                        self.found = Some(lt);
                        Ok(())
                    }
                },
            }
        }
        fn args(&mut self, args: &GenericArgs, plain: bool) -> Result<(), Diag> {
            match args {
                GenericArgs::Angle(a) => {
                    for g in a {
                        match g {
                            AstArg::Lifetime(lt) => self.note(*lt, plain, false)?,
                            AstArg::Type(t) => self.ty(*t, plain)?,
                            AstArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => self.ty(*t, false)?,
                            _ => {}
                        }
                    }
                    Ok(())
                }
                GenericArgs::Parenthesized { inputs, output } => inputs.iter().chain(output.iter()).try_for_each(|&t| self.ty(t, false)),
                _ => Ok(()),
            }
        }
        fn bounds(&mut self, bounds: &[TraitBound]) -> Result<(), Diag> {
            for b in bounds {
                match b {
                    TraitBound::Lifetime(lt) => self.note(*lt, false, false)?,
                    TraitBound::Trait { trait_ref, .. } => trait_ref.path.iter().try_for_each(|s| self.args(&s.args, false))?,
                }
            }
            Ok(())
        }
        fn ty(&mut self, t: ast::TyId, plain: bool) -> Result<(), Diag> {
            let ast = self.ast;
            match ast.ty(t) {
                TyExpr::Ref { lifetime, inner, .. } => {
                    if let Some(lt) = lifetime {
                        self.note(*lt, plain, true)?;
                    }
                    self.ty(*inner, plain)
                }
                TyExpr::Tuple(elems) => elems.iter().try_for_each(|&e| self.ty(e, plain)),
                TyExpr::Paren(i) | TyExpr::Slice(i) | TyExpr::Array { inner: i, .. } | TyExpr::Ptr { inner: i, .. } => self.ty(*i, plain),
                TyExpr::Path(segs) => segs.iter().try_for_each(|s| self.args(&s.args, plain)),
                TyExpr::FnPtr { inputs, ret, .. } => inputs.iter().map(|p| p.ty).chain(*ret).try_for_each(|t| self.ty(t, false)),
                TyExpr::Dyn { bounds, lifetime, .. } => {
                    if let Some(lt) = lifetime {
                        self.note(*lt, false, false)?;
                    }
                    self.bounds(bounds)
                }
                TyExpr::ImplTrait { bounds, .. } => self.bounds(bounds),
                TyExpr::QPath { self_ty, trait_path, .. } => {
                    self.ty(*self_ty, false)?;
                    trait_path.iter().try_for_each(|s| self.args(&s.args, false))
                }
                _ => Ok(()),
            }
        }
    }
    let TyExpr::FnPtr { inputs, ret, .. } = ast.ty(id) else { return Ok(None) };
    let mut w = W { ast, interner, found: None };
    for t in inputs.iter().map(|p| p.ty).chain(*ret) {
        w.ty(t, true)?;
    }
    Ok(w.found)
}

/// `FnSig::own_out` and `FnSig::out_slots` of a fn pointer type with
/// inputs `in_tys` and output `ret` (erased: `out`): the types resolve
/// again with regions kept (an elided lifetime is `Region::Bound(0)`, a
/// `for<'a>` one its own region), and each output slot that is the one
/// input region sets its bit (an elided output slot is that region). A
/// `'static` slot, and an erased one of an alias argument, does not. A
/// type parameter adds no slot (`fn(&D, usize) -> &T` is mask 1 of 1
/// slot), and so does a `_`. (0, `u8::MAX`) when the inputs have no or
/// several regions, the output holds a projection, or it has more than
/// 32 slots; (0, 0) with no output.
#[allow(clippy::too_many_arguments)]
fn fn_ptr_own_output(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    in_tys: &[ast::TyId],
    ret: Option<ast::TyId>,
    out: Ty,
) -> (u32, u8) {
    let Some(r) = ret else { return (0, 0) };
    let f = tys.flags(out);
    // A `_` adds no slot, as a type param does: what it resolves to is
    // fixed outside the pointer's binder.
    if f.contains_projection() {
        return (0, u8::MAX);
    }
    let mut ts = scope.clone();
    ts.fn_ptr_free = false;
    ts.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    let mut lts: Vec<Region> = Vec::new();
    for &t in in_tys {
        let Ok(twin) = resolve_scoped(ast, interner, known, cx, tys, t, &ts) else { return (0, u8::MAX) };
        crate::borrowck::elision_regions(tys, twin, &mut lts);
    }
    lts.retain(|r| !matches!(r, Region::Erased | Region::Static));
    lts.dedup();
    let [own] = lts[..] else { return (0, u8::MAX) };
    ts.regions = RegionMode::Keep { next: None, elided: Some(own) };
    let Ok(twin) = resolve_scoped(ast, interner, known, cx, tys, r, &ts) else { return (0, u8::MAX) };
    let mut slots: Vec<Region> = Vec::new();
    if !crate::borrowck::paired_slot_regions(cx.adt_lifetimes, tys, twin, out, &mut slots) || slots.len() > 32 {
        return (0, u8::MAX);
    }
    let mask = slots.iter().enumerate().filter(|(_, r)| **r == own).fold(0u32, |m, (k, _)| m | 1 << k);
    (mask, slots.len() as u8)
}

/// The `FnSig::free_slots` of a fn pointer type whose free lifetime is
/// `lt` (W-BORROW3): its inputs `in_tys` and output `ret` resolve again
/// with regions kept, `lt` as a marker, and each slot of the erased
/// signature (`ins`, `out`) where the marker lands sets its bit. An
/// elided output is the marker when `lt` is the one input lifetime.
#[allow(clippy::too_many_arguments)]
fn fn_ptr_free_mask(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    in_tys: &[ast::TyId],
    ret: Option<ast::TyId>,
    lt: ast::Lifetime,
    ins: &[Ty],
    out: Ty,
) -> Result<u32, Diag> {
    let marker = Region::Placeholder(u32::MAX);
    let mut ts = scope.clone();
    ts.alias_lifetimes.insert(0, (lt.name, marker));
    ts.fn_ptr_free = false;
    ts.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    let mut twin_ins = Vec::with_capacity(in_tys.len());
    for &t in in_tys {
        twin_ins.push(resolve_scoped(ast, interner, known, cx, tys, t, &ts)?);
    }
    let mut lts: Vec<Region> = Vec::new();
    for &t in &twin_ins {
        crate::borrowck::elision_regions(tys, t, &mut lts);
    }
    lts.retain(|r| *r != Region::Erased);
    let elided_out = if lts == [marker] { marker } else { Region::Bound(0) };
    ts.regions = RegionMode::Keep { next: None, elided: Some(elided_out) };
    let twin_out = match ret {
        Some(r) => resolve_scoped(ast, interner, known, cx, tys, r, &ts)?,
        None => UNIT,
    };
    let mut slots: Vec<Region> = Vec::new();
    let paired = twin_ins.iter().zip(ins).chain(std::iter::once((&twin_out, &out))).all(|(&r, &e)| crate::borrowck::paired_slot_regions(cx.adt_lifetimes, tys, r, e, &mut slots));
    let cut = |why: &str| Diag::new("L0203", lt.span, format!("this lifetime in a fn pointer type is not supported yet: {why}"), "Elide it, or use a generic `F: Fn(..)` parameter.");
    if !paired {
        return Err(cut("lust cannot place it in the signature"));
    }
    let mut mask = 0u32;
    for (j, r) in slots.into_iter().enumerate() {
        if r == marker {
            if j >= 32 {
                return Err(cut("the signature has more than 32 region places"));
            }
            mask |= 1 << j;
        }
    }
    if mask == 0 {
        return Err(cut("lust cannot place it in the signature"));
    }
    Ok(mask)
}

/// L0203 (rustc E0496) when a `for<..>` binder declares a lifetime
/// already in scope. The parser checked the rest (`parser::hrtb`).
fn binder_shadow(interner: &Interner, scope: &Scope, binder: &[ast::Lifetime]) -> Result<(), Diag> {
    match binder.iter().find(|l| scope.lifetimes.iter().any(|(n, _)| *n == l.name) || scope.alias_lifetimes.iter().any(|(n, _)| *n == l.name)) {
        Some(l) => Err(Diag::new(
            "L0203",
            l.span,
            format!("lifetime name `'{}` shadows a lifetime name that is already in scope", interner.get(l.name)),
            "Rename the binder lifetime.",
        )),
        None => Ok(()),
    }
}

/// True when fn pointer type `id` has a `for<..>` binder or names a
/// lifetime other than `'_` (`'static` included): only the scoped
/// resolver keeps those (W-BORROW3).
pub fn fn_ptr_names_lifetime(ast: &Ast, interner: &Interner, id: ast::TyId) -> bool {
    matches!(ast.ty(id), TyExpr::FnPtr { binder, .. } if !binder.is_empty()) || names_lifetime(ast, interner, id)
}

/// True when a written type names a lifetime other than `'_` anywhere
/// (fn pointer types cannot carry one yet, W-BORROW).
pub fn names_lifetime(ast: &Ast, interner: &Interner, id: ast::TyId) -> bool {
    names_lifetime_with(ast, interner, id, false)
}

/// True when a written type names a lifetime other than `'_`, not
/// counting a `'static` written on a reference (`&'static str`).
pub fn names_lifetime_beyond_static_refs(ast: &Ast, interner: &Interner, id: ast::TyId) -> bool {
    names_lifetime_with(ast, interner, id, true)
}

/// True when a written type names a type alias with no lifetime params
/// (`alias` looks one up by name) whose body holds a reference or a dyn
/// type, or an Adt with a lifetime (`type R = &'static u32`, `type A =
/// Q<'static>`). Those
/// regions are `'static` (`staticize`), so a body annotation that names
/// the alias binds them as a written `'static` would (rustc E0597 for
/// `let x: R = &local`).
pub fn names_static_alias(
    ast: &Ast,
    adt_lifetimes: &FxMap<DefId, Vec<Sym>>,
    alias: &dyn Fn(Sym) -> Option<Ty>,
    tys: &mut impl TyIntern,
    id: ast::TyId,
) -> bool {
    let mut go = |t: ast::TyId| names_static_alias(ast, adt_lifetimes, alias, tys, t);
    match ast.ty(id) {
        TyExpr::Ref { inner, .. } | TyExpr::Paren(inner) | TyExpr::Slice(inner) => go(*inner),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => go(*inner),
        TyExpr::Tuple(elems) => elems.iter().any(|&e| go(e)),
        TyExpr::Path(segs) => {
            let args: Vec<ast::TyId> = segs
                .iter()
                .flat_map(|s| match &s.args {
                    GenericArgs::Angle(a) => a.iter().filter_map(|g| if let AstArg::Type(t) = g { Some(*t) } else { None }).collect(),
                    GenericArgs::Parenthesized { inputs, output } => inputs.iter().copied().chain(*output).collect(),
                    _ => Vec::new(),
                })
                .collect();
            if args.into_iter().any(&mut go) {
                return true;
            }
            segs.len() == 1
                && alias(segs[0].name).is_some_and(|t| staticize(tys, t) != t || alias_holds_region(adt_lifetimes, tys, t, false))
        }
        _ => false,
    }
}

/// True when a written type holds a qualified path that names a lifetime
/// other than `'_` (`<Cloned<slice::Iter<'a, T>> as Iterator>::Item`).
/// `names_lifetime` does not look into one; a body annotation with one
/// still gets the outlives check (`Checker::annotation_outlives`).
pub fn qpath_names_lifetime(ast: &Ast, interner: &Interner, id: ast::TyId) -> bool {
    let go = |t: ast::TyId| qpath_names_lifetime(ast, interner, t);
    let in_args = |args: &GenericArgs| match args {
        GenericArgs::Angle(a) => a.iter().any(|g| matches!(g, AstArg::Type(t) if go(*t))),
        GenericArgs::Parenthesized { inputs, output } => inputs.iter().any(|&t| go(t)) || output.is_some_and(go),
        _ => false,
    };
    match ast.ty(id) {
        TyExpr::QPath { self_ty, trait_path, segs } => {
            let lt_args = |s: &ast::PathSeg| match &s.args {
                GenericArgs::Angle(a) => a.iter().any(|g| matches!(g, AstArg::Lifetime(lt) if interner.get(lt.name) != "_")),
                _ => false,
            };
            names_lifetime(ast, interner, *self_ty)
                || trait_path.iter().chain(segs.iter()).any(|s| lt_args(s) || in_args(&s.args))
                || go(*self_ty)
        }
        TyExpr::Ref { inner, .. } | TyExpr::Paren(inner) | TyExpr::Slice(inner) => go(*inner),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => go(*inner),
        TyExpr::Tuple(elems) => elems.iter().any(|&e| go(e)),
        TyExpr::Path(segs) => segs.iter().any(|s| in_args(&s.args)),
        TyExpr::FnPtr { inputs, ret, .. } => inputs.iter().any(|p| go(p.ty)) || ret.is_some_and(go),
        _ => false,
    }
}

/// `names_lifetime`; with `static_refs`, a `'static` written on a
/// reference does not count (`names_lifetime_beyond_static_refs`).
fn names_lifetime_with(ast: &Ast, interner: &Interner, id: ast::TyId, static_refs: bool) -> bool {
    let named = |lt: &ast::Lifetime| interner.get(lt.name) != "_";
    let go = |t: ast::TyId| names_lifetime_with(ast, interner, t, static_refs);
    let in_args = |args: &GenericArgs| match args {
        GenericArgs::Angle(a) => a.iter().any(|g| match g {
            AstArg::Lifetime(lt) => named(lt),
            AstArg::Type(t) => go(*t),
            _ => false,
        }),
        GenericArgs::Parenthesized { inputs, output } => inputs.iter().any(|&t| go(t)) || output.is_some_and(go),
        _ => false,
    };
    match ast.ty(id) {
        TyExpr::Ref { lifetime, inner, .. } => {
            lifetime.as_ref().is_some_and(|lt| named(lt) && !(static_refs && interner.get(lt.name) == "static")) || go(*inner)
        }
        TyExpr::Tuple(elems) => elems.iter().any(|&e| go(e)),
        TyExpr::Paren(i) | TyExpr::Slice(i) => go(*i),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => go(*inner),
        TyExpr::Path(segs) => segs.iter().any(|s| in_args(&s.args)),
        TyExpr::FnPtr { inputs, ret, .. } => inputs.iter().any(|p| go(p.ty)) || ret.is_some_and(go),
        TyExpr::Dyn { bounds, lifetime, .. } => {
            lifetime.as_ref().is_some_and(named)
                || bounds.iter().any(|b| match b {
                    TraitBound::Lifetime(lt) => named(lt),
                    TraitBound::Trait { trait_ref, .. } => trait_ref.path.iter().any(|s| in_args(&s.args)),
                })
        }
        _ => false,
    }
}

/// `t` (an erased signature type) with rustc's object lifetime default
/// put in where it is `'static`: a `dyn` with no written bound becomes
/// `dyn + 'static` unless it sits right under a reference, whose
/// lifetime it then takes (it stays erased). See `check_lang_method`.
fn obj_default(tys: &mut impl TyIntern, t: Ty, under_ref: bool) -> Ty {
    match tys.kind(t) {
        TyKind::Dyn(b, Region::Erased) if !under_ref => tys.intern(TyKind::Dyn(b, Region::Static)),
        TyKind::Ref(r, m, inner) => {
            let i = obj_default(tys, inner, true);
            tys.intern(TyKind::Ref(r, m, i))
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec().into_iter().map(|e| obj_default(tys, e, false)).collect();
            let id = tys.intern_tys(&elems);
            tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let e = obj_default(tys, e, false);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = obj_default(tys, e, false);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Adt(d, a) => {
            let args: Vec<GenericArg> = tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(obj_default(tys, e, false)),
                    x => x,
                })
                .collect();
            tys.mk_adt(d, &args)
        }
        _ => t,
    }
}

/// Object lifetimes put back from the written types, for the signature
/// compare of `check_lang_method`. Erased types keep only a written
/// `'static` on a dyn, so `dyn K + 'a` and an unwritten `dyn K` look the
/// same there. Walking the type with its AST (`ast_t`, None where no
/// written form lines up), each dyn region becomes: `'static` (written,
/// or rustc's default outside a reference); `Region::Param(sym)` for a
/// named lifetime, and for an elided one in the impl header (`header`:
/// each is its own early-bound lifetime, numbered down from u32::MAX by
/// `anon`); or `Erased` for an elided method lifetime (late-bound). A
/// dyn right under a reference takes that reference's lifetime. `Self`
/// (written, or unwritten where the type is the raw Self) becomes
/// `self_canon`. Equal forms agree in rustc; rustc's wider matches
/// (an elided parameter lifetime) stay rejects.
#[allow(clippy::too_many_arguments)]
fn canon_dyn(
    p: &mut Program,
    ast_t: Option<ast::TyId>,
    t: Ty,
    outer: Option<Region>,
    header: bool,
    self_raw: Ty,
    self_canon: Option<Ty>,
    anon: &mut u32,
) -> Ty {
    let mut ast_t = ast_t;
    while let Some(TyExpr::Paren(inner)) = ast_t.map(|a| p.ast.ty(a)) {
        ast_t = Some(*inner);
    }
    let node = ast_t.map(|a| p.ast.ty(a).clone());
    let is_self_path = matches!(&node, Some(TyExpr::Path(segs)) if segs.len() == 1 && segs[0].name == p.known.self_type);
    if let Some(sc) = self_canon
        && t == self_raw
        && (node.is_none() || is_self_path)
    {
        return sc;
    }
    let lt_region = |p: &Program, lt: ast::Lifetime, anon: &mut u32| match p.interner.get(lt.name) {
        "static" => Region::Static,
        "_" if header => {
            *anon -= 1;
            Region::Param(*anon)
        }
        "_" => Region::Erased,
        _ => Region::Param(lt.name.0),
    };
    match p.tys.kind(t) {
        TyKind::Dyn(b, Region::Erased) => {
            let written = match &node {
                Some(TyExpr::Dyn { bounds, lifetime, .. }) => {
                    lifetime.or_else(|| bounds.iter().find_map(|b| if let TraitBound::Lifetime(lt) = b { Some(*lt) } else { None }))
                }
                _ => None,
            };
            let r = match written {
                Some(lt) => lt_region(p, lt, anon),
                None => outer.unwrap_or(Region::Static),
            };
            p.tys.intern(TyKind::Dyn(b, r))
        }
        TyKind::Ref(r, m, inner) => {
            let (inner_ast, ref_r) = match &node {
                Some(TyExpr::Ref { lifetime, inner, .. }) => {
                    let ref_r = match lifetime {
                        Some(lt) => lt_region(p, *lt, anon),
                        None if header => {
                            *anon -= 1;
                            Region::Param(*anon)
                        }
                        None => Region::Erased,
                    };
                    (Some(*inner), ref_r)
                }
                _ => (None, Region::Erased),
            };
            let i = canon_dyn(p, inner_ast, inner, Some(ref_r), header, self_raw, self_canon, anon);
            p.tys.intern(TyKind::Ref(r, m, i))
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            let asts: Vec<Option<ast::TyId>> = match &node {
                Some(TyExpr::Tuple(xs)) if xs.len() == elems.len() => xs.iter().map(|&x| Some(x)).collect(),
                _ => vec![None; elems.len()],
            };
            let out: Vec<Ty> = elems.iter().zip(asts).map(|(&e, a)| canon_dyn(p, a, e, None, header, self_raw, self_canon, anon)).collect();
            let id = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let a = if let Some(TyExpr::Array { inner, .. }) = &node { Some(*inner) } else { None };
            let e = canon_dyn(p, a, e, None, header, self_raw, self_canon, anon);
            p.tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let a = if let Some(TyExpr::Slice(inner)) = &node { Some(*inner) } else { None };
            let e = canon_dyn(p, a, e, None, header, self_raw, self_canon, anon);
            p.tys.intern(TyKind::Slice(e))
        }
        TyKind::Adt(d, a) => {
            let args: Vec<GenericArg> = p.tys.args(a).to_vec();
            let n_tys = args.iter().filter(|g| g.as_ty().is_some()).count();
            // The written type args line up only when they are all there.
            let written: Vec<ast::TyId> = match &node {
                Some(TyExpr::Path(segs)) => match segs.last().map(|s| &s.args) {
                    Some(GenericArgs::Angle(xs)) => xs.iter().filter_map(|g| if let AstArg::Type(t) = g { Some(*t) } else { None }).collect(),
                    _ => Vec::new(),
                },
                _ => Vec::new(),
            };
            let mut asts = (written.len() == n_tys).then(|| written.into_iter());
            let out: Vec<GenericArg> = args
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => {
                        let a = asts.as_mut().and_then(|it| it.next());
                        GenericArg::Ty(canon_dyn(p, a, e, None, header, self_raw, self_canon, anon))
                    }
                    x => x,
                })
                .collect();
            p.tys.mk_adt(d, &out)
        }
        _ => t,
    }
}

/// True when a lang trait impl method's signature type `got` may stand
/// for the trait's `want` (both from `canon_dyn`): equal, or different
/// only in dyn object lifetimes where rustc's subtyping allows it. In the
/// return (`ret`) got must be a subtype, so a `'static` object fits any
/// want. In a parameter want must be a subtype of got: a `'static` want
/// object fits, and so does an elided got object when `free` (its
/// late-bound lifetime can be as short as needed). Only covariant places
/// take part (`cov`: shared references, `Box`, tuples, arrays, slices);
/// anywhere else the types must be equal.
#[allow(clippy::too_many_arguments)]
fn dyn_sub_ok(tys: &impl TyIntern, want: Ty, got: Ty, ret: bool, cov: bool, free: bool, boxed: DefId) -> bool {
    if want == got {
        return true;
    }
    let go = |w: Ty, g: Ty, c: bool| dyn_sub_ok(tys, w, g, ret, c, free, boxed);
    match (tys.kind(want), tys.kind(got)) {
        (TyKind::Dyn(bw, rw), TyKind::Dyn(bg, rg)) if bw == bg && cov => {
            if ret { rg == Region::Static } else { rw == Region::Static || (free && rg == Region::Erased) }
        }
        (TyKind::Ref(r1, m1, a), TyKind::Ref(r2, m2, b)) if r1 == r2 && m1 == m2 => go(a, b, cov && m1 == Mut::Shared),
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (a, b) = (tys.tys_of(a), tys.tys_of(b));
            a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| go(x, y, cov))
        }
        (TyKind::Array(a, n), TyKind::Array(b, m)) if n == m => go(a, b, cov),
        (TyKind::Slice(a), TyKind::Slice(b)) => go(a, b, cov),
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (a1, a2) = (tys.args(a1), tys.args(a2));
            a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(&x, &y)| match (x, y) {
                    (GenericArg::Ty(x), GenericArg::Ty(y)) => go(x, y, cov && d1 == boxed),
                    _ => x == y,
                })
        }
        _ => false,
    }
}

/// True when `t` holds a reference anywhere.
fn mentions_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
        TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_ref(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_ref(tys, e)),
        TyKind::Adt(_, a) | TyKind::Projection(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_ref(tys, e))),
        TyKind::Dyn(..) | TyKind::FnPtr(_) | TyKind::Opaque(..) | TyKind::Param(_) => true,
        _ => false,
    }
}

/// True when an alias body `t` (erased) holds a region: a reference, or
/// (`adt_only`: only) an Adt with lifetime params (`Q<'static>`,
/// `Chars<'static>`), which an alias body can only write as `'static`.
pub(crate) fn alias_holds_region(adt_lifetimes: &FxMap<DefId, Vec<Sym>>, tys: &impl TyIntern, t: Ty, adt_only: bool) -> bool {
    let go = |e: Ty| alias_holds_region(adt_lifetimes, tys, e, adt_only);
    match tys.kind(t) {
        TyKind::Ref(_, _, e) => !adt_only || go(e),
        TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => go(e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| go(e)),
        TyKind::Adt(_, a) => {
            crate::borrowck::adt_region_count(adt_lifetimes, tys, t) > 0 || tys.args(a).iter().any(|g| g.as_ty().is_some_and(go))
        }
        _ => false,
    }
}

/// The resolved body of an alias with no lifetime params at one use
/// (W-BORROW). In a region signature or a recorded body annotation
/// (`Ctx::annotation_has_regions`) its regions are `'static`: `staticize`,
/// or for a body with an Adt lifetime (`type A = Q<'static>`, which an
/// erased type cannot carry) the module alias's written `body` resolved
/// again with regions kept. Elsewhere in a body (a cast target, a
/// turbofish) the checker would erase them and the borrow checker never
/// see them, so an alias that holds a region is the same reject as a
/// written `'static` there (but inside a fn pointer type, where both keep
/// `'static`), and so is a block-local alias over an Adt
/// lifetime in an annotation.
#[allow(clippy::too_many_arguments)]
fn alias_at_use(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    alias_ty: Ty,
    body: AliasBody,
    span: Span,
) -> Result<Ty, Diag> {
    let not_here = Diag::new(
        "L0203",
        span,
        "a type alias with a `'static` lifetime is not supported here inside a body yet",
        "Write the aliased type with `'_`, or bind the value with a `let` annotation that names a module-level alias.",
    );
    match scope.regions {
        RegionMode::Keep { .. } if alias_holds_region(cx.adt_lifetimes, tys, alias_ty, true) => match body {
            AliasBody::Module(Some(b)) => {
                resolve_scoped(ast, interner, known, cx, tys, b, &Scope { regions: scope.regions.clone(), ..Scope::default() })
            }
            AliasBody::Module(None) => Ok(staticize(tys, alias_ty)),
            AliasBody::Local => Err(not_here),
        },
        RegionMode::Keep { .. } => Ok(staticize(tys, alias_ty)),
        // Inside a fn pointer or `dyn Fn` type a written `&'static` keeps
        // its region (`Scope::static_refs`); so does an alias's.
        RegionMode::Erase if scope.static_refs => Ok(staticize(tys, alias_ty)),
        RegionMode::Erase if scope.infer_cell.is_some() && !scope.annotation => {
            if alias_holds_region(cx.adt_lifetimes, tys, alias_ty, false) { Err(not_here) } else { Ok(alias_ty) }
        }
        RegionMode::Erase => Ok(alias_ty),
    }
}

/// Where an alias used in `alias_at_use` comes from: a module alias with
/// its written body when it has no generic params, or a block-local one.
enum AliasBody {
    Module(Option<ast::TyId>),
    Local,
}

/// The written body of the module type alias `name`, for `alias_at_use`.
fn module_alias_body(ast: &Ast, cx: &ResolveCx, name: Sym) -> Option<ast::TyId> {
    match &ast.items.get(*cx.item_index.get(&name)? as usize)?.kind {
        ast::ItemKind::Type(a) if a.name == name && a.generics.params.is_empty() => Some(a.ty),
        _ => None,
    }
}

/// `t` with every reference region and dyn object lifetime `'static`:
/// the region form of a type alias body, which may only use `'static`
/// (W-BORROW, increment 1), and of a `thread_local!` value type
/// (check/tls.rs), where every elided lifetime is `'static`.
pub(crate) fn staticize(tys: &mut impl TyIntern, t: Ty) -> Ty {
    match tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            let i = staticize(tys, inner);
            tys.intern(TyKind::Ref(Region::Static, m, i))
        }
        TyKind::Dyn(b, _) => tys.intern(TyKind::Dyn(b, Region::Static)),
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec().into_iter().map(|e| staticize(tys, e)).collect();
            let id = tys.intern_tys(&elems);
            tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let e = staticize(tys, e);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = staticize(tys, e);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Adt(d, a) => {
            let args: Vec<GenericArg> = tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(staticize(tys, e)),
                    x => x,
                })
                .collect();
            tys.mk_adt(d, &args)
        }
        _ => t,
    }
}

/// Resolves one generic argument list against a declared parameter
/// list. Written arguments follow declared order (lifetime
/// parameters do not exist in this subset's generics, so written
/// lifetimes only appear on types whose parameters are all
/// erased, like `Formatter<'_>`, where they are checked and
/// dropped). Missing trailing arguments are an error: parameter
/// defaults are not supported yet.
fn resolve_generic_args(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    args: &[AstArg],
    param_is_const: &[bool],
    min_params: usize,
    span: Span,
    what: &str,
) -> Result<Vec<GenericArg>, Diag> {
    let n_params = param_is_const.len();
    let mut out: Vec<GenericArg> = Vec::new();
    // The index among type/const arguments (lifetimes do not count).
    let mut vi = 0usize;
    for a in args {
        match a {
            AstArg::Type(t) => {
                // A bare path in a const parameter's position names
                // a const, not a type (`Arr<N>`): the parser cannot
                // tell, so the declared kind decides here.
                if param_is_const.get(vi).copied().unwrap_or(false) {
                    out.push(GenericArg::Const(resolve_const_path_arg(ast, interner, known, cx, tys, scope, *t, span)?));
                } else {
                    out.push(GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?));
                }
                vi += 1;
            }
            AstArg::Lifetime(lt) => {
                check_lifetime(interner, scope, *lt)?;
                out.push(GenericArg::Lifetime(Region::Erased));
            }
            AstArg::Const(e) => {
                // A const value in a type parameter's slot is a kind
                // error (rustc E0747), never a type argument.
                if param_is_const.get(vi).copied() == Some(false) {
                    return Err(Diag::new(
                        "L0110",
                        span,
                        "constant provided when a type was expected",
                        "Write a type for this parameter, such as `u8`.",
                    ));
                }
                out.push(GenericArg::Const(resolve_const_arg(ast, interner, known, tys, scope, *e, span)?));
                vi += 1;
            }
            AstArg::Binding { span, .. } => {
                return Err(Diag::new(
                    "L0110",
                    *span,
                    format!("associated bindings are not allowed on `{what}`"),
                    "Write the binding on a trait bound instead.",
                ));
            }
        }
    }
    // Erased lifetime arguments do not count against the declared
    // type/const parameters (declared lifetimes are rejected when
    // the item's generics are built).
    // Trailing params with defaults (`min_params` and up) may be left
    // out; the caller fills them (`check::defaults`).
    let n_value_args = out.iter().filter(|g| !matches!(g, GenericArg::Lifetime(_))).count();
    if n_value_args > n_params || n_value_args < min_params {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{what}` takes {n_params} generic argument(s), but {n_value_args} were given"),
            "Match the number of parameters in the definition.",
        ));
    }
    Ok(out)
}

/// True when the integer `v` (two's complement in a u128, as
/// `ConstKind::Int` holds it) is a value of `it`.
pub(crate) fn const_int_fits(v: u128, it: IntTy) -> bool {
    // Every 128-bit pattern is a value of a 128-bit type; the
    // signed read below would call u128 values past 2^127 negative.
    if it.bits() >= 128 {
        return true;
    }
    let v = v as i128;
    if it.signed() {
        let max = (it.max128() as i128).max(0);
        v >= -max - 1 && v <= max
    } else {
        v >= 0 && (v as u128) <= it.max128()
    }
}

/// Written const generic args of a type path against the declared
/// types of its const params in `g` (an integer type, `bool`, or
/// `char`): rustc's E0308 and out-of-range literal errors, on the
/// evaluated value and on the written expression's type
/// (`ConstTyper`; a const param passes when its declared type is the
/// same).
#[allow(clippy::too_many_arguments)]
fn check_const_arg_types(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    g: &ast::Generics,
    written: &[AstArg],
    args: &[GenericArg],
    span: Span,
) -> Result<(), Diag> {
    let decls = g.params.iter().filter(|p| !matches!(p, ast::GenericParam::Lifetime { .. }));
    let vals = args.iter().filter(|a| !matches!(a, GenericArg::Lifetime(_)));
    let forms = written.iter().filter(|a| !matches!(a, AstArg::Lifetime(_)));
    for ((param, arg), form) in decls.zip(vals).zip(forms) {
        let (ast::GenericParam::Const { ty, .. }, GenericArg::Const(c)) = (param, arg) else { continue };
        let mut typer = ConstTyper { ast, interner, known, cx, tys: &mut *tys, scope, lets: Vec::new() };
        let want = typer.written(*ty);
        if let AstArg::Const(e) = form {
            note_anon_const(ast, cx.anon_wants, *e, want);
        }
        let Some(want) = want else { continue };
        let typed = match form {
            AstArg::Const(e) => typer.expr(*e, Some(want)).is_ok(),
            // A bare name in a const position (`Arr<N>`).
            AstArg::Type(t) => match ast.ty(*t) {
                TyExpr::Path(segs) if segs.len() == 1 => typer.name(segs[0].name).is_none_or(|s| s == want),
                _ => true,
            },
            _ => true,
        };
        if !typed || !want.holds(tys, *c) {
            return Err(const_mismatch(want, span, "this const argument"));
        }
    }
    Ok(())
}

/// A const generic argument the parser read as a type path
/// (`Arr<N>`): a const parameter of the enclosing item, or a
/// free const item. Rust reads a bare generic argument as a
/// type first: only a single-segment path that names no type
/// in scope may name a const (multi-segment const paths need
/// braces, `Arr<{ S::N }>`).
fn resolve_const_path_arg(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    t: ast::TyId,
    span: Span,
) -> Result<ConstId, Diag> {
    let err = || {
        Diag::new(
            "L0110",
            span,
            "const argument must be a literal or a const parameter",
            "Use a literal such as `3`, or braces around a const path such as `{ S::N }`.",
        )
    };
    let TyExpr::Path(segs) = ast.ty(t) else { return Err(err()) };
    let [seg] = segs.as_slice() else { return Err(err()) };
    if seg.has_args() {
        return Err(err());
    }
    // A name that resolves as a type here is a type argument,
    // never a const (rustc E0747 in this position).
    if cx.type_names.contains_key(&seg.name)
        || cx.aliases.contains_key(&seg.name)
        || cx.generic_aliases.contains_key(&seg.name)
        || scope.param_tys.iter().any(|(n, _)| *n == seg.name)
        || seg.name == known.self_type
    {
        return Err(err());
    }
    if let Some(&(_, c)) = scope.const_values.iter().find(|(n, _)| *n == seg.name)
        && !ast.is_parenthesized_ty(t)
    {
        return Ok(c);
    }
    if let Some(&(_, i, _)) = scope.const_params.iter().find(|(n, ..)| *n == seg.name) {
        // `(N)` is a const operation on the parameter, not the
        // parameter itself.
        if ast.is_parenthesized_ty(t) {
            return Err(Diag::new(
                "L0110",
                span,
                "generic parameters may not be used in const operations",
                "Write the const parameter without parentheses.",
            ));
        }
        return Ok(tys.intern_const(ConstKind::Param(i)));
    }
    match crate::check::collect::named_const_kind(ast, interner, known, seg.name, span) {
        Some(k) => Ok(tys.intern_const(k)),
        None => Err(err()),
    }
}

/// A const generic argument or array length in signature form:
/// a literal value, or a const parameter reference.
pub(crate) fn resolve_const_arg(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    scope: &Scope,
    e: ast::ExprId,
    span: Span,
) -> Result<ConstId, Diag> {
    match ast.expr(e) {
        // `{ N }`: a const parameter in braces is the parameter.
        ast::Expr::Block(b)
            if ast.block(*b).stmts.is_empty()
                && ast.block(*b).tail.is_some_and(|t| matches!(ast.expr(t), ast::Expr::Path(segs) if segs.len() == 1 && scope.const_params.iter().any(|(n, ..)| *n == segs[0].name))) =>
        {
            resolve_const_arg(ast, interner, known, tys, scope, ast.block(*b).tail.unwrap(), span)
        }
        ast::Expr::Path(segs) if segs.len() == 1 => {
            if let Some(&(_, c)) = scope.const_values.iter().find(|(n, _)| *n == segs[0].name)
                && !ast.is_parenthesized(e)
            {
                return Ok(c);
            }
            if let Some(&(_, i, _)) = scope.const_params.iter().find(|(n, ..)| *n == segs[0].name) {
                // `(N)` is a const operation on the parameter, not
                // the parameter itself (rustc: generic parameters
                // may not be used in const operations).
                if ast.is_parenthesized(e) {
                    return Err(Diag::new(
                        "L0110",
                        span,
                        "generic parameters may not be used in const operations",
                        "Write the const parameter without parentheses.",
                    ));
                }
                return Ok(tys.intern_const(ConstKind::Param(i)));
            }
            // A named const item evaluates like the literal forms below.
            match crate::check::collect::eval_array_len_in(ast, interner, known, e, scope.self_name) {
                Some(v) => Ok(tys.intern_const(ConstKind::Int(v))),
                None => {
                    Err(Diag::new("L0110", span, "const argument must be a literal or a const parameter", "Use a literal such as `3`."))
                }
            }
        }
        ast::Expr::Bool(b) => Ok(tys.intern_const(ConstKind::Bool(*b))),
        ast::Expr::Char(c) => Ok(tys.intern_const(ConstKind::Char(*c))),
        _ => match crate::check::collect::eval_array_len_in(ast, interner, known, e, scope.self_name) {
            Some(v) => Ok(tys.intern_const(ConstKind::Int(v))),
            None => Err(Diag::new("L0110", span, "const argument must be a constant integer", "Write a literal such as `3`.")),
        },
    }
}

/// The type of a const generic value or of an array length: an
/// integer type, `bool`, or `char` (rustc allows no other const
/// param type).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ConstScalar {
    Int(IntTy),
    Bool,
    Char,
}

impl ConstScalar {
    pub(crate) fn of(tys: &impl TyIntern, t: Ty) -> Option<ConstScalar> {
        match tys.kind(t) {
            TyKind::Int(it) => Some(ConstScalar::Int(it)),
            TyKind::Bool => Some(ConstScalar::Bool),
            TyKind::Char => Some(ConstScalar::Char),
            _ => None,
        }
    }

    /// The type itself.
    pub(crate) fn ty(self) -> Ty {
        match self {
            ConstScalar::Int(it) => crate::ty::int(it),
            ConstScalar::Bool => crate::ty::BOOL,
            ConstScalar::Char => crate::ty::CHAR,
        }
    }

    fn name(self) -> &'static str {
        match self {
            ConstScalar::Int(it) => it.name(),
            ConstScalar::Bool => "bool",
            ConstScalar::Char => "char",
        }
    }

    /// True when an evaluated const is a value of this type. Params
    /// and inference variables pass (their types are checked where
    /// they are written).
    fn holds(self, tys: &impl TyIntern, c: ConstId) -> bool {
        match (tys.const_kind(c), self) {
            (ConstKind::Int(v), ConstScalar::Int(it)) => const_int_fits(v, it),
            (ConstKind::Bool(_), ConstScalar::Bool) | (ConstKind::Char(_), ConstScalar::Char) => true,
            (ConstKind::Int(_) | ConstKind::Bool(_) | ConstKind::Char(_), _) => false,
            _ => true,
        }
    }
}

/// What `ConstTyper` knows about one expression's type: `Ok(Some)` a
/// type it certainly has, `Ok(None)` one that adapts to the expected
/// type (an unsuffixed integer literal) or that the walk cannot tell,
/// and `Err` an expression that cannot have the expected type.
type ConstTyped = Result<Option<ConstScalar>, ()>;

fn const_want(want: Option<ConstScalar>, have: ConstScalar) -> ConstTyped {
    match want {
        Some(w) if w != have => Err(()),
        _ => Ok(Some(have)),
    }
}

/// Types a const expression in signature form (an array length, a
/// const generic argument, a const param default) as rustc types the
/// anonymous const: E0308, and E0600 for `-` on an unsigned type. The
/// untyped scalar evaluator in collect computes the value; this walk
/// covers the same forms for their types: literal suffixes, bool and
/// char literals, const params and const items by declared type,
/// casts, const fn calls, operators, blocks with lets, and `if`.
struct ConstTyper<'x, 'c, T: TyIntern> {
    ast: &'x Ast,
    interner: &'x Interner,
    known: &'x Known,
    cx: &'x ResolveCx<'c>,
    tys: &'x mut T,
    scope: &'x Scope,
    lets: Vec<(Sym, Option<ConstScalar>)>,
}

impl<T: TyIntern> ConstTyper<'_, '_, T> {
    /// The scalar a written type names (a const item's or a const fn
    /// param's declared type), resolved outside any generic scope.
    fn written(&mut self, t: ast::TyId) -> Option<ConstScalar> {
        let ty = resolve_scoped(self.ast, self.interner, self.known, self.cx, self.tys, t, &Scope::default()).ok()?;
        ConstScalar::of(self.tys, ty)
    }

    fn expr(&mut self, e: ast::ExprId, want: Option<ConstScalar>) -> ConstTyped {
        use ast::{Expr, UnOp};
        use ConstScalar as S;
        let ast = self.ast;
        match ast.expr(e) {
            // A literal must fit the type that pins it (rustc's
            // overflowing_literals): the value check in `holds`
            // cannot see it, since a magnitude past `i128::MAX`
            // wraps to an in-range bit pattern.
            Expr::Int(mag, None) => match want {
                Some(S::Int(it)) if *mag > it.max128() => Err(()),
                None | Some(S::Int(_)) => Ok(None),
                Some(_) => Err(()),
            },
            Expr::Int(mag, Some(sfx)) => {
                let it = IntTy::from_suffix(*sfx);
                if *mag > it.max128() {
                    return Err(());
                }
                const_want(want, S::Int(it))
            }
            Expr::Bool(_) => const_want(want, S::Bool),
            Expr::Char(_) => const_want(want, S::Char),
            Expr::Float(_) | Expr::Str(_) | Expr::Unit => {
                if want.is_some() {
                    Err(())
                } else {
                    Ok(None)
                }
            }
            Expr::Block(b) | Expr::ConstBlock(b) => self.block(*b, want),
            Expr::Unary { op: UnOp::Neg, expr } => {
                // A negated literal may reach one past the max
                // (the type's min): check its magnitude here, where
                // the negation is visible.
                if let Expr::Int(mag, sfx) = ast.expr(*expr) {
                    let mag = *mag;
                    return match (sfx, want) {
                        (Some(s), _) => {
                            let it = IntTy::from_suffix(*s);
                            if !it.signed() || mag > it.max128() + 1 {
                                return Err(());
                            }
                            const_want(want, S::Int(it))
                        }
                        (None, Some(S::Int(it))) => {
                            if it.signed() && mag <= it.max128() + 1 { Ok(None) } else { Err(()) }
                        }
                        (None, Some(_)) => Err(()),
                        (None, None) => Ok(None),
                    };
                }
                let unsigned = |s: Option<S>| match s {
                    Some(S::Int(it)) => !it.signed(),
                    Some(_) => true,
                    None => false,
                };
                if unsigned(want) {
                    return Err(());
                }
                let t = self.expr(*expr, want)?;
                if unsigned(t) { Err(()) } else { Ok(t) }
            }
            Expr::Unary { op: UnOp::Not, expr } => {
                if want == Some(S::Char) {
                    return Err(());
                }
                let t = self.expr(*expr, want)?;
                if t == Some(S::Char) { Err(()) } else { Ok(t) }
            }
            Expr::Binary { op, lhs, rhs } => self.binary(*op, *lhs, *rhs, want),
            Expr::Cast { expr, ty } => {
                self.expr(*expr, None)?;
                match self.written(*ty) {
                    Some(s) => const_want(want, s),
                    None => Ok(None),
                }
            }
            Expr::If { cond, then, els } => {
                self.expr(*cond, Some(S::Bool))?;
                let t = self.block(*then, want)?;
                match els {
                    Some(x) => {
                        let u = self.expr(*x, want.or(t))?;
                        match (t, u) {
                            (Some(a), Some(b)) if a != b => Err(()),
                            _ => Ok(t.or(u)),
                        }
                    }
                    None if want.is_some() => Err(()),
                    None => Ok(None),
                }
            }
            Expr::Path(segs) => {
                let t = match segs.as_slice() {
                    [seg] if !seg.has_args() => self.name(seg.name),
                    [owner, item] if !owner.has_args() => match self.known.int_ty(owner.name) {
                        Some(it) => match self.interner.get(item.name) {
                            "MAX" | "MIN" => Some(S::Int(it)),
                            "BITS" => Some(S::Int(IntTy::U32)),
                            _ => None,
                        },
                        None => self.assoc_const(owner.name, item.name),
                    },
                    _ => None,
                };
                match t {
                    Some(s) => const_want(want, s),
                    None => Ok(None),
                }
            }
            Expr::Call { callee, args } => self.call(*callee, args, want),
            _ => Ok(None),
        }
    }

    fn binary(&mut self, op: ast::BinOp, lhs: ast::ExprId, rhs: ast::ExprId, want: Option<ConstScalar>) -> ConstTyped {
        use ConstScalar as S;
        use ast::BinOp as B;
        let same = |a: Option<S>, b: Option<S>| match (a, b) {
            (Some(x), Some(y)) if x != y => Err(()),
            _ => Ok(a.or(b)),
        };
        match op {
            B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge => {
                let l = self.expr(lhs, None)?;
                let r = self.expr(rhs, l)?;
                same(l, r)?;
                const_want(want, S::Bool)
            }
            B::And | B::Or => {
                self.expr(lhs, Some(S::Bool))?;
                self.expr(rhs, Some(S::Bool))?;
                const_want(want, S::Bool)
            }
            B::Shl | B::Shr => {
                let int = |s: Option<S>| matches!(s, None | Some(S::Int(_)));
                if !int(want) {
                    return Err(());
                }
                let l = self.expr(lhs, want)?;
                let r = self.expr(rhs, None)?;
                if int(l) && int(r) { Ok(l) } else { Err(()) }
            }
            // Arithmetic and bit operators: both sides and the result
            // share one type; `&`, `|`, and `^` also take bool.
            _ => {
                let bit = matches!(op, B::BitAnd | B::BitOr | B::BitXor);
                let ok = |s: Option<S>| match s {
                    Some(S::Char) => false,
                    Some(S::Bool) => bit,
                    _ => true,
                };
                if !ok(want) {
                    return Err(());
                }
                let l = self.expr(lhs, want)?;
                let r = self.expr(rhs, want.or(l))?;
                let t = same(l, r)?;
                if ok(t) { Ok(t) } else { Err(()) }
            }
        }
    }

    fn block(&mut self, b: ast::BlockId, want: Option<ConstScalar>) -> ConstTyped {
        let saved = self.lets.len();
        let out = self.block_body(b, want);
        self.lets.truncate(saved);
        out
    }

    fn block_body(&mut self, b: ast::BlockId, want: Option<ConstScalar>) -> ConstTyped {
        use crate::ast::{Pat, Stmt};
        let ast = self.ast;
        let block = ast.block(b);
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, ty, init, .. } => {
                    let Pat::Binding { name, .. } = ast.pat(*pat) else { return Ok(None) };
                    let declared = ty.and_then(|t| self.written(t));
                    let t = match init {
                        Some(i) => self.expr(*i, declared)?,
                        None => None,
                    };
                    self.lets.push((*name, declared.or(t)));
                }
                Stmt::Expr { expr, .. } => {
                    self.expr(*expr, None)?;
                }
                _ => return Ok(None),
            }
        }
        match block.tail {
            Some(t) => self.expr(t, want),
            None if want.is_some() => Err(()),
            None => Ok(None),
        }
    }

    /// A bare name: a block binding, a const param of the item, or a
    /// free const item (the first of its name, as the evaluator reads).
    fn name(&mut self, name: Sym) -> Option<ConstScalar> {
        if let Some(&(_, t)) = self.lets.iter().rev().find(|(n, _)| *n == name) {
            return t;
        }
        if let Some(&(_, _, t)) = self.scope.const_params.iter().find(|(n, ..)| *n == name) {
            return ConstScalar::of(self.tys, t);
        }
        let ast = self.ast;
        let ty = ast.items.iter().find_map(|item| match &item.kind {
            ast::ItemKind::Const(c) if c.name == Some(name) => Some(c.ty),
            _ => None,
        })?;
        self.written(ty)
    }

    /// An inherent associated const by flat type name, when every
    /// impl that defines it declares the same type.
    fn assoc_const(&mut self, owner: Sym, name: Sym) -> Option<ConstScalar> {
        let ast = self.ast;
        let mut found = None;
        for item in &ast.items {
            let ast::ItemKind::Impl(imp) = &item.kind else { continue };
            if imp.trait_ref.is_some() {
                continue;
            }
            let TyExpr::Path(segs) = ast.ty(imp.self_ty) else { continue };
            if segs.first().map(|s| s.name) != Some(owner) {
                continue;
            }
            for c in imp.consts.iter().filter(|c| c.name == name) {
                let s = self.written(c.ty)?;
                if found.is_some_and(|f| f != s) {
                    return None;
                }
                found = Some(s);
            }
        }
        found
    }

    /// A call to a non-generic const fn (the evaluator's call form):
    /// its args against the declared param types, its declared return.
    fn call(&mut self, callee: ast::ExprId, args: &[ast::ExprId], want: Option<ConstScalar>) -> ConstTyped {
        let ast = self.ast;
        let ast::Expr::Path(segs) = ast.expr(callee) else { return Ok(None) };
        let [seg] = segs.as_slice() else { return Ok(None) };
        let def = ast.items.iter().find_map(|item| match &item.kind {
            ast::ItemKind::Fn(def)
                if def.name == seg.name && def.qual.is_const && def.self_param.is_none() && def.params.len() == args.len() =>
            {
                Some(def)
            }
            _ => None,
        });
        let Some(def) = def else { return Ok(None) };
        if !def.generics.params.is_empty() {
            return Ok(None);
        }
        for (param, &a) in def.params.iter().zip(args) {
            let p = self.written(param.ty);
            self.expr(a, p)?;
        }
        match def.ret {
            Some(t) => match self.written(t) {
                Some(s) => const_want(want, s),
                None => Ok(None),
            },
            None if want.is_some() => Err(()),
            None => Ok(None),
        }
    }
}

/// Checks one const expression in signature form against the type it
/// must have: `usize` for an array length, the declared type for a
/// const argument (`ConstTyper`), and its evaluated value `c` against
/// that type's range.
#[allow(clippy::too_many_arguments)]
pub(crate) fn check_const_expr_ty(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    e: ast::ExprId,
    c: ConstId,
    want: ConstScalar,
    span: Span,
    what: &str,
) -> Result<(), Diag> {
    note_anon_const(ast, cx.anon_wants, e, Some(want));
    let mut typer = ConstTyper { ast, interner, known, cx, tys: &mut *tys, scope, lets: Vec::new() };
    if typer.expr(e, Some(want)).is_ok() && want.holds(tys, c) {
        return Ok(());
    }
    Err(const_mismatch(want, span, what))
}

/// The declared type of a bare name in a const position (`f::<L>`,
/// `Arr<N>`): a const param of `scope`, or a free const item. None
/// when it names neither or its type is no const scalar.
#[allow(clippy::too_many_arguments)]
pub(crate) fn const_name_ty(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    name: Sym,
) -> Option<ConstScalar> {
    ConstTyper { ast, interner, known, cx, tys: &mut *tys, scope, lets: Vec::new() }.name(name)
}

/// rustc E0308 for a const in signature form; `what` names it
/// ("this array length").
fn const_mismatch(want: ConstScalar, span: Span, what: &str) -> Diag {
    let tn = want.name();
    Diag::new(
        "L0110",
        span,
        format!("mismatched types: {what} is not a value of type `{tn}`"),
        format!("Write a `{tn}` value in its range, or cast with `as {tn}`."),
    )
}

/// The trait a written trait path names, by its last segment:
/// user traits first, then lang traits. `std::` and `core::`
/// prefixes are accepted and ignored, as type paths do today.
pub(crate) fn trait_def_of_path(
    cx: &ResolveCx,
    interner: &Interner,
    known: &Known,
    segs: &[ast::PathSeg],
    span: Span,
) -> Result<DefId, Diag> {
    let last = segs.last().ok_or_else(|| Diag::new("L0102", span, "expected a trait name", "Write a trait name."))?;
    if segs.len() > 1 && segs[0].name != known.std && interner.get(segs[0].name) != "core" && interner.get(segs[0].name) != "alloc" {
        let names: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
        return Err(crate::diag::module_path_not_yet(&names, span));
    }
    // A full std path must name the trait really living at that
    // path (`std::mem::Display` is not `Display`): only exact
    // canonical rows fall through to the by-name lookup.
    if segs.len() > 1 {
        let path: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
        if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Trait) {
            return Err(Diag::new(
                "L0102",
                span,
                format!("unknown trait `{}`", crate::intern::source_path(interner.get(last.name))),
                "Check the spelling, or define the trait.",
            ));
        }
    }
    // A checked std path names the std trait: a user trait of the same
    // name (`trait Sub`) must not take std's `impl core::ops::Sub`.
    let found = if segs.len() == 1 {
        cx.trait_by_bare_name(interner, last.name)
    } else {
        cx.lang.by_name(interner.get(last.name)).or_else(|| cx.trait_names.get(&last.name).copied())
    };
    found.ok_or_else(|| {
        let n = crate::intern::source_path(interner.get(last.name));
        let fix = match crate::ty::lang::std_trait_module(&n) {
            Some(m) => format!("Import it: `use std::{m}::{n};`."),
            None => "Check the spelling, or define the trait.".to_string(),
        };
        Diag::new("L0102", span, format!("unknown trait `{n}`"), fix)
    })
}

/// The bindings of one trait path's last segment, resolved to
/// assoc defs of the trait. Plain type arguments are returned too,
/// in written order after Self.
fn resolve_trait_path_args(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    trait_def: DefId,
    seg: &ast::PathSeg,
    self_ty: Ty,
    span: Span,
) -> Result<TraitRef, Diag> {
    let rec = cx.index.trait_record(trait_def);
    let n_inputs = rec.map_or(0, |r| r.generics.params.len().saturating_sub(1));
    if matches!(seg.args, GenericArgs::None) && cx.adt_lifetimes.get(&trait_def).is_some_and(|v| !v.is_empty()) {
        return Err(Diag::new(
            "L0203",
            span,
            "an elided lifetime argument of a trait is not supported yet",
            "Write the trait's lifetime arguments, for example `Tr<'a>` or `Tr<'static>`.",
        ));
    }
    let (input_args, bindings): (Vec<GenericArg>, Vec<(DefId, GenericArg)>) = match &seg.args {
        GenericArgs::None => (Vec::new(), Vec::new()),
        GenericArgs::Parenthesized { inputs, output } => {
            // Fn sugar: one tuple input argument, Output binding. A
            // missing `-> R` means `-> ()`, as in Rust. Only the Fn
            // traits take this sugar (rustc E0214 elsewhere).
            if !cx.lang.is_fn_family(trait_def) {
                return Err(Diag::new("L0110", span, "parenthesized trait sugar is only for Fn traits", "Use angle arguments."));
            }
            let one = sugar_elision(ast, interner, known, cx, tys, scope, inputs, *output)?;
            let mut parts = Vec::new();
            for t in inputs {
                parts.push(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?);
            }
            // In a dyn's sugar (R11), an elided output lifetime is the one
            // input lifetime: the object's late-bound one when that is
            // elided, else the written one.
            let out_scope;
            let scope = if scope.late_elided {
                let mut s = scope.clone();
                s.late_out = Some(match one {
                    Some(Region::Static) => Region::Static,
                    Some(Region::Bound(_)) | None => crate::ty::DYN_LATE,
                    Some(r @ Region::Param(_)) if matches!(scope.regions, RegionMode::Keep { .. }) => r,
                    Some(_) => Region::Erased,
                });
                out_scope = s;
                &out_scope
            } else {
                scope
            };
            let tuple = if parts.len() == 1 {
                let ts = tys.intern_tys(&parts);
                tys.intern(TyKind::Tuple(ts))
            } else {
                let ts = tys.intern_tys(&parts);
                tys.intern(TyKind::Tuple(ts))
            };
            let assoc = cx.lang.output_of(trait_def).expect("the Fn family has an Output def");
            let out = match output {
                Some(out) => resolve_scoped(ast, interner, known, cx, tys, *out, scope)?,
                None => UNIT,
            };
            let bindings = vec![(assoc, GenericArg::Ty(out))];
            (vec![GenericArg::Ty(tuple)], bindings)
        }
        GenericArgs::Angle(args) => {
            let mut inputs: Vec<GenericArg> = Vec::new();
            let mut bindings: Vec<(DefId, GenericArg)> = Vec::new();
            // A trait's lifetime params (W-BORROW): all written, or none
            // (an elided trait lifetime is a stated cut below).
            let n_lts = cx.adt_lifetimes.get(&trait_def).map_or(0, |v| v.len());
            let given = args.iter().filter(|a| matches!(a, AstArg::Lifetime(_))).count();
            if given != 0 && given != n_lts {
                return Err(Diag::new(
                    "L0110",
                    span,
                    format!("trait takes {n_lts} lifetime argument(s), but {given} were given"),
                    "Match the trait definition's lifetime parameters.",
                ));
            }
            if given == 0 && n_lts != 0 {
                return Err(Diag::new(
                    "L0203",
                    span,
                    "an elided lifetime argument of a trait is not supported yet",
                    "Write the trait's lifetime arguments, for example `Tr<'a>` or `Tr<'static>`.",
                ));
            }
            for a in args {
                match a {
                    AstArg::Type(t) => {
                        // A bare name in a const parameter's slot names
                        // a const (`Tr<N>`); a type there is a kind
                        // error (rustc E0747).
                        let decl = rec.and_then(|r| r.generics.params.iter().filter(|p| !matches!(p.kind, ParamKind::Lifetime)).nth(1 + inputs.len()));
                        if matches!(decl.map(|p| p.kind), Some(ParamKind::Const(_))) {
                            inputs.push(GenericArg::Const(resolve_const_path_arg(ast, interner, known, cx, tys, scope, *t, span)?));
                        } else {
                            inputs.push(GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?));
                        }
                    }
                    AstArg::Lifetime(lt) => {
                        check_lifetime(interner, scope, *lt)?;
                        if interner.get(lt.name) == "_" {
                            return Err(Diag::new(
                                "L0203",
                                lt.span,
                                "an elided lifetime argument of a trait is not supported yet",
                                "Write a named lifetime or `'static`.",
                            ));
                        }
                    }
                    AstArg::Const(e) => {
                        let c = resolve_const_arg(ast, interner, known, tys, scope, *e, span)?;
                        // The trait's declared type for this position (Self is param 0).
                        let decl = rec.and_then(|r| r.generics.params.iter().filter(|p| !matches!(p.kind, ParamKind::Lifetime)).nth(1 + inputs.len()));
                        // A const value in a type parameter's slot is a
                        // kind error (rustc E0747).
                        if matches!(decl.map(|p| p.kind), Some(ParamKind::Type)) {
                            return Err(Diag::new(
                                "L0110",
                                span,
                                "constant provided when a type was expected",
                                "Write a type for this parameter, such as `u8`.",
                            ));
                        }
                        if let Some(ParamKind::Const(t)) = decl.map(|p| p.kind)
                            && let Some(want) = ConstScalar::of(tys, t)
                        {
                            check_const_expr_ty(ast, interner, known, cx, tys, scope, *e, c, want, span, "this const argument")?;
                        }
                        inputs.push(GenericArg::Const(c));
                    }
                    AstArg::Binding { name, span: bspan, kind } => {
                        let assoc = assoc_in_supers(cx, tys, trait_def, *name).ok_or_else(|| {
                            Diag::new(
                                "L0102",
                                *bspan,
                                format!("trait has no associated item named `{}`", interner.get(*name)),
                                "Check the spelling against the trait definition.",
                            )
                        })?;
                        let bound = match kind {
                            ast::BindingKind::EqTy(t) => GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?),
                            ast::BindingKind::EqConst(e) => {
                                GenericArg::Const(resolve_const_arg(ast, interner, known, tys, scope, *e, *bspan)?)
                            }
                            ast::BindingKind::Constraint(_) => {
                                return Err(not_yet("L0621", *bspan, "associated binding constraints in this position"));
                            }
                        };
                        bindings.push((assoc, bound));
                    }
                }
            }
            (inputs, bindings)
        }
    };
    // Lang traits with a `Rhs = Self` default (the comparison and
    // binary operator families) accept the input omitted.
    let mut input_args = input_args;
    if input_args.len() + 1 == n_inputs && cx.lang.input_defaults_to_self(trait_def) {
        input_args.push(GenericArg::Ty(self_ty));
    }
    // A user trait's omitted trailing inputs take their defaults, with
    // `Self` as this ref's Self type. A trait object has no Self to put
    // there (rustc E0393).
    if input_args.len() < n_inputs
        && !matches!(seg.args, GenericArgs::Parenthesized { .. })
        && let Some(g) = rec.and_then(|r| crate::check::defaults::trait_generics(ast, cx, r.name))
    {
        if self_ty == DYN_SELF && crate::check::defaults::defaults_name_self(ast, known, g, input_args.len()) {
            return Err(Diag::new(
                "L0110",
                span,
                "a trait object cannot use a parameter default that names `Self`",
                "Write the trait's parameters out in the `dyn` type.",
            ));
        }
        crate::check::defaults::fill(ast, interner, known, cx, tys, scope, g, Some(self_ty), &mut input_args, span)?;
    }
    if input_args.len() != n_inputs {
        return Err(Diag::new(
            "L0110",
            span,
            format!("trait takes {n_inputs} input argument(s), but {} were given", input_args.len()),
            "Match the trait definition's parameters.",
        ));
    }
    let mut all = vec![GenericArg::Ty(self_ty)];
    all.extend(input_args);
    let args = tys.intern_args(&all);
    let bindings = tys.intern_bindings(&bindings);
    Ok(TraitRef { def: trait_def, args, bindings })
}

/// Resolves a written trait reference (a bound or an impl header)
/// for one Self type.
pub fn resolve_trait_ref(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    self_ty: Ty,
    tref: &ast::TraitRefExpr,
    span: Span,
) -> Result<TraitRef, Diag> {
    // A trait declared in an enclosing function-body block shadows
    // the flat trait tables (R18).
    let trait_def = match tref.path.as_slice() {
        [only] => match scope.local_traits.iter().rev().find(|(n, _)| *n == only.name) {
            Some(&(_, d)) => d,
            None => trait_def_of_path(cx, interner, known, &tref.path, span)?,
        },
        _ => trait_def_of_path(cx, interner, known, &tref.path, span)?,
    };
    let seg = tref.path.last().unwrap();
    resolve_trait_path_args(ast, interner, known, cx, tys, scope, trait_def, seg, self_ty, span)
}

/// Scoped type resolution: `resolve_ty` plus generic parameters,
/// generic Adt applications, projections, and qualified paths.
/// Everything `resolve_ty` accepts resolves the same way here
/// under an empty scope.
pub fn resolve_scoped(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    id: ast::TyId,
    scope: &Scope,
) -> Result<Ty, Diag> {
    let span = ast.ty_span(id);
    match ast.ty(id) {
        TyExpr::Unit => Ok(UNIT),
        TyExpr::Never => Ok(NEVER),
        TyExpr::Ref { lifetime, mutable, inner } => {
            // `&'static dyn Tr` defaults its object lifetime to the
            // reference's: `&'static (dyn Tr + 'static)` (ARCH 2.8).
            // A reference to a dyn type keeps a written `'static`, so
            // a coercion into it can be checked (`check::object`); the
            // borrow checker honors that kept region too. Every other
            // reference resolves under the scope's region mode.
            let pointee = *inner;
            let dyn_pointee = (matches!(scope.regions, RegionMode::Keep { .. }) || scope.dyn_args) && points_to_dyn(ast, pointee);
            let early = if dyn_pointee { Some(ref_region(interner, scope, *lifetime, span)?) } else { None };
            let mut inner = match early {
                // W-BORROW: the pointee's default object lifetime is this
                // reference's, in region signatures (`resolve_dyn`).
                Some(r) => {
                    let mut s = scope.clone();
                    s.obj_default = Some(r);
                    resolve_scoped(ast, interner, known, cx, tys, pointee, &s)?
                }
                None => resolve_scoped(ast, interner, known, cx, tys, pointee, scope)?,
            };
            if lifetime.is_some_and(|lt| interner.get(lt.name) == "static")
                && let TyKind::Dyn(b, r) = tys.kind(inner)
            {
                if r == Region::Erased {
                    inner = tys.intern(TyKind::Dyn(b, Region::Static));
                }
                return Ok(tys.intern(TyKind::Ref(Region::Static, Mut::from_bool(*mutable), inner)));
            }
            let region = match early {
                Some(r) => r,
                None => ref_region(interner, scope, *lifetime, span)?,
            };
            let region = if scope.static_refs && lifetime.is_some_and(|lt| interner.get(lt.name) == "static") { Region::Static } else { region };
            Ok(if region == Region::Erased { tys.mk_ref(*mutable, inner) } else { tys.intern(TyKind::Ref(region, Mut::from_bool(*mutable), inner)) })
        }
        TyExpr::Tuple(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for &e in elems {
                out.push(resolve_scoped(ast, interner, known, cx, tys, e, scope)?);
            }
            let ts = tys.intern_tys(&out);
            Ok(tys.intern(TyKind::Tuple(ts)))
        }
        TyExpr::Paren(inner) => resolve_scoped(ast, interner, known, cx, tys, *inner, scope),
        TyExpr::Slice(inner) => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            Ok(tys.intern(TyKind::Slice(e)))
        }
        TyExpr::Array { inner, len } => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            let n = resolve_const_arg(ast, interner, known, tys, scope, *len, span)?;
            check_const_expr_ty(ast, interner, known, cx, tys, scope, *len, n, ConstScalar::Int(IntTy::Usize), span, "this array length")?;
            Ok(tys.intern(TyKind::Array(e, n)))
        }
        TyExpr::Ptr { mutable, inner } => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            // A raw pointer to `str`, `[T]` or `dyn Tr` is a fat pointer
            // (tf-fatptr): address plus length or vtable, with a narrow set
            // of operations (check/mod.rs `ptr_method`, casts, `ptr::eq`).
            // A struct with an unsized tail stays out.
            if let TyKind::Adt(d, _) = tys.kind(e)
                && tys.unsized_field(d).is_some()
            {
                return Err(not_yet("L0602", span, "a raw pointer to an unsized struct"));
            }
            Ok(tys.intern(TyKind::RawPtr(Mut::from_bool(*mutable), e)))
        }
        TyExpr::Infer => match &scope.infer_cell {
            Some(cell) => {
                let id = cell.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Ok(tys.intern(TyKind::Infer(InferId(id, InferKind::General))))
            }
            None => Err(not_yet("L0602", span, "inferred types (`_`) in signatures")),
        },
        TyExpr::ImplTrait { .. } => match scope.apit.iter().find(|(n, _)| *n == id) {
            Some(&(_, t)) => Ok(t),
            None => Err(not_yet("L0602", span, "`impl Trait` types in this position")),
        },
        TyExpr::Dyn { binder, bounds, lifetime } => {
            // The trait args keep the scope's region mode (R11): a written
            // lifetime there is a free region of the object.
            let mut ds = scope.clone();
            ds.fn_ptr_free = false;
            let ty = resolve_dyn(ast, interner, known, cx, tys, &ds, binder, bounds, *lifetime, span)?;
            keep_object_lifetime(interner, tys, scope, ty, bounds, *lifetime, span)
        }
        TyExpr::FnPtr { qual, inputs, variadic, ret, binder } => {
            if *variadic || qual.is_unsafe || qual.is_async || qual.is_const || qual.abi.is_some() {
                return Err(not_yet("L0602", span, "qualified or variadic function pointer types"));
            }
            binder_shadow(interner, scope, binder)?;
            // A fn pointer's elided lifetimes are its own (late-bound), a
            // written `&'static` is kept (`Scope::static_refs`), and one
            // lifetime of the enclosing item is its free region (W-BORROW3,
            // `FnSig::free_slots`). Other written lifetimes are L0203.
            let free = fn_ptr_free_name(ast, interner, id)?;
            if free.is_some() && !scope.fn_ptr_free {
                return Err(Diag::new(
                    "L0203",
                    span,
                    "a fn pointer type that names a lifetime is supported only in fn signatures and `let` annotations",
                    "Elide the lifetimes (`fn(&T) -> &U`), or use a generic `F: Fn(&T) -> &U` parameter.",
                ));
            }
            let in_tys: Vec<ast::TyId> = inputs.iter().map(|p| p.ty).collect();
            sugar_elision(ast, interner, known, cx, tys, scope, &in_tys, *ret)?;
            let free_region = match free {
                Some(lt) => Some((lt, scope_region(interner, scope, Some(lt), lt.span)?)),
                None => None,
            };
            let outer = scope;
            let mut erased = scope.erased();
            erased.static_refs = true;
            let scope = &erased;
            let mut ins = Vec::with_capacity(inputs.len());
            for p in inputs {
                ins.push(resolve_scoped(ast, interner, known, cx, tys, p.ty, scope)?);
            }
            let out = match ret {
                Some(r) => resolve_scoped(ast, interner, known, cx, tys, *r, scope)?,
                None => UNIT,
            };
            let (free_slots, free_region) = match free_region {
                Some((lt, r)) => (fn_ptr_free_mask(ast, interner, known, cx, tys, outer, &in_tys, *ret, lt, &ins, out)?, r),
                None => (0, Region::Erased),
            };
            let (own_out, out_slots) = if free_slots == 0 { fn_ptr_own_output(ast, interner, known, cx, tys, outer, &in_tys, *ret, out) } else { (0, u8::MAX) };
            let inputs = tys.intern_tys(&ins);
            let sig = tys.intern_sig(Binder::plain(FnSig { free_slots, free_region, own_out, out_slots, ..FnSig::plain(inputs, out) }));
            Ok(tys.intern(TyKind::FnPtr(sig)))
        }
        TyExpr::QPath { self_ty, trait_path, segs } => {
            let base = resolve_scoped(ast, interner, known, cx, tys, *self_ty, scope)?;
            if trait_path.is_empty() {
                return assoc_projection(cx, tys, scope, base, segs, span, interner);
            }
            let trait_def = trait_def_of_path(cx, interner, known, trait_path, span)?;
            let seg = trait_path.last().unwrap();
            let tr = resolve_trait_path_args(ast, interner, known, cx, tys, scope, trait_def, seg, base, span)?;
            projection_of(cx, tys, tr, segs, span, interner)
        }
        TyExpr::Path(segs) => resolve_path_ty(ast, interner, known, cx, tys, scope, segs, span),
        _ => Err(not_yet("L0602", span, "this type form")),
    }
}

/// `<T>::Assoc` and `T::Assoc`: the trait comes from the scope's
/// associated sources for that Self type. Exactly one source may
/// name the assoc item, as in Rust without disambiguation.
fn assoc_projection(
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    base: Ty,
    segs: &[ast::PathSeg],
    span: Span,
    interner: &Interner,
) -> Result<Ty, Diag> {
    if segs.len() != 1 {
        return Err(not_yet("L0505", span, "module paths in types"));
    }
    let name = segs[0].name;
    // The same bound can reach a scope twice (a method's own bounds
    // are in both its own scope and the combined env); one trait ref
    // counts once, as in rustc, where only distinct traits clash.
    let mut hits: Vec<&AssocSrc> = Vec::new();
    for src in &scope.assoc_srcs {
        if src.self_ty == base
            && src.assocs.iter().any(|(n, _)| *n == name)
            && !hits.iter().any(|h| h.trait_def == src.trait_def && h.args == src.args)
        {
            hits.push(src);
        }
    }
    match hits.len() {
        1 => {
            let src = hits[0];
            let tr = TraitRef { def: src.trait_def, args: src.args, bindings: EMPTY_BINDINGS };
            projection_of(cx, tys, tr, segs, span, interner)
        }
        0 => Err(Diag::new(
            "L0102",
            span,
            format!("no associated item named `{}` is in scope for this type", interner.get(name)),
            "Name the trait: write `<Type as Trait>::Item`, or add the bound.",
        )),
        _ => Err(Diag::new(
            "L0110",
            span,
            format!("`{}` is ambiguous: more than one bound names it", interner.get(name)),
            "Name the trait: write `<Type as Trait>::Item`.",
        )),
    }
}

/// The def of the associated item `name` of a trait, looking
/// through its supertraits as rustc does for a trait reference's
/// binding (`ExactSizeIterator<Item = ..>` names
/// `Iterator::Item`). A qualified path must name the defining
/// trait instead (rustc E0576), so `projection_of` does not use
/// this. None when no supertrait path names it, or when two
/// different items of the name are reachable (rustc reports
/// that binding ambiguous).
fn assoc_in_supers(cx: &ResolveCx, tys: &impl TyIntern, trait_def: DefId, name: Sym) -> Option<DefId> {
    let mut found: Option<DefId> = None;
    let mut seen: Vec<DefId> = Vec::new();
    let mut stack = vec![trait_def];
    while let Some(def) = stack.pop() {
        if seen.contains(&def) {
            continue;
        }
        seen.push(def);
        let rec = cx.index.trait_record(def)?;
        if let Some(d) = rec.assoc_by_name(name) {
            match found {
                None => found = Some(d),
                Some(prev) if prev == d => {}
                Some(_) => return None,
            }
        }
        for pred in &rec.generics.predicates {
            let Predicate::Trait(b) = pred else { continue };
            let is_self = tys.args(b.value.args).first().and_then(|g| g.as_ty()).is_some_and(|t| tys.kind(t) == TyKind::Param(ParamId(0)));
            if is_self {
                stack.push(b.value.def);
            }
        }
    }
    found
}

/// The projection type for the assoc item `segs[0]` of one trait ref.
fn projection_of(
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    tr: TraitRef,
    segs: &[ast::PathSeg],
    span: Span,
    interner: &Interner,
) -> Result<Ty, Diag> {
    if segs.len() != 1 || segs[0].has_args() {
        return Err(not_yet("L0621", span, "qualified paths with more than one segment"));
    }
    let assoc = cx.index.trait_record(tr.def).and_then(|r| r.assoc_by_name(segs[0].name)).ok_or_else(|| {
        Diag::new(
            "L0102",
            span,
            format!("trait has no associated item named `{}`", interner.get(segs[0].name)),
            "Check the spelling against the trait definition.",
        )
    })?;
    Ok(tys.intern(TyKind::Projection(AssocId(assoc), tr.args)))
}

/// A `dyn` type in signature form (ARCH 2.8). The principal is
/// existential (`DYN_SELF` in its Self slot), auto bounds become
/// the bound bits as written, and supertraits stay empty: the
/// derived sets come from the trait's dyn info, so the same written
/// type interns the same bounds before and after trait tables are
/// built. A written `'static` bound is kept as the region (the
/// coercion site checks it); every other region is erased. Dyn
/// compatibility errors are `check::object`'s (they need the
/// trait's methods); this only forms the type and rejects the
/// forms the subset has no vtable for.
#[allow(clippy::too_many_arguments)]
fn resolve_dyn(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    binder: &[ast::Lifetime],
    bounds: &[TraitBound],
    lifetime: Option<ast::Lifetime>,
    span: Span,
) -> Result<Ty, Diag> {
    // One explicit lifetime bound at most (rustc E0226): the
    // trailing one is `lifetime`, any others stay in `bounds`.
    if usize::from(lifetime.is_some()) + bounds.iter().filter(|b| matches!(b, TraitBound::Lifetime(_))).count() > 1 {
        return Err(Diag::new("L0110", span, "a dyn type has at most one lifetime bound", "Keep one lifetime bound."));
    }
    let mut principal: Option<Binder<TraitRef>> = None;
    let mut auto = AutoTraits::default();
    let mut region = Region::Erased;
    let mut lifetime_bound = |lt: ast::Lifetime| -> Result<(), Diag> {
        check_lifetime(interner, scope, lt)?;
        if interner.get(lt.name) == "static" {
            region = Region::Static;
        }
        Ok(())
    };
    if let Some(lt) = lifetime {
        lifetime_bound(lt)?;
    }
    binder_shadow(interner, scope, binder)?;
    for b in bounds {
        match b {
            TraitBound::Lifetime(lt) => lifetime_bound(*lt)?,
            TraitBound::Trait { binder, trait_ref, maybe } => {
                if *maybe {
                    return Err(not_yet("L0602", span, "`?Trait` bounds on dyn types"));
                }
                // Regions in a dyn type's trait args are free regions the
                // borrow checker does not track through objects yet: an
                // elided `Fn(&T)` input is the trait's own (late-bound),
                // every other lifetime or reference there is a reject.
                if dyn_args_have_regions(ast, interner, &trait_ref.path) {
                    return Err(Diag::new(
                        "L0203",
                        span,
                        "lifetimes in the trait arguments of a `dyn` type are not supported yet",
                        "Use owned argument types, or elide the lifetimes in `Fn(&T)` arguments.",
                    ));
                }
                let trait_def = trait_def_of_path(cx, interner, known, &trait_ref.path, span)?;
                if cx.lang.is_auto(trait_def) {
                    if trait_def == cx.lang.send {
                        auto.send = true;
                    } else if trait_def == cx.lang.sync {
                        auto.sync = true;
                    } else {
                        auto.unpin = true;
                    }
                    continue;
                }
                if principal.is_some() {
                    return Err(Diag::new("L0110", span, "a dyn type has at most one principal trait", "Keep one trait plus auto traits."));
                }
                binder_shadow(interner, scope, binder)?;
                // Vtables exist for user traits, the Fn family (ARCH
                // 2.9: a closure's one call entry), `Any` (a type id,
                // check/any.rs), and `Debug` and `Display` (the header's
                // fmt shim); another std trait has no method bodies the
                // subset can point a vtable at yet.
                let fn_family = cx.lang.is_fn_family(trait_def);
                let fmt_trait = trait_def == cx.lang.debug || trait_def == cx.lang.display;
                if !fn_family && !fmt_trait && trait_def != cx.lang.any && !cx.index.trait_record(trait_def).is_some_and(|r| r.local) {
                    let name = interner.get(trait_ref.path.last().unwrap().name).to_string();
                    return Err(dyn_not_yet(span, &format!("`dyn {name}` (a std trait)")));
                }
                let seg = trait_ref.path.last().unwrap();
                if fn_family && !matches!(seg.args, GenericArgs::Parenthesized { .. }) {
                    return Err(dyn_not_yet(span, "a `dyn` Fn trait without the `Fn(..) -> R` form"));
                }
                let mut fs = scope.clone();
                fs.static_refs = fn_family;
                fs.dyn_args = true;
                fs.late_elided = fn_family;
                fs.late_out = None;
                let tr = resolve_trait_path_args(ast, interner, known, cx, tys, &fs, trait_def, seg, DYN_SELF, span)?;
                // An elided lifetime of an Adt in `Fn` sugar is late-bound,
                // and erased Adts keep no lifetime args to mark that in.
                if fn_family && sugar_has_adt_regions(cx, tys, tr) {
                    return Err(Diag::new(
                        "L0203",
                        span,
                        "a std type with a lifetime (`Chars`, a guard, a borrowing iterator) in the arguments of a `dyn Fn` type is not supported yet",
                        "Use a reference to an owned type, or a generic `F: Fn(..)` parameter.",
                    ));
                }
                // The `Fn(..) -> R` sugar binds `Output`; other bindings
                // are not supported yet.
                if !fn_family && !tys.bindings(tr.bindings).is_empty() {
                    return Err(dyn_not_yet(span, "associated type bindings in `dyn` types"));
                }
                principal = Some(Binder::plain(tr));
            }
        }
    }
    // `dyn Send`, `dyn Send + Sync`: no principal, only auto traits. Its
    // vtable holds drop, size, and align (`object::vtable_key`). No trait
    // at all (`dyn 'a`) is rustc E0224.
    if principal.is_none() && !(auto.send || auto.sync || auto.unpin) {
        return Err(Diag::new("L0110", span, "at least one trait is required for an object type", "Write a trait after `dyn`."));
    }
    let bounds_id = tys.intern_dyn_bounds(DynBounds { principal, supertraits: Box::new([]), auto });
    Ok(tys.intern(TyKind::Dyn(bounds_id, region)))
}

/// True when a `dyn Fn*` principal's inputs or output hold a builtin Adt
/// with a lifetime (`Chars`, `Ref<T>`), also inside nested `dyn` args:
/// its lifetime has no arg to keep (a user Adt's does, R11).
fn sugar_has_adt_regions(cx: &ResolveCx, tys: &impl TyIntern, tr: TraitRef) -> bool {
    fn go(cx: &ResolveCx, tys: &impl TyIntern, t: Ty) -> bool {
        match tys.kind(t) {
            TyKind::Adt(_, a) => {
                (tys.builtin_of(t).is_some() && crate::borrowck::adt_region_count(cx.adt_lifetimes, tys, t) > 0)
                    || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| go(cx, tys, e)))
            }
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => go(cx, tys, e),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| go(cx, tys, e)),
            TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.is_some_and(|p| sugar_has_adt_regions(cx, tys, p.value)),
            _ => false,
        }
    }
    tys.args(tr.args).iter().skip(1).any(|g| g.as_ty().is_some_and(|e| go(cx, tys, e)))
        || tys.bindings(tr.bindings).iter().any(|(_, g)| g.as_ty().is_some_and(|e| go(cx, tys, e)))
}

/// True when a written type is a `dyn` type (through parentheses) with
/// no lifetime bound: its object lifetime is the context's default.
fn dyn_lifetime_unwritten(ast: &Ast, t: ast::TyId) -> bool {
    match ast.ty(t) {
        TyExpr::Paren(inner) => dyn_lifetime_unwritten(ast, *inner),
        TyExpr::Dyn { bounds, lifetime, .. } => lifetime.is_none() && !bounds.iter().any(|b| matches!(b, TraitBound::Lifetime(_))),
        _ => false,
    }
}

/// A region signature's type arg `elem` of a std type whose param has a
/// lifetime bound (`MutexGuard<'a, T: ?Sized + 'a>`, the `RwLock` and
/// `RefCell` guards, `Cow<'a, B: ?Sized + 'a>`): a `dyn` written there
/// with no lifetime bound has that lifetime `r` as its object lifetime
/// (rustc's default from the containing type's bound), not `'static`.
fn bounded_arg_default(ast: &Ast, tys: &mut impl TyIntern, seg: &ast::PathSeg, elem: Ty, r: Region) -> Ty {
    let TyKind::Dyn(b, _) = tys.kind(elem) else { return elem };
    let GenericArgs::Angle(a) = &seg.args else { return elem };
    match a.iter().find_map(|g| if let AstArg::Type(t) = g { Some(*t) } else { None }) {
        Some(t) if dyn_lifetime_unwritten(ast, t) => tys.intern(TyKind::Dyn(b, r)),
        _ => elem,
    }
}

/// The reject for a `dyn` form the subset has no vtable for yet.
pub fn dyn_not_yet(span: Span, what: &str) -> Diag {
    Diag::new(
        "L0702",
        span,
        format!("{what} is not supported yet"),
        "Use `&dyn Trait` or `&mut dyn Trait` with a trait defined in this crate, or use generics.",
    )
}

/// A path type: parameters, primitives, builtin Adts, user Adts
/// with generic arguments, and `Self`/parameter projections.
pub(crate) fn resolve_path_ty(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    segs: &[ast::PathSeg],
    span: Span,
) -> Result<Ty, Diag> {
    if segs.len() > 1 {
        // `Self::Assoc` and `Param::Assoc` projections.
        if segs[0].name == known.self_type
            && let Some(base) = scope.self_ty
        {
            // A region signature reads the impl's own associated types with
            // their regions (`Self::IntoIter` in `into_iter`).
            if matches!(scope.regions, RegionMode::Keep { .. })
                && segs.len() == 2
                && let Some(&(_, t)) = scope.assoc_regioned.iter().find(|(n, _)| *n == segs[1].name)
            {
                return Ok(t);
            }
            return assoc_projection(cx, tys, scope, base, &segs[1..], span, interner);
        }
        if let Some(i) = scope.param_of(segs[0].name) {
            let base = tys.intern(TyKind::Param(ParamId(i)));
            return assoc_projection(cx, tys, scope, base, &segs[1..], span, interner);
        }
        // In an instance body the param name maps to its concrete type,
        // and the assoc sources are substituted alike (`fn_instance`).
        if let Some(&(_, base)) = scope.param_tys.iter().find(|(n, _)| *n == segs[0].name) {
            return assoc_projection(cx, tys, scope, base, &segs[1..], span, interner);
        }
        if segs[0].name == known.std || interner.get(segs[0].name) == "core" || interner.get(segs[0].name) == "alloc" {
            // Fall through with the last segment, but only for a
            // path that really names a std type there
            // (`std::option::Vec` is not `Vec`).
            let path: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
            // A std iterator type by path (`std::slice::Iter<'a, T>`).
            if let Some(kind) = crate::check::stdtypes::iter_by_path(&path) {
                return crate::check::stdtypes::resolve_iter_path(ast, interner, known, cx, tys, scope, kind, segs.last().unwrap(), span);
            }
            if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Type)
                && !crate::ty::lang::std_is_primitive_path(&path)
            {
                let n = interner.get(segs.last().unwrap().name);
                return Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."));
            }
            // `std::cmp::Ordering` is the core enum (and the UTF-8 error
            // paths the std structs) even where a user type of that name
            // owns the flat name.
            if let Some(def) = std_adt_of_path(&path)
                && !segs.last().unwrap().has_args()
            {
                return Ok(tys.intern(TyKind::Adt(def, EMPTY_ARGS)));
            }
            // `core::fmt` types are known by their full path only:
            // `Error` and `Result` must never match a bare name.
            if path.len() == 3 && path[1] == "fmt" {
                return resolve_fmt_path(interner, tys, scope, path[2], segs.last().unwrap(), span);
            }
            // `Location<'a>`: lust erases its one lifetime.
            if path[1..] == ["panic", "Location"]
                && let GenericArgs::Angle(a) = &segs[2].args
                && a.iter().all(|g| matches!(g, ast::GenericArg::Lifetime(_)))
            {
                return Ok(tys.intern(TyKind::Adt(location_def(), EMPTY_ARGS)));
            }
            if path[1..] == ["any", "TypeId"] {
                if segs[2].has_args() {
                    return Err(Diag::new("L0110", span, "`TypeId` takes no generic arguments", "Remove the `<...>` part."));
                }
                return Ok(type_id_ty(tys));
            }
            // `std::thread::Result<T>`: std's alias for
            // `Result<T, Box<dyn Any + Send>>` (R26).
            if path.len() == 3 && path[0] == "std" && path[1] == "thread" && path[2] == "Result" {
                let seg = segs.last().unwrap();
                let GenericArgs::Angle(a) = &seg.args else {
                    return Err(Diag::new("L0110", span, "`thread::Result` takes one type argument", "Write `thread::Result<T>`."));
                };
                let args: Vec<Ty> = resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "thread::Result")?
                    .into_iter()
                    .filter_map(|g| g.as_ty())
                    .collect();
                let [t] = args.as_slice() else {
                    return Err(Diag::new("L0110", span, "`thread::Result` takes one type argument", "Write `thread::Result<T>`."));
                };
                let any = crate::check::unwind::dyn_any_send(tys, cx.lang.any);
                let err = tys.mk_boxed(any);
                return Ok(tys.mk_result(*t, err));
            }
            // `std::borrow::Cow<'a, B>` (W-STD-B).
            if path.len() == 3 && path[1] == "borrow" && path[2] == "Cow" {
                return resolve_cow_path(ast, interner, known, cx, tys, scope, segs.last().unwrap(), span);
            }
            // `std::ops::Bound<T>` (W-STD-C phase 2).
            if path.len() == 3 && path[1] == "ops" && path[2] == "Bound" {
                let seg = segs.last().unwrap();
                let GenericArgs::Angle(a) = &seg.args else {
                    return Err(Diag::new("L0110", span, "`Bound` takes one type argument", "Write `Bound<&T>`, for example."));
                };
                let args: Vec<GenericArg> =
                    resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "Bound")?.into_iter().filter(|g| g.as_ty().is_some()).collect();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "`Bound` takes one type argument", "Write `Bound<&T>`, for example."));
                }
                return Ok(tys.mk_adt(bound_def(), &args));
            }
            // `core::mem::MaybeUninit<T>` (TRIAGE T5).
            if path.len() == 3 && path[1] == "mem" && path[2] == "MaybeUninit" {
                let seg = segs.last().unwrap();
                let GenericArgs::Angle(a) = &seg.args else {
                    return Err(Diag::new("L0110", span, "`MaybeUninit` takes one type argument", "Write `MaybeUninit<T>`."));
                };
                let args: Vec<GenericArg> =
                    resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "MaybeUninit")?.into_iter().filter(|g| g.as_ty().is_some()).collect();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "`MaybeUninit` takes one type argument", "Write `MaybeUninit<T>`."));
                }
                return Ok(tys.mk_adt(maybe_uninit_def(), &args));
            }
            // `std::sync::mpsc::TrySendError<T>` (TRIAGE T5).
            if path.len() == 4 && path[1] == "sync" && path[2] == "mpsc" && path[3] == "TrySendError" {
                let seg = segs.last().unwrap();
                let GenericArgs::Angle(a) = &seg.args else {
                    return Err(Diag::new("L0110", span, "`TrySendError` takes one type argument", "Write `TrySendError<T>`."));
                };
                let args: Vec<GenericArg> =
                    resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "TrySendError")?.into_iter().filter(|g| g.as_ty().is_some()).collect();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "`TrySendError` takes one type argument", "Write `TrySendError<T>`."));
                }
                return Ok(tys.mk_adt(try_send_error_def(), &args));
            }
            // `std::sync::TryLockError<T>`.
            if path.len() == 3 && path[1] == "sync" && path[2] == "TryLockError" {
                let seg = segs.last().unwrap();
                let GenericArgs::Angle(a) = &seg.args else {
                    return Err(Diag::new("L0110", span, "`TryLockError` takes one type argument", "Write `TryLockError<T>`."));
                };
                let args: Vec<GenericArg> =
                    resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "TryLockError")?.into_iter().filter(|g| g.as_ty().is_some()).collect();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "`TryLockError` takes one type argument", "Write `TryLockError<T>`."));
                }
                return Ok(tys.mk_adt(try_lock_error_def(), &args));
            }
            // `core::num::NonZero<T>` and its aliases
            // (`NonZeroU32` and kin, TRIAGE T5): one integer
            // argument, explicit or from the alias name.
            if path.len() == 3 && path[1] == "num" && (path[2] == "NonZero" || path[2].starts_with("NonZero")) {
                let seg = segs.last().unwrap();
                let alias = match path[2] {
                    "NonZeroU8" => Some(IntTy::U8),
                    "NonZeroU16" => Some(IntTy::U16),
                    "NonZeroU32" => Some(IntTy::U32),
                    "NonZeroU64" => Some(IntTy::U64),
                    "NonZeroU128" => Some(IntTy::U128),
                    "NonZeroUsize" => Some(IntTy::Usize),
                    "NonZeroI8" => Some(IntTy::I8),
                    "NonZeroI16" => Some(IntTy::I16),
                    "NonZeroI32" => Some(IntTy::I32),
                    "NonZeroI64" => Some(IntTy::I64),
                    "NonZeroI128" => Some(IntTy::I128),
                    "NonZeroIsize" => Some(IntTy::Isize),
                    _ => None,
                };
                let inner = if let Some(i) = alias {
                    if seg.has_args() {
                        return Err(Diag::new("L0110", span, format!("`{}` takes no type arguments", path[2]), "Remove the `<...>` part."));
                    }
                    int(i)
                } else if path[2] == "NonZero" {
                    let GenericArgs::Angle(a) = &seg.args else {
                        return Err(Diag::new("L0110", span, "`NonZero` takes one type argument", "Write `NonZero<u32>`, for example."));
                    };
                    let args: Vec<GenericArg> =
                        resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "NonZero")?.into_iter().filter(|g| g.as_ty().is_some()).collect();
                    if args.len() != 1 {
                        return Err(Diag::new("L0110", span, "`NonZero` takes one type argument", "Write `NonZero<u32>`, for example."));
                    }
                    args[0].as_ty().unwrap()
                } else {
                    return Err(Diag::new("L0102", span, format!("unknown type `{}`", path[2]), "Check the spelling, or define the type."));
                };
                if !matches!(tys.kind(inner), TyKind::Int(_)) {
                    return Err(Diag::new(
                        "L0612",
                        span,
                        "the argument of `NonZero` is not an integer type".to_string(),
                        "NonZero wraps an integer type.",
                    ));
                }
                return Ok(nonzero_ty(tys, inner));
            }
            // The owning std iterators (W-STD-B, ty/iter.rs).
            if let Some(k) = crate::ty::iter::owning_by_path(&path) {
                let seg = segs.last().unwrap();
                let args: Vec<Ty> = match &seg.args {
                    GenericArgs::Angle(a) => {
                        let kinds = vec![false; a.len()];
                        resolve_generic_args(ast, interner, known, cx, tys, scope, a, &kinds, kinds.len(), span, k.path().1)?
                            .into_iter()
                            .filter_map(|g| g.as_ty())
                            .collect()
                    }
                    _ => Vec::new(),
                };
                if args.len() != k.n_args() {
                    return Err(Diag::new(
                        "L0110",
                        span,
                        format!("`{}` takes {} type argument(s)", k.display(), k.n_args()),
                        "Write the type arguments.",
                    ));
                }
                return Ok(crate::ty::iter::mk_iter(tys, k, &args));
            }
            // The hashed collections and hashers (W-STD-B, ty/hash.rs). A map
            // entry type keeps its loan in a region slot of its own, so a
            // written one (whose lifetime a signature would relate) is
            // outside the subset; its variants match (`PatRes::Entry`).
            if let Some(k) = crate::ty::hash::HashTy::by_name(path[path.len() - 1])
                && matches!(path[1], "collections" | "hash")
            {
                use crate::ty::hash::HashTy;
                if matches!(k, HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry) {
                    return Err(crate::ty::hash::not_imported(k, span));
                }
                return resolve_hash_path(ast, interner, known, cx, tys, scope, k, segs.last().unwrap(), span);
            }
        } else {
            return Err(not_yet("L0505", span, "module paths in types"));
        }
    }
    let seg = segs.last().unwrap();
    let name = seg.name;
    if segs.len() == 1 {
        if let Some((_, t)) = scope.param_tys.iter().find(|(n, _)| *n == name) {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "a type parameter takes no generic arguments", "Remove the `<...>` part."));
            }
            return Ok(*t);
        }
        if let Some(i) = scope.param_of(name) {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "a type parameter takes no generic arguments", "Remove the `<...>` part."));
            }
            return Ok(tys.intern(TyKind::Param(ParamId(i))));
        }
        if scope.outer_params.contains(&name) {
            return Err(Diag::new(
                "L0110",
                span,
                format!("can't use generic parameters from an outer function: `{}`", interner.get(name)),
                "Move the item out of the function, or give it its own generic parameter.",
            ));
        }
        if name == known.self_type {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "`Self` takes no generic arguments", "Remove the `<...>` part."));
            }
            let keep = matches!(scope.regions, RegionMode::Keep { .. });
            return (if keep { scope.self_ty_regioned.or(scope.self_ty) } else { scope.self_ty })
                .ok_or_else(|| Diag::new("L0102", span, "`Self` is only valid inside an impl or trait", "Write the type name."));
        }
    }
    // A type item of an enclosing function-body block (R18) shadows the
    // builtin, std, and module types of its name, primitives included:
    // an alias answers here, an Adt takes the Adt path below.
    let local_block = segs.len() == 1 && (scope.local_types.iter().any(|e| e.0 == name) || scope.local_aliases.iter().any(|e| e.0 == name));
    if local_block && let Some(&(_, alias_ty)) = scope.local_aliases.iter().rev().find(|(n, _)| *n == name) {
        return if seg.has_args() {
            Err(Diag::new("L0110", span, "this alias takes no generic arguments", "Remove the `<...>` part."))
        } else {
            alias_at_use(ast, interner, known, cx, tys, scope, alias_ty, AliasBody::Local, span)
        };
    }
    if !local_block {
    let no_generics = |t: Ty| -> Result<Ty, Diag> {
        if !seg.has_args() {
            Ok(t)
        } else {
            Err(Diag::new("L0110", span, "this type takes no generic arguments", "Remove the `<...>` part."))
        }
    };
    if let Some(t) = known.int_ty(name) {
        return no_generics(int(t));
    }
    if name == known.bool {
        return no_generics(BOOL);
    }
    if name == known.char {
        return no_generics(CHAR);
    }
    if name == known.str {
        return no_generics(STR);
    }
    if name == known.f32 {
        return no_generics(tys.float_ty(FloatTy::F32));
    }
    if name == known.f64 {
        return no_generics(tys.float_ty(FloatTy::F64));
    }
    if name == known.String {
        return no_generics(STRING);
    }
    // Past the checks above, a multi-segment path is a canonical std
    // path: it names std's type, never a user type of that name.
    let std_path = segs.len() > 1;
    // A user type named `Rc` shadows std's (which needs a `use`), and
    // so does a user `Option` or `Result` (prelude names, as in Rust).
    let shadowed = !std_path && (cx.type_names.contains_key(&name) || scope.local_types.iter().any(|(n, _, _)| *n == name));
    if name == known.Vec || (name == known.Option && !shadowed) || name == known.Box || (name == known.Rc && !shadowed) {
        let args = match &seg.args {
            GenericArgs::Angle(a) => resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, interner.get(name))?,
            _ => {
                return Err(Diag::new(
                    "L0110",
                    span,
                    format!("`{}` takes one type argument", interner.get(name)),
                    "Write it with its element type.",
                ));
            }
        };
        let mut elem = args.iter().find_map(|g| g.as_ty()).unwrap_or(ERROR);
        // The default object lifetime of `Box<dyn Tr>` and `Rc<dyn Tr>`
        // with no written bound is `'static` in a signature (fields,
        // params, returns, aliases, impl headers), as in rustc; a body
        // annotation infers it, and a written bound is the borrow
        // checker's (regions erased here).
        if (name == known.Box || name == known.Rc)
            && scope.infer_cell.is_none()
            && matches!(scope.regions, RegionMode::Erase)
            && let TyKind::Dyn(b, Region::Erased) = tys.kind(elem)
            && let GenericArgs::Angle(a) = &seg.args
            && let Some(AstArg::Type(t)) = a.iter().find(|g| matches!(g, AstArg::Type(_)))
            && dyn_lifetime_unwritten(ast, *t)
        {
            elem = tys.intern(TyKind::Dyn(b, Region::Static));
        }
        // `Box<dyn Tr>` and `Rc<dyn Tr>` are owning fat pointers (ARCH
        // 2.8), `Box<[T]>` a boxed slice (W-STD-A), and `Box<str>`,
        // `Rc<str>`, and `Rc<[T]>` the fat forms of check/own.rs.
        return Ok(if name == known.Vec {
            tys.mk_vec(elem)
        } else if name == known.Box {
            tys.mk_boxed(elem)
        } else if name == known.Rc {
            tys.mk_rc(elem)
        } else {
            tys.mk_option(elem)
        });
    }
    // The sync and thread types (W-THREADS): by their std path, or by a
    // bare name a module glob of their std module imports.
    if let Some(k) = crate::check::sync::sync_type_named(interner, segs) {
        if k.arity() == 0 && k.regions() == 0 {
            return no_generics(crate::ty::sync::sync_ty(tys, k, &[]));
        }
        let args = match &seg.args {
            GenericArgs::Angle(a) if k.arity() == 0 => {
                if a.iter().any(|g| !matches!(g, AstArg::Lifetime(_))) {
                    return Err(Diag::new("L0110", span, format!("`{}` takes no type arguments", k.name()), "Remove the type arguments."));
                }
                Vec::new()
            }
            GenericArgs::Angle(a) => resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, k.name())?,
            GenericArgs::None if k.arity() == 0 => Vec::new(),
            _ => return Err(Diag::new("L0110", span, format!("`{}` takes one type argument", k.name()), "Write it with its element type.")),
        };
        let mut elem = args.iter().find_map(|g| g.as_ty()).unwrap_or(ERROR);
        crate::check::sync::check_sync_arg(tys, k, elem, span)?;
        // `Arc<dyn Tr>` (and `Mutex<dyn Tr>`, `sync::Weak<dyn Tr>`) with
        // no written bound is `'static` in a signature, as for `Box` and
        // `Rc` above.
        if matches!(k, crate::ty::sync::SyncTy::Arc | crate::ty::sync::SyncTy::Mutex | crate::ty::sync::SyncTy::ArcWeak)
            && scope.infer_cell.is_none()
            && matches!(scope.regions, RegionMode::Erase)
            && let TyKind::Dyn(b, Region::Erased) = tys.kind(elem)
            && let GenericArgs::Angle(a) = &seg.args
            && let Some(AstArg::Type(t)) = a.iter().find(|g| matches!(g, AstArg::Type(_)))
            && dyn_lifetime_unwritten(ast, *t)
        {
            elem = tys.intern(TyKind::Dyn(b, Region::Static));
        }
        // Lifetime params (a lock guard's, a scoped handle's, a `Scope`'s
        // two): none written (each elided) or all; a region signature
        // keeps them first, as for a user Adt's lifetimes.
        let n_lts = k.regions() as usize;
        let written: Vec<ast::Lifetime> = match &seg.args {
            GenericArgs::Angle(a) => a.iter().filter_map(|g| if let AstArg::Lifetime(lt) = g { Some(*lt) } else { None }).collect(),
            _ => Vec::new(),
        };
        if !written.is_empty() && written.len() != n_lts {
            return Err(Diag::new("L0110", span, format!("`{}` takes {n_lts} lifetime argument(s), but {} were given", k.name(), written.len()), "Match the number of lifetime parameters."));
        }
        if scope.infer_cell.is_some()
            && !scope.annotation
            && let Some(lt) = written.iter().find(|lt| interner.get(lt.name) != "_")
        {
            return Err(Diag::new(
                "L0203",
                lt.span,
                "an explicit lifetime in a type annotation inside a body is not supported yet",
                "Remove the annotation and let the type be inferred, or write `'_`.",
            ));
        }
        if n_lts > 0 && matches!(scope.regions, RegionMode::Keep { .. }) {
            let def = tys.builtins().sync_tys[k as usize];
            let mut all = Vec::new();
            for i in 0..n_lts {
                all.push(GenericArg::Lifetime(scope_region(interner, scope, written.get(i).copied(), span)?));
            }
            if k.arity() > 0 {
                // A lock guard's `T: ?Sized + 'a`: a dyn arg's object
                // lifetime defaults to the guard's.
                if let Some(GenericArg::Lifetime(r)) = all.first().copied() {
                    elem = bounded_arg_default(ast, tys, seg, elem, r);
                }
                all.push(GenericArg::Ty(elem));
            }
            return Ok(tys.mk_adt(def, &all));
        }
        if k.arity() == 0 {
            return Ok(crate::ty::sync::sync_ty(tys, k, &[]));
        }
        return Ok(crate::ty::sync::sync_ty(tys, k, &[elem]));
    }
    // `Weak<T>`, `RefCell<T>`, `Cell<T>`, and the `RefCell` guards
    // `Ref<'_, T>` / `RefMut<'_, T>` (W-STD-A, R26). A guard's
    // element may be unsized (`Ref<str>`, `RefMut<dyn Tr>`), as in std.
    if let n @ ("Weak" | "RefCell" | "Cell" | "Ref" | "RefMut") = interner.get(name)
        && (std_path || !cx.type_names.contains_key(&name))
    {
        let args = match &seg.args {
            GenericArgs::Angle(a) => resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, n)?,
            _ => return Err(Diag::new("L0110", span, format!("`{n}` takes one type argument"), "Write it with its element type.")),
        };
        let mut elem = args.iter().find_map(|g| g.as_ty()).unwrap_or(ERROR);
        // `RefCell<dyn Tr>` behind a pointer is check/own.rs's, and
        // `Weak<dyn Tr>` is cgen/own.rs's; their object lifetime
        // defaults as for `Box<dyn Tr>`.
        // A guard over `dyn Tr` (`RefMut<'_, dyn Tr>`) takes the guard's
        // lifetime (`T: ?Sized + 'b`, RFC 599): erased here (a caller's
        // lifetime), the guard's region in region signatures. A guard
        // over a `'static` object coerces to it (`Ctx::guard_unsize`).
        let dyn_cell = matches!(n, "RefCell" | "Weak" | "Ref" | "RefMut") && matches!(tys.kind(elem), TyKind::Dyn(..));
        let guard = matches!(n, "Ref" | "RefMut");
        if dyn_cell
            && !guard
            && scope.infer_cell.is_none()
            && matches!(scope.regions, RegionMode::Erase)
            && let TyKind::Dyn(b, Region::Erased) = tys.kind(elem)
            && let GenericArgs::Angle(a) = &seg.args
            && let Some(AstArg::Type(t)) = a.iter().find(|g| matches!(g, AstArg::Type(_)))
            && dyn_lifetime_unwritten(ast, *t)
        {
            elem = tys.intern(TyKind::Dyn(b, Region::Static));
        }
        // `rc::Weak<str>` and `rc::Weak<[T]>` hold the Rc's fat value (cgen/own.rs).
        let weak_fat = n == "Weak" && matches!(tys.kind(elem), TyKind::Slice(_) | TyKind::Str);
        if !dyn_cell && !guard && !weak_fat && matches!(tys.kind(elem), TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..)) {
            return Err(not_yet("L0641", span, &format!("a {n} of an unsized type")));
        }
        let which: fn(&crate::ty::BuiltinDefs) -> DefId = match n {
            "Weak" => |d| d.weak,
            "RefCell" => |d| d.refcell,
            "Ref" => |d| d.ref_guard,
            "RefMut" => |d| d.ref_mut_guard,
            _ => |d| d.cell,
        };
        // A guard keeps its lifetime first in a region signature, like
        // `Cow` and the lock guards, so a returned guard borrows its
        // source (R26).
        if guard && matches!(scope.regions, RegionMode::Keep { .. }) {
            let written = match &seg.args {
                GenericArgs::Angle(a) => a.iter().find_map(|g| if let AstArg::Lifetime(lt) = g { Some(*lt) } else { None }),
                _ => None,
            };
            let r = scope_region(interner, scope, written, span)?;
            let elem = bounded_arg_default(ast, tys, seg, elem, r);
            let def = which(tys.builtins());
            return Ok(tys.mk_adt(def, &[GenericArg::Lifetime(r), GenericArg::Ty(elem)]));
        }
        return Ok(tys.mk_builtin1(which, elem));
    }
    if interner.get(name) == "ExitCode" && (std_path || !cx.type_names.contains_key(&name)) {
        return no_generics(tys.exit_code_ty());
    }
    if name == known.Result && !shadowed {
        let args = match &seg.args {
            GenericArgs::Angle(a) => {
                resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false, false], 2, span, interner.get(name))?
            }
            _ => {
                return Err(Diag::new("L0110", span, "`Result` takes two type arguments".to_string(), "Write `Result<T, E>`."));
            }
        };
        let mut it = args.iter().filter_map(|g| g.as_ty());
        let (t, e) = (it.next().unwrap_or(ERROR), it.next().unwrap_or(ERROR));
        return Ok(tys.mk_result(t, e));
    }
    if std_path && cx.type_names.get(&name).is_none_or(|&a| !is_std_adt(tys, a)) {
        return Err(crate::check::collect::std_path_shadowed(interner, name, span));
    }
    // A type alias declared in an enclosing function-body block
    // shadows the module alias tables (R18).
    if segs.len() == 1
        && let Some(&(_, alias_ty)) = scope.local_aliases.iter().rev().find(|(n, _)| *n == name)
    {
        return if seg.has_args() {
            Err(Diag::new("L0110", span, "this alias takes no generic arguments", "Remove the `<...>` part."))
        } else {
            alias_at_use(ast, interner, known, cx, tys, scope, alias_ty, AliasBody::Local, span)
        };
    }
    if segs.len() == 1
        && let Some(la) = cx.generic_aliases.get(&name)
    {
        return resolve_generic_alias(ast, interner, known, cx, tys, scope, la, seg, span);
    }
    if segs.len() == 1
        && let Some(&alias_ty) = cx.aliases.get(&name)
    {
        let g_ast = crate::check::defaults::type_generics(ast, cx, name);
        let kinds: Vec<bool> = g_ast.map_or_else(Vec::new, |g| {
            g.params
                .iter()
                .filter_map(|p| match p {
                    ast::GenericParam::Type { .. } => Some(false),
                    ast::GenericParam::Const { .. } => Some(true),
                    ast::GenericParam::Lifetime { .. } => None,
                })
                .collect()
        });
        let body = AliasBody::Module(module_alias_body(ast, cx, name));
        let alias_ty = alias_at_use(ast, interner, known, cx, tys, scope, alias_ty, body, span)?;
        if kinds.is_empty() {
            return if seg.has_args() {
                Err(Diag::new("L0110", span, "this alias takes no generic arguments", "Remove the `<...>` part."))
            } else {
                Ok(alias_ty)
            };
        }
        // A generic alias: its args (defaults for omitted trailing ones)
        // substitute into the target.
        let what = crate::intern::source_name(interner.get(name));
        let mut args: Vec<GenericArg> = match &seg.args {
            GenericArgs::None => Vec::new(),
            GenericArgs::Angle(a) => {
                let min = g_ast.map_or(kinds.len(), crate::check::defaults::required);
                resolve_generic_args(ast, interner, known, cx, tys, scope, a, &kinds, min, span, what)?
            }
            GenericArgs::Parenthesized { .. } => {
                return Err(Diag::new("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments."));
            }
        };
        if args.iter().any(|g| matches!(g, GenericArg::Lifetime(_))) {
            return Err(Diag::new("L0110", span, "this alias takes no lifetime arguments", "Remove the lifetime arguments."));
        }
        if let Some(g) = g_ast {
            crate::check::defaults::fill(ast, interner, known, cx, tys, scope, g, None, &mut args, span)?;
        }
        if args.len() != kinds.len() {
            return Err(Diag::new(
                "L0110",
                span,
                format!("`{what}` takes {} generic argument(s)", kinds.len()),
                "Write the arguments, for example with `_` where inference should fill them in a body.",
            ));
        }
        return Ok(subst(tys, alias_ty, &args));
    }
    }
    // A type item declared in an enclosing function-body block
    // shadows the flat module table (R18).
    let local_adt = scope.local_types.iter().rev().find(|(n, _, _)| *n == name);
    if let Some(&adt) = local_adt.map_or_else(|| cx.type_names.get(&name), |e| Some(&e.1)) {
        let (def, n_params) = cx.adt_info_of(adt);
        // Declared parameter kinds and defaults from the Adt's own item:
        // its built generics may not exist yet when an earlier item's
        // fields name it.
        let g_ast = match local_adt {
            Some(e) => e.2.as_ref(),
            None => crate::check::defaults::type_generics(ast, cx, name),
        };
        let arity = || {
            Diag::new(
                "L0110",
                span,
                format!("`{}` takes {n_params} generic argument(s)", crate::intern::source_name(interner.get(name))),
                "Write the arguments, for example with `_` where inference should fill them in a body.",
            )
        };
        let mut gargs: Vec<GenericArg> = match &seg.args {
            GenericArgs::None => Vec::new(),
            GenericArgs::Angle(a) => {
                let kinds: Vec<bool> = g_ast
                    .map(|g| {
                        g.params
                            .iter()
                            .filter_map(|p| match p {
                                ast::GenericParam::Type { .. } => Some(false),
                                ast::GenericParam::Const { .. } => Some(true),
                                ast::GenericParam::Lifetime { .. } => None,
                            })
                            .collect()
                    })
                    .unwrap_or_else(|| vec![false; n_params]);
                let min = g_ast.map_or(n_params, crate::check::defaults::required);
                resolve_generic_args(
                    ast,
                    interner,
                    known,
                    cx,
                    tys,
                    scope,
                    a,
                    &kinds,
                    min,
                    span,
                    crate::intern::source_name(interner.get(name)),
                )?
            }
            GenericArgs::Parenthesized { .. } => {
                return Err(Diag::new("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments."));
            }
        };
        if let Some(g) = g_ast {
            let written = match &seg.args {
                GenericArgs::Angle(a) => a.as_slice(),
                _ => &[],
            };
            check_const_arg_types(ast, interner, known, cx, tys, scope, g, written, &gargs, span)?;
        }
        // Omitted trailing params take their defaults.
        let n_written = gargs.iter().filter(|g| !matches!(g, GenericArg::Lifetime(_))).count();
        if n_written < n_params {
            let mut values: Vec<GenericArg> = gargs.iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
            if let Some(g) = g_ast {
                crate::check::defaults::fill(ast, interner, known, cx, tys, scope, g, None, &mut values, span)?;
            }
            if values.len() != n_params {
                return Err(arity());
            }
            gargs.extend_from_slice(&values[n_written..]);
        }
        // Lifetime args (W-BORROW): none written (each elided), or one
        // per declared lifetime param (rustc E0107 otherwise). The erased
        // type drops them; a region signature keeps them first, in
        // declared order (`Region::Param` or `'static`).
        let n_lts = cx.adt_lifetimes.get(&def).map_or(0, |v| v.len());
        let written: Vec<ast::Lifetime> = match &seg.args {
            GenericArgs::Angle(a) => a.iter().filter_map(|g| if let AstArg::Lifetime(lt) = g { Some(*lt) } else { None }).collect(),
            _ => Vec::new(),
        };
        if scope.infer_cell.is_some()
            && !scope.annotation
            && let Some(lt) = written.iter().find(|lt| interner.get(lt.name) != "_")
        {
            return Err(Diag::new(
                "L0203",
                lt.span,
                "an explicit lifetime in a type annotation inside a body is not supported yet",
                "Remove the annotation and let the type be inferred, or write `'_`.",
            ));
        }
        if !written.is_empty() && written.len() != n_lts {
            return Err(Diag::new(
                "L0110",
                span,
                format!(
                    "`{}` takes {n_lts} lifetime argument(s), but {} were given",
                    crate::intern::source_name(interner.get(name)),
                    written.len()
                ),
                "Match the number of lifetime parameters in the definition.",
            ));
        }
        let gargs: Vec<GenericArg> = gargs.into_iter().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
        if n_lts > 0 && matches!(scope.regions, RegionMode::Keep { .. }) {
            let mut all: Vec<GenericArg> = Vec::with_capacity(n_lts + gargs.len());
            for i in 0..n_lts {
                // In a dyn's `Fn*` sugar an elided one is the object's (R11).
                all.push(GenericArg::Lifetime(ref_region(interner, scope, written.get(i).copied(), span)?));
            }
            all.extend(gargs);
            return Ok(tys.mk_adt(def, &all));
        }
        // In a dyn's trait args (R11) an elided lifetime of `Fn*` sugar is
        // the object's own, late-bound: the erased Adt keeps its lifetime
        // args then, `DYN_LATE` there, and so it does for a written
        // `'static` (a written named one is free, `Erased`).
        let kept = |lt: &ast::Lifetime| matches!(interner.get(lt.name), "_" | "static");
        if n_lts > 0 && scope.dyn_args && ((scope.late_elided && written.is_empty()) || written.iter().any(kept)) {
            let mut all: Vec<GenericArg> = Vec::with_capacity(n_lts + gargs.len());
            for i in 0..n_lts {
                all.push(GenericArg::Lifetime(match written.get(i).map(|lt| interner.get(lt.name)) {
                    Some("static") => Region::Static,
                    Some(n) if n != "_" => Region::Erased,
                    _ => ref_region(interner, scope, None, span)?,
                }));
            }
            all.extend(gargs);
            return Ok(tys.mk_adt(def, &all));
        }
        return Ok(tys.mk_adt(def, &gargs));
    }
    let n = interner.get(name);
    if ["BTreeMap", "Box", "Rc", "Arc"].contains(&n) {
        return Err(not_yet("L0641", span, &format!("the `{n}` type")));
    }
    if let Some(k) = crate::ty::hash::HashTy::by_name(n) {
        return Err(crate::ty::hash::not_imported(k, span));
    }
    // A user trait in a type position (rustc E0782): name the trait by
    // its source path, not its flat name.
    if cx.trait_names.contains_key(&name) {
        return Err(Diag::new(
            "L0102",
            span,
            format!("expected a type, found trait `{}`", crate::intern::source_path(n)),
            "Write `dyn Trait` for a trait object, or name a type.",
        ));
    }
    Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."))
}

/// `std::borrow::Cow<'a, B>` (W-STD-B): the synthetic enum at `B`, its
/// lifetime kept first in a region signature like a user Adt's.
#[allow(clippy::too_many_arguments)]
fn resolve_cow_path(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    seg: &ast::PathSeg,
    span: Span,
) -> Result<Ty, Diag> {
    let usage = || Diag::new("L0110", span, "`Cow` takes one type argument", "Write `Cow<'a, str>`, for example.");
    let GenericArgs::Angle(a) = &seg.args else { return Err(usage()) };
    let written: Vec<ast::Lifetime> = a.iter().filter_map(|g| if let AstArg::Lifetime(lt) = g { Some(*lt) } else { None }).collect();
    if written.len() > 1 {
        return Err(Diag::new("L0110", span, "`Cow` takes 1 lifetime argument", "Write one lifetime, or none."));
    }
    let args: Vec<GenericArg> = resolve_generic_args(ast, interner, known, cx, tys, scope, a, &[false], 1, span, "Cow")?
        .into_iter()
        .filter(|g| g.as_ty().is_some())
        .collect();
    if args.len() != 1 {
        return Err(usage());
    }
    if matches!(scope.regions, RegionMode::Keep { .. }) {
        let r = scope_region(interner, scope, written.first().copied(), span)?;
        let elem = args[0].as_ty().map_or(args[0], |t| GenericArg::Ty(bounded_arg_default(ast, tys, seg, t, r)));
        return Ok(tys.mk_adt(cow_def(), &[GenericArg::Lifetime(r), elem]));
    }
    Ok(tys.mk_adt(cow_def(), &args))
}

/// A hashed collection or hasher type by its std path (W-STD-B):
/// type args as written, with the default `S = RandomState` filled.
#[allow(clippy::too_many_arguments)]
fn resolve_hash_path(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    k: crate::ty::hash::HashTy,
    seg: &ast::PathSeg,
    span: Span,
) -> Result<Ty, Diag> {
    use crate::ty::hash::{HashTy, mk_hash};
    let n = k.n_args();
    let written: Vec<Ty> = match &seg.args {
        GenericArgs::None => Vec::new(),
        GenericArgs::Angle(a) => {
            let kinds = vec![false; a.len()];
            resolve_generic_args(ast, interner, known, cx, tys, scope, a, &kinds, kinds.len(), span, k.path().1)?
                .into_iter()
                .filter_map(|g| g.as_ty())
                .collect()
        }
        GenericArgs::Parenthesized { .. } => {
            return Err(Diag::new("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments."));
        }
    };
    let defaults = match k {
        HashTy::HashMap | HashTy::HashSet => 1,
        _ => 0,
    };
    if written.len() > n || written.len() + defaults < n || (written.is_empty() && n > 0) {
        return Err(Diag::new(
            "L0110",
            span,
            format!(
                "`{}` takes {} type argument(s)",
                k.path().1,
                if defaults > 0 { format!("{} or {n}", n - defaults) } else { n.to_string() }
            ),
            "Write the arguments, for example with `_` where inference should fill them in a body.",
        ));
    }
    let mut args = written;
    if args.len() < n {
        args.push(mk_hash(tys, HashTy::RandomState, &[]));
    }
    Ok(mk_hash(tys, k, &args))
}

/// A `core::fmt` type by its last path segment (W-STD-B): the
/// Formatter family (lifetime arguments only), `fmt::Result`, and
/// `fmt::Error`.
fn resolve_fmt_path(
    interner: &Interner,
    tys: &mut impl TyIntern,
    scope: &Scope,
    name: &str,
    seg: &ast::PathSeg,
    span: Span,
) -> Result<Ty, Diag> {
    let only_lifetimes = match &seg.args {
        GenericArgs::None => true,
        GenericArgs::Angle(a) => a.iter().all(|g| matches!(g, ast::GenericArg::Lifetime(_))),
        GenericArgs::Parenthesized { .. } => false,
    };
    if !only_lifetimes {
        return Err(Diag::new("L0110", span, "this type takes no type arguments", "Remove the `<...>` part."));
    }
    match name {
        "Result" if seg.has_args() => Err(Diag::new("L0110", span, "`fmt::Result` takes no generic arguments", "Remove the `<...>` part.")),
        "Result" => Ok(fmt_result_ty(tys)),
        "Error" if seg.has_args() => Err(Diag::new("L0110", span, "`fmt::Error` takes no generic arguments", "Remove the `<...>` part.")),
        "Error" => Ok(fmt_error_ty(tys)),
        _ => match crate::ty::fmt::FmtTy::by_name(name) {
            Some(k) => {
                // In region signatures the written lifetimes stay as
                // lifetime args (like the sync guards above), so a
                // field `Arguments<'a>` uses `'a` and borrowck can
                // relate the field's slot. Erased types keep no args.
                if matches!(scope.regions, RegionMode::Keep { .. }) {
                    let written: Vec<ast::Lifetime> = match &seg.args {
                        GenericArgs::Angle(a) => {
                            a.iter().filter_map(|g| if let ast::GenericArg::Lifetime(lt) = g { Some(*lt) } else { None }).collect()
                        }
                        _ => Vec::new(),
                    };
                    let n_lts = if k.is_builder() { 2 } else { 1 };
                    let mut all = Vec::new();
                    for i in 0..n_lts {
                        all.push(GenericArg::Lifetime(scope_region(interner, scope, written.get(i).copied(), span)?));
                    }
                    let def = tys.builtins().fmt_tys[k as usize];
                    return Ok(tys.mk_adt(def, &all));
                }
                Ok(crate::ty::fmt::fmt_ty(tys, k))
            }
            None => Err(Diag::new("L0102", span, format!("unknown type `{name}`"), "Check the spelling, or define the type.")),
        },
    }
}

/// A use of a generic alias (W-BORROW): lifetime args none (each elided
/// under the use site's rules) or one per param, then type args, missing
/// ones from their defaults (rustc E0107 otherwise); the body resolves in
/// a scope of its own where the alias's lifetimes are the use site's
/// regions and its type params the use site's types.
#[allow(clippy::too_many_arguments)]
fn resolve_generic_alias(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    la: &GenericAlias,
    seg: &ast::PathSeg,
    span: Span,
) -> Result<Ty, Diag> {
    let (written, types, other): (Vec<ast::Lifetime>, Vec<ast::TyId>, bool) = match &seg.args {
        GenericArgs::Angle(a) => (
            a.iter().filter_map(|g| if let AstArg::Lifetime(lt) = g { Some(*lt) } else { None }).collect(),
            a.iter().filter_map(|g| if let AstArg::Type(t) = g { Some(*t) } else { None }).collect(),
            a.iter().any(|g| !matches!(g, AstArg::Lifetime(_) | AstArg::Type(_))),
        ),
        GenericArgs::None => (Vec::new(), Vec::new(), false),
        _ => (Vec::new(), Vec::new(), true),
    };
    let alias = crate::intern::source_name(interner.get(seg.name)).to_string();
    if other {
        return Err(Diag::new("L0110", span, format!("`{alias}` takes lifetime and type arguments only"), "Pass lifetime and type arguments."));
    }
    if !written.is_empty() && written.len() != la.lifetimes.len() {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{alias}` takes {} lifetime argument(s), but {} were given", la.lifetimes.len(), written.len()),
            "Match the number of lifetime parameters in the alias.",
        ));
    }
    let required = la.type_params.iter().take_while(|(_, d)| d.is_none()).count();
    if types.len() > la.type_params.len() || types.len() < required {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{alias}` takes {} type argument(s), but {} were given", la.type_params.len(), types.len()),
            "Match the number of type parameters in the alias.",
        ));
    }
    if scope.infer_cell.is_some()
        && !scope.annotation
        && let Some(lt) = written.iter().find(|lt| interner.get(lt.name) != "_")
    {
        return Err(Diag::new(
            "L0203",
            lt.span,
            "an explicit lifetime in a type annotation inside a body is not supported yet",
            "Remove the annotation and let the type be inferred, or write `'_`.",
        ));
    }
    if scope.alias_depth > 32 {
        return Err(Diag::new("L0601", span, format!("cycle detected in type alias `{alias}`"), "An alias must not name itself, directly or through other aliases."));
    }
    // In a dyn's `Fn*` sugar an elided or `'_` alias arg is the object's
    // own late-bound lifetime (`&dyn Fn(&mut Cb<'_>)`, R11), as for an
    // Adt's (`resolve_path_ty`).
    let mut regions = Vec::with_capacity(la.lifetimes.len());
    for i in 0..la.lifetimes.len() {
        regions.push(ref_region(interner, scope, written.get(i).copied(), span)?);
    }
    // Inside a dyn's trait args the body's dyn types stay the object's
    // (`dyn_args`, R11), as they do written out.
    let mut body = Scope {
        regions: scope.regions.clone(),
        alias_lifetimes: la.lifetimes.iter().copied().zip(regions).collect(),
        alias_depth: scope.alias_depth + 1,
        dyn_args: scope.dyn_args,
        ..Scope::default()
    };
    // Type args resolve where they are written; a default resolves in the
    // alias's scope, where the earlier params are bound.
    for (i, &(name, default)) in la.type_params.iter().enumerate() {
        let t = match types.get(i) {
            Some(&w) => resolve_scoped(ast, interner, known, cx, tys, w, scope)?,
            None => resolve_scoped(ast, interner, known, cx, tys, default.expect("checked arity"), &body)?,
        };
        body.param_tys.push((name, t));
    }
    resolve_scoped(ast, interner, known, cx, tys, la.ty, &body)
}

/// Converts one written bound on `lhs` into predicates. `?Sized`
/// records the parameter index in `relaxed` instead of a
/// predicate (the implicit `Sized` predicate is then withheld by
/// `build_generics`). Lifetime bounds on named lifetimes are the
/// subset's lifetime reject; a `'static` bound is a
/// `TypeOutlives(lhs, 'static)` predicate, which the checker proves
/// where lust tracks lifetimes (type parameters, dyn types; see
/// `Ctx::static_bound_err`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn bound_predicates(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    lhs: Ty,
    bound: &TraitBound,
    out: &mut Vec<Predicate>,
    relaxed: &mut Vec<u32>,
    errs: &mut Vec<Diag>,
) {
    match bound {
        TraitBound::Lifetime(lt) => match check_lifetime(interner, scope, *lt) {
            Err(d) => errs.push(d),
            Ok(_) if interner.get(lt.name) == "static" => out.push(Predicate::TypeOutlives(lhs, Region::Static)),
            // `T: 'a` on a fn or inherent method: its calls prove it.
            Ok(_) if scope.type_outlives
                && matches!(tys.kind(lhs), TyKind::Param(_))
                && let Some(&(_, i)) = scope.lifetimes.iter().find(|(n, _)| *n == lt.name) =>
            {
                out.push(Predicate::TypeOutlives(lhs, Region::Param(i)))
            }
            // Elsewhere `T: 'a` would be a type-outlives obligation at
            // every use; lust proves only `'static` ones there (W-BORROW).
            Ok(_) if interner.get(lt.name) != "_" => errs.push(Diag::new(
                "L0203",
                lt.span,
                "a bound like `T: 'a` on a named lifetime is not supported yet",
                "Remove the bound if the code still checks, or bound the type by `'static`.",
            )),
            // `T: '_` names no lifetime (rustc E0637).
            Ok(_) => errs.push(Diag::new("L0202", lt.span, "`'_` cannot be used here", "Write `'static` or a named lifetime parameter.")),
        },
        TraitBound::Trait { binder, trait_ref, maybe } => {
            let span = trait_ref.path.last().map_or(Span::default(), |_| Span::default());
            let trait_def = match trait_def_of_path(cx, interner, known, &trait_ref.path, span) {
                Ok(d) => d,
                Err(d) => {
                    errs.push(d);
                    return;
                }
            };
            if *maybe {
                if trait_def != cx.lang.sized {
                    errs.push(Diag::new("L0110", span, "only `Sized` may be relaxed with `?`", "Remove the `?`."));
                    return;
                }
                if let TyKind::Param(p) = tys.kind(lhs) {
                    relaxed.push(p.0);
                } else {
                    // A non-parameter left side (an associated type
                    // projection): the caller reads this marker as
                    // "the implicit Sized bound was relaxed".
                    relaxed.push(u32::MAX);
                }
                return;
            }
            if let Err(d) = binder_shadow(interner, scope, binder) {
                errs.push(d);
                return;
            }
            // The parser rewrote a binder's uses to elided lifetimes
            // (`parser::hrtb`); one it could not rewrite stays written and
            // fails to resolve. So no region here is bound by it.
            match resolve_trait_ref(ast, interner, known, cx, tys, scope, lhs, trait_ref, span) {
                Ok(tr) => out.push(Predicate::Trait(Binder::plain(tr))),
                Err(d) => errs.push(d),
            }
        }
    }
}

/// The elaborated param env of one item from its written
/// predicates (section 2.1), through the index's supertraits.
pub fn elaborate_env(tys: &mut impl TyIntern, index: &ImplIndex, written: &[Predicate]) -> Vec<Predicate> {
    crate::traits::solve::elaborate_in(tys, index, written)
}

/// The env a body is checked under (its `FnScope`): the elaborated
/// env minus the global predicates (`is_global_pred`). A global
/// predicate such as `where A: Tr` must hold outright where its item
/// is written (`check_written_wf`); in the body an impl proves it, as
/// in rustc, where a global where-bound never beats an impl, guides
/// inference, or brings its trait into scope. Kept in the env, it
/// selected as param evidence and sent a concrete call to the trait
/// method's stub, which has no body.
pub fn body_env(tys: &mut impl TyIntern, index: &ImplIndex, written: &[Predicate]) -> Vec<Predicate> {
    let mut env = elaborate_env(tys, index, written);
    env.retain(|pred| !is_global_pred(tys, pred));
    env
}

/// True for a predicate lust treats as global: not higher-ranked, and
/// no type or const parameter anywhere in it (args and bindings). That
/// is rustc's global predicate, plus predicates over lifetime
/// parameters only (`where &'a A: Tr`): selection erases regions, so
/// the impl is the callee either way. The impl's region bounds then
/// apply in the body, where rustc leaves them to callers: stricter,
/// so a reject, never a wrong accept. Outlives predicates are never
/// global here: they pick no callee, and region checks read them.
pub fn is_global_pred(tys: &impl TyIntern, pred: &Predicate) -> bool {
    let ty_free = |t: Ty| !tys.flags(t).contains_param();
    let args_free = |a: ArgsId| {
        tys.args(a).iter().all(|g| match g {
            GenericArg::Ty(t) => ty_free(*t),
            GenericArg::Const(c) => !matches!(tys.const_kind(*c), ConstKind::Param(_)),
            GenericArg::Lifetime(_) => true,
        })
    };
    match pred {
        Predicate::Trait(b) => {
            b.count == 0 && args_free(b.value.args) && tys.bindings(b.value.bindings).iter().all(|(_, g)| g.as_ty().is_none_or(ty_free))
        }
        Predicate::AssocEq(b) => b.count == 0 && args_free(b.value.trait_args) && ty_free(b.value.ty),
        Predicate::Outlives(..) | Predicate::TypeOutlives(..) => false,
    }
}

/// The associated sources a set of predicates gives a scope: one
/// per trait predicate, for `Self::Assoc` and `T::Assoc`
/// resolution in the item's other signatures.
pub fn assoc_srcs_of(cx: &ResolveCx, tys: &impl TyIntern, preds: &[Predicate]) -> Vec<AssocSrc> {
    let mut out = Vec::new();
    for p in preds {
        if let Predicate::Trait(b) = p
            && let Some(rec) = cx.index.trait_record(b.value.def)
            && !rec.assoc_items.is_empty()
        {
            out.push(AssocSrc {
                self_ty: tys.args(b.value.args)[0].as_ty().unwrap_or(ERROR),
                trait_def: b.value.def,
                args: b.value.args,
                assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
            });
        }
    }
    out
}

/// Builds the semantic `Generics` of one item (params without the
/// `Self` a trait prepends; traits go through `build_trait_generics`)
/// and the scope its signatures resolve under. Lifetime parameters
/// are the subset's lifetime reject, as are parameter defaults.
#[allow(clippy::too_many_arguments)]
pub fn build_generics(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    build_generics_shifted(ast, interner, known, cx, tys, g, w, 0, &Scope::default(), errs)
}

/// `build_generics` with parameter indexes shifted by `shift`
/// (a trait's synthetic `Self` at 0, or an impl's parameters
/// before a method's own). `seed` is the enclosing scope (an
/// impl's or trait's parameters): bounds on these parameters
/// may name the seed's parameters, so pass 2 resolves through
/// seed ++ own. The returned scope holds only the own
/// parameters; callers merge as before.
#[allow(clippy::too_many_arguments)]
pub fn build_generics_shifted(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    shift: u32,
    seed: &Scope,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    build_generics_owned(ast, interner, known, cx, tys, g, w, shift, seed, crate::check::defaults::Owner::Other, errs)
}

/// The generics of a struct or enum: like `build_generics`, but its
/// params may have defaults (`check::defaults`).
#[allow(clippy::too_many_arguments)]
pub fn build_adt_generics(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    build_generics_owned(ast, interner, known, cx, tys, g, w, 0, &Scope::default(), crate::check::defaults::Owner::Type, errs)
}

/// `build_generics_shifted` for an item of the given kind: only structs,
/// enums, traits, and aliases may write param defaults.
#[allow(clippy::too_many_arguments)]
fn build_generics_owned(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    shift: u32,
    seed: &Scope,
    owner: crate::check::defaults::Owner,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    crate::check::defaults::check_written(ast, known, g, owner, errs);
    let mut params: Vec<ParamDef> = Vec::new();
    let mut scope = Scope::default();
    // Pass 0 (W-BORROW): lifetime params. They do not enter `params`
    // (type param indexes stay as before); they number the item's
    // universal regions after the enclosing item's, in written order.
    for p in &g.params {
        if let ast::GenericParam::Lifetime { lt, .. } = p {
            let name = interner.get(lt.name);
            if name == "static" || name == "_" {
                errs.push(Diag::new(
                    "L0203",
                    lt.span,
                    format!("invalid lifetime parameter name: `'{name}` is reserved"),
                    "Pick another name, such as `'a`.",
                ));
                continue;
            }
            if scope.lifetimes.iter().chain(&seed.lifetimes).any(|(n, _)| *n == lt.name) {
                errs.push(Diag::new(
                    "L0106",
                    lt.span,
                    format!("the lifetime `'{name}` is already declared on this item or an enclosing one"),
                    "Rename one of the lifetime parameters.",
                ));
                continue;
            }
            let idx = (seed.lifetimes.len() + scope.lifetimes.len()) as u32;
            scope.lifetimes.push((lt.name, idx));
        }
    }
    // `'a: 'b` facts, from the params and the where clause. Their names
    // resolve through the enclosing item's lifetimes and the own ones.
    {
        let find = |n: Sym| seed.lifetimes.iter().chain(&scope.lifetimes).find(|(m, _)| *m == n).map(|&(_, i)| i);
        let mut facts: Vec<(u32, u32)> = Vec::new();
        let mut fact = |a: &ast::Lifetime, b: &ast::Lifetime, errs: &mut Vec<Diag>| {
            let (an, bn) = (interner.get(a.name), interner.get(b.name));
            match (find(a.name), find(b.name), bn) {
                // `'a: 'static`: `'a` is `'static` (`STATIC_FACT` stands for it).
                (Some(x), _, "static") => facts.push((x, STATIC_FACT)),
                (Some(x), Some(y), _) => facts.push((x, y)),
                (None, _, _) if an != "static" => errs.push(lifetime_diag_undeclared(interner, *a)),
                (_, None, _) if bn != "static" => errs.push(lifetime_diag_undeclared(interner, *b)),
                _ => {}
            }
        };
        for p in &g.params {
            if let ast::GenericParam::Lifetime { lt, bounds, .. } = p {
                for b in bounds {
                    fact(lt, b, errs);
                }
            }
        }
        for pred in &w.preds {
            if let ast::WherePred::Lifetime { lt, bounds } = pred {
                for b in bounds {
                    fact(lt, b, errs);
                }
            }
        }
        scope.region_facts = facts;
    }
    let mut rscope_lt = seed.lifetimes.clone();
    rscope_lt.extend(scope.lifetimes.iter().copied());
    // Pass 1: parameter list and names. Indexes count type and
    // const parameters together, in written order.
    for p in &g.params {
        match p {
            ast::GenericParam::Lifetime { .. } => {}
            ast::GenericParam::Type { name, span, default, .. } => {
                // One name, one parameter in a list (rustc E0403). Type and
                // const parameters share the list's namespace; lifetimes do not.
                if params.iter().any(|q| q.name == *name) {
                    errs.push(Diag::new(
                        "L0106",
                        *span,
                        format!("the parameter `{}` is already used for a parameter of an enclosing item", interner.get(*name)),
                        "Rename one of the parameters.",
                    ));
                }
                let _ = default;
                let idx = shift + params.len() as u32;
                scope.type_params.push((*name, idx));
                params.push(ParamDef { name: *name, kind: ParamKind::Type, span: *span });
            }
            ast::GenericParam::Const { name, span, ty, default, .. } => {
                if params.iter().any(|q| q.name == *name) {
                    errs.push(Diag::new(
                        "L0106",
                        *span,
                        format!("the parameter `{}` is already used for a parameter of an enclosing item", interner.get(*name)),
                        "Rename one of the parameters.",
                    ));
                }
                let _ = default;
                let idx = shift + params.len() as u32;
                let cty = resolve_scoped(ast, interner, known, cx, tys, *ty, &scope).unwrap_or_else(|d| {
                    errs.push(d);
                    ERROR
                });
                if cty != ERROR && ConstScalar::of(tys, cty).is_none() {
                    errs.push(Diag::new(
                        "L0110",
                        *span,
                        "this type is forbidden as the type of a const generic parameter",
                        "Use an integer type, `bool`, or `char`.",
                    ));
                }
                scope.const_params.push((*name, idx, cty));
                params.push(ParamDef { name: *name, kind: ParamKind::Const(cty), span: *span });
            }
        }
    }
    // Pass 2: bounds on parameters, then where predicates. Each
    // parameter's sources join the scope as they are built, so a
    // later bound may name an earlier parameter's assoc types.
    // Resolution runs through the seed ++ own scope (`rscope`);
    // the returned `scope` keeps only the own parameters.
    let mut rscope = seed.clone();
    rscope.lifetimes = rscope_lt;
    rscope.type_params.extend(scope.type_params.iter().copied());
    rscope.const_params.extend(scope.const_params.iter().copied());
    rscope.param_tys.extend(scope.type_params.iter().map(|&(n, i)| (n, tys.intern(TyKind::Param(ParamId(i))))));
    let mut predicates: Vec<Predicate> = Vec::new();
    let mut relaxed: Vec<u32> = Vec::new();
    let mut type_param_tys: Vec<(u32, Ty)> = Vec::new();
    for (name, idx) in &scope.type_params {
        let t = tys.intern(TyKind::Param(ParamId(*idx)));
        type_param_tys.push((*idx, t));
        let _ = name;
    }
    for p in &g.params {
        if let ast::GenericParam::Type { name, bounds, .. } = p
            && let Some(idx) = scope.param_of(*name)
        {
            let lhs = tys.intern(TyKind::Param(ParamId(idx)));
            for b in bounds {
                errs.extend(bound_elided_ref(ast, interner, b).map(e0637));
                bound_predicates(ast, interner, known, cx, tys, &rscope, lhs, b, &mut predicates, &mut relaxed, errs);
            }
            scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
            rscope.assoc_srcs.clone_from(&seed.assoc_srcs);
            rscope.assoc_srcs.extend(scope.assoc_srcs.iter().cloned());
        }
    }
    for pred in &w.preds {
        match pred {
            ast::WherePred::Lifetime { .. } => {}
            ast::WherePred::Type { binder, ty, bounds } => {
                // A `for<'a>` binder on the predicate binds the
                // lifetimes its type and bounds name. Checker types
                // are region-erased, so its predicates are plain
                // here, as for a bound's own `for<..>` binder
                // (`bound_predicates`); the region distinction is
                // the borrow checker's, read from the AST.
                if let Err(d) = binder_shadow(interner, &rscope, binder) {
                    errs.push(d);
                    continue;
                }
                let mut bscope = rscope.clone();
                for (i, lt) in binder.iter().enumerate() {
                    bscope.alias_lifetimes.push((lt.name, Region::Bound(i as u32)));
                }
                errs.extend(elided_ref(ast, interner, *ty).map(e0637));
                match resolve_scoped(ast, interner, known, cx, tys, *ty, &bscope) {
                    Ok(lhs) => {
                        for b in bounds {
                            errs.extend(bound_elided_ref(ast, interner, b).map(e0637));
                            bound_predicates(ast, interner, known, cx, tys, &bscope, lhs, b, &mut predicates, &mut relaxed, errs);
                        }
                        scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
                        rscope.assoc_srcs.clone_from(&seed.assoc_srcs);
                        rscope.assoc_srcs.extend(scope.assoc_srcs.iter().cloned());
                    }
                    Err(d) => errs.push(d),
                }
            }
        }
    }
    // The implicit `Sized` bound on every type parameter that did
    // not write `?Sized` (section 2.7).
    for (idx, t) in &type_param_tys {
        if !relaxed.contains(idx) {
            let args = tys.intern_args(&[GenericArg::Ty(*t)]);
            predicates.push(Predicate::Trait(Binder::plain(TraitRef { def: cx.lang.sized, args, bindings: EMPTY_BINDINGS })));
        }
    }
    scope.param_tys = type_param_tys
        .iter()
        .map(|(idx, t)| {
            let name = scope.type_params.iter().find(|(_, i)| i == idx).map_or(Sym(0), |(n, _)| *n);
            (name, *t)
        })
        .collect();
    (Generics { parent: None, params, predicates }, scope)
}

/// The span of the first lifetime argument a trait ref writes, if any.
fn trait_ref_lifetime_span(tref: &ast::TraitRefExpr) -> Option<Span> {
    tref.path.iter().find_map(|seg| match &seg.args {
        GenericArgs::Angle(a) => a.iter().find_map(|g| if let AstArg::Lifetime(lt) = g { Some(lt.span) } else { None }),
        _ => None,
    })
}

/// A trait's generics: the synthetic `Self` parameter at index 0,
/// then the written parameters. The returned scope resolves the
/// trait's own items (its `Self` type is `Param(0)` and its assoc
/// sources are its supertraits, filled in by collect once the
/// trait record exists).
#[allow(clippy::too_many_arguments)]
pub fn build_trait_generics(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    supertraits: &[TraitBound],
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    let self_ty = tys.intern(TyKind::Param(ParamId(0)));
    // `Self` resolves in the trait's own bounds and `where` clauses
    // (`trait T where Self: Sized`), so the seed scope names it.
    let seed = Scope { self_ty: Some(self_ty), ..Scope::default() };
    // Lifetime params are the trait's own regions (W-BORROW): its methods'
    // universals `0..n`, instantiated by a bound's or an impl header's
    // lifetime args. A supertrait or a `Self` where-clause naming a
    // lifetime would need its own region replay at every impl (Sol review
    // P0.5), so a lifetime arg in the trait's own bounds is a stated cut.
    for b in supertraits.iter().chain(w.preds.iter().flat_map(|p| match p {
        ast::WherePred::Type { bounds, .. } => bounds.as_slice(),
        _ => &[],
    })) {
        if let TraitBound::Trait { trait_ref, .. } = b
            && let Some(lt_span) = trait_ref_lifetime_span(trait_ref)
        {
            errs.push(Diag::new(
                "L0203",
                lt_span,
                "lifetime arguments in a trait's own bounds are not supported yet",
                "Move the bound onto the methods or impls that need it.",
            ));
        }
    }
    let (mut generics, mut scope) =
        build_generics_owned(ast, interner, known, cx, tys, g, w, 1, &seed, crate::check::defaults::Owner::Trait, errs);
    generics.params.insert(0, ParamDef { name: known.self_type, kind: ParamKind::Type, span: Span::default() });
    scope.self_ty = Some(self_ty);
    // Supertrait bounds are predicates on Self, in source order,
    // ahead of the parameter bounds built above.
    let mut preds: Vec<Predicate> = Vec::new();
    let mut relaxed: Vec<u32> = Vec::new();
    for b in supertraits {
        bound_predicates(ast, interner, known, cx, tys, &scope, self_ty, b, &mut preds, &mut relaxed, errs);
    }
    preds.extend(std::mem::take(&mut generics.predicates));
    generics.predicates = preds;
    scope.assoc_srcs = assoc_srcs_of(cx, tys, &generics.predicates);
    (generics, scope)
}

/// The target index a `'a: 'static` fact has in `Scope::region_facts`.
pub const STATIC_FACT: u32 = u32::MAX;

/// The checking scope of one fn: its elaborated param env and the
/// naming scope its body annotations resolve under. For an
/// instance both are substituted with the instance args, so a
/// body never sees a `Param` type outside its template check.
#[derive(Clone, Debug, Default)]
pub struct FnScope {
    pub env: Vec<Predicate>,
    pub scope: Scope,
}

/// One generic fn or method in template form: combined generics
/// (parent impl/trait params first, then its own) and the
/// elaborated env. The signature tys themselves live in the
/// template's `FnInfo` (for AST fns) or `TraitMethodTemplate`.
#[derive(Clone, Debug)]
pub struct FnTemplate {
    pub generics: Generics,
    /// The same env as the template's `FnScope`; bodies read that one.
    #[allow(dead_code)]
    pub env: Vec<Predicate>,
}

/// One trait method in template form. Trait methods are not AST
/// fns in the driver's count, so they live here, not in `fns`;
/// mono materializes them into `fns` per instance when an impl
/// uses a default body, and checks signatures against them.
#[derive(Clone)]
pub struct TraitMethodTemplate {
    /// The method's def in its trait (`FnLoc::Trait`).
    pub loc: crate::check::collect::FnLoc,
    pub name: Sym,
    pub self_kind: Option<ast::SelfKind>,
    /// Parameter types including `self` first, over the combined
    /// generics (trait params with Self at 0, then method params).
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub ret_borrows_from: Option<usize>,
    pub generics: Generics,
    pub env: Vec<Predicate>,
    pub scope: Scope,
}

impl TraitMethodTemplate {
    /// The method's def in `ast` (the program's Ast).
    pub fn def<'x>(&self, ast: &'x Ast) -> &'x ast::FnDef {
        self.loc.def(ast)
    }
}

/// What one entry of `Program::fns` is, for the driver: only
/// `Plain` and `Instance` fns are checked, lowered, and codegen'd
/// by the driver. Templates are checked once each by mono, against
/// their param env (`template_check`); stubs only carry the
/// signatures of trait methods for template bodies.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum FnClass {
    #[default]
    Plain,
    Template,
    Instance,
    Stub,
    /// A closure body fn of a plain fn or a concrete instance (ARCH
    /// 2.9): checked as its parent, lowered from the closure body,
    /// and generated like any instance.
    Closure,
    /// A closure body fn of a template check: borrow-checked only,
    /// never generated.
    TemplateClosure,
}

/// One closure registered by mono: its parent fn (the body it is
/// checked in), its body fn, and its kind and signature in global
/// types. Calls and Fn selection in other bodies read the facts from
/// here (iface: lowering and cgen read `body_fn`).
#[derive(Clone, Debug)]
pub struct ClosureEntry {
    pub parent: LocalDefId,
    pub body_fn: LocalDefId,
    pub kind: crate::check::closure::ClosureKind,
    pub inputs: Vec<Ty>,
    pub output: Ty,
    /// `ClosureInfo::free_args` (W-BORROW).
    pub free_args: Option<Vec<bool>>,
    /// `ClosureInfo::scope_body` (W-THREADS).
    pub scope_body: bool,
    /// `ClosureInfo::input_regions` (W-BORROW).
    pub input_regions: Vec<Option<Ty>>,
    /// `ClosureInfo::output_region` (W-BORROW).
    pub output_region: Option<Ty>,
    /// `ClosureInfo::bound_output` (W-BORROW).
    pub bound_output: Option<Ty>,
    /// `ClosureInfo::bound_inputs` (W-BORROW).
    pub bound_inputs: Vec<Ty>,
    /// `ClosureInfo::call_out` (W-BORROW).
    pub call_out: bool,
    /// `ClosureInfo::free_sig` (W-BORROW).
    pub free_sig: bool,
}

/// One return-position `impl Trait` (ARCH 2.11): the fn that defines it
/// and its written bounds, over the fn's params with the opaque itself as
/// one more param (`Param(n)` for a fn with `n` params). Callers see only
/// these bounds; the defining body gives the hidden type (`check::opaque`).
#[derive(Clone, Debug)]
pub struct OpaqueInfo {
    pub owner: DefId,
    pub bounds: Vec<Predicate>,
    /// Its `Fn*(..) -> R` bounds with regions (`FnBound`, param
    /// `RPIT_PARAM`): a returned closure's output slots take theirs
    /// (`rpit_bound_output`).
    pub fn_outs: Vec<crate::borrowck::FnBound>,
    /// An `Iterator<Item = T>` bound's `T` with regions (named lifetimes
    /// `Region::Param`, `'static`): the defining body's returned items
    /// must outlive them (`Builder::rpit_item_edges`).
    pub item_out: Option<Ty>,
    /// The written lifetime bounds (`+ 'a`, `+ 'static`) as regions: every
    /// region of the returned value outlives them.
    pub outlives: Vec<Region>,
}

/// `OpaqueInfo::item_out` and `OpaqueInfo::outlives` of the bounds of a
/// return-position `impl Trait`. An elided lifetime in the item type is
/// `Region::Erased` (borrowck takes the fn's output elision lifetime,
/// `output_elision`); `+ '_` gives no outlives region.
fn rpit_region_bounds(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    bounds: &[TraitBound],
) -> (Option<Ty>, Vec<Region>) {
    let mut ks = scope.clone();
    ks.fn_ptr_free = false;
    ks.regions = RegionMode::Keep { next: None, elided: Some(Region::Erased) };
    let (mut item, mut outlives) = (None, Vec::new());
    for b in bounds {
        match b {
            TraitBound::Lifetime(lt) => match interner.get(lt.name) {
                "static" => outlives.push(Region::Static),
                "_" => {}
                _ => outlives.extend(scope.lifetimes.iter().find(|(n, _)| *n == lt.name).map(|&(_, i)| Region::Param(i))),
            },
            TraitBound::Trait { trait_ref, .. } => {
                let Some(seg) = trait_ref.path.last() else { continue };
                if interner.get(seg.name) != "Iterator" {
                    continue;
                }
                let GenericArgs::Angle(args) = &seg.args else { continue };
                for g in args {
                    if let AstArg::Binding { name, kind: ast::BindingKind::EqTy(t), .. } = g
                        && interner.get(*name) == "Item"
                    {
                        item = resolve_scoped(ast, interner, known, cx, tys, *t, &ks).ok();
                    }
                }
            }
        }
    }
    (item, outlives)
}

/// The def of the return-position `impl Trait` of one fn.
pub fn opaque_def(owner: DefId) -> DefId {
    DefId { krate: owner.krate, hash: crate::def::child_hash(owner.hash, crate::def::DefKind::Assoc, "{opaque}", 0) }
}

/// A template's capture analysis without types: (root local,
/// projections, mode) per capture, in capture order.
pub type CaptureShape = (u32, Vec<crate::ir::Proj>, crate::check::closure::CaptureMode);

/// One materialized fn instance: its template and concrete args
/// (combined parent+own order). Lowering reads `template_local`
/// today; the rest is the instance's identity for slot and
/// cache keys, kept with the record it belongs to.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct InstanceInfo {
    pub template_def: DefId,
    pub template_local: Option<LocalDefId>,
    pub args: ArgsId,
}

/// The generic tables of one program, built by collect and read
/// by check, mono, and the driver. Parallel vecs are indexed by
/// the session-local `AdtId` / `LocalDefId` of the compat tables
/// in `Program`, including the instances mono appends.
pub struct GenTables {
    pub lang: LangTraits,
    pub index: ImplIndex,
    pub trait_names: crate::driver::read_cover::NameMap<DefId>,
    pub trait_scopes: FxMap<DefId, Scope>,
    pub trait_methods: FxMap<DefId, TraitMethodTemplate>,
    /// Signatures of the lang trait methods, by method def
    /// (`lang_method_sigs`, built from the lang trait records in
    /// `init_lang`): the lang counterpart of `trait_methods`.
    pub lang_method_sigs: FxMap<DefId, LangMethodSig>,
    /// Associated type defaults from trait definitions, in trait
    /// signature form (over the trait's params, Self at 0).
    pub trait_assoc_defaults: FxMap<DefId, Ty>,
    /// User traits written `unsafe trait`: their impls must be
    /// `unsafe impl`, and no other impl may be.
    pub trait_unsafe: FxMap<DefId, bool>,
    /// Associated consts of user traits: the written type (over
    /// the trait's params) and whether a default value is given.
    pub trait_assoc_consts: FxMap<DefId, (Ty, bool)>,
    /// Inherent impl headers awaiting the finish-side WF check:
    /// (Self pattern, impl generics, span). Trait impls are
    /// read back from their index records instead.
    pub wf_headers: Vec<(Ty, Generics, Span)>,
    /// Per user Adt (templates first, instances appended): the
    /// template def and declared parameter count.
    pub adt_info: Vec<(DefId, usize)>,
    /// The lifetime param names of each user Adt template, by def
    /// (W-BORROW). They are not in `adt_generics`: lifetimes leave type
    /// param indexes and instance keys as before.
    pub adt_lifetimes: FxMap<DefId, Vec<Sym>>,
    /// Generic type aliases, by name (W-BORROW).
    pub generic_aliases: crate::driver::read_cover::NameMap<GenericAlias>,
    pub adt_generics: Vec<Generics>,
    pub adt_envs: Vec<Vec<Predicate>>,
    pub adt_scopes: Vec<Scope>,
    /// The (template def, concrete args) a materialized Adt is an
    /// instance of. None for templates and plain Adts.
    pub adt_instance_of: Vec<Option<(DefId, ArgsId)>>,
    pub fn_templates: Vec<Option<FnTemplate>>,
    pub fn_scopes: Vec<FnScope>,
    pub fn_class: Vec<FnClass>,
    pub instances: crate::check::spec::Logged<LocalDefId, InstanceInfo, { crate::check::spec::tab::INSTANCES }>,
    /// Every registered closure by its def (ARCH 2.9).
    pub closures: crate::check::spec::Logged<DefId, ClosureEntry, { crate::check::spec::tab::CLOSURES }>,
    /// Closure body fns back to their closure def.
    pub closure_fns: crate::check::spec::Logged<LocalDefId, DefId, { crate::check::spec::tab::CLOSURE_FNS }>,
    /// Each template's closures as its template check analyzed them:
    /// (template, closure expr) to kind and capture shapes. Concrete
    /// instances reuse these, so captures follow the generic body.
    pub template_closures: crate::check::spec::Logged<(LocalDefId, ast::ExprId), (crate::check::closure::ClosureKind, Vec<CaptureShape>), { crate::check::spec::tab::TEMPLATE_CLOSURES }>,
    /// The Fn trait each closure call in a template goes through
    /// (from its template check), by (template, call expr).
    pub template_calls: crate::check::spec::Logged<(LocalDefId, ast::ExprId), crate::check::closure::ClosureKind, { crate::check::spec::tab::TEMPLATE_CALLS }>,
    pub instance_by_key: crate::check::spec::Logged<(DefId, ArgsId), LocalDefId, { crate::check::spec::tab::INSTANCE_BY_KEY }>,
    /// Inherent method templates by (Adt template def, name), in
    /// registration order; disjoint Self patterns may share a name.
    pub inherent_methods: FxMap<(DefId, Sym), Vec<LocalDefId>>,
    /// Every fn in `inherent_methods`, built at the first ask
    /// (`is_inherent_template`): collect fills `inherent_methods` before
    /// mono makes any instance, and nothing changes it after.
    pub inherent_tmpls: std::sync::OnceLock<FxMap<LocalDefId, ()>>,
    /// Inherent methods std source defines on a primitive type
    /// (`impl char` in `core::char`, TRIAGE T8), by (Self type,
    /// name). User source cannot add inherent impls on primitives.
    pub prim_inherent_methods: FxMap<(Ty, Sym), Vec<LocalDefId>>,
    /// Each inherent method's impl Self pattern and impl generics,
    /// for the inherent overlap check in `finish_collect`.
    pub inherent_self_pats: FxMap<LocalDefId, (Ty, Generics)>,
    /// Each inherent impl's Self pattern and generics, by impl
    /// def: associated const registration reads them back (the
    /// const tables build after the fn pass).
    pub inherent_impl_self: FxMap<DefId, (Ty, Generics)>,
    /// Each inherent associated const's impl Self pattern, impl
    /// generics, and item span, by const index: use sites pick
    /// among same-name consts by their written Self type.
    pub inherent_const_self: FxMap<u32, (Ty, Generics, Span)>,
    /// Associated consts whose initializer names a generic
    /// parameter, by const index: the initializer expression and
    /// the impl (or trait) generics it is over. Their `consts`
    /// value is a zero placeholder; use sites evaluate the
    /// initializer per instance (`check::assoc_eval`).
    pub assoc_const_tmpls: FxMap<u32, (ast::ExprId, Generics)>,
    /// Trait defs that declare a method of this name.
    pub traits_by_method: FxMap<Sym, Vec<DefId>>,
    /// The `Drop::drop` instance to call for one concrete Adt,
    /// for cgen's drop glue (iface: W-CGEN reads this).
    pub drop_methods: crate::check::spec::Logged<AdtId, LocalDefId, { crate::check::spec::tab::DROP_METHODS }>,
    /// The written `Clone::clone`, `Default::default`,
    /// `PartialEq::eq`, and `PartialOrd::partial_cmp` methods of
    /// non-generic impls on non-generic local Adts, by (Adt, trait):
    /// derived glue calls them for a field of that type, as rustc's
    /// derived bodies call the field type's impl (iface: W-CGEN
    /// reads this, like `drop_methods`).
    pub glue_methods: crate::check::spec::Logged<(AdtId, DefId), LocalDefId, { crate::check::spec::tab::GLUE_METHODS }>,
    /// The written `Clone::clone_from` methods of impls on local
    /// Adts, by Adt: cgen's `clonefrom` glue calls them, as a derived
    /// or default `clone_from` calls each field's (iface: W-CGEN
    /// reads this, like `glue_methods`).
    pub clone_from_methods: crate::check::spec::Logged<AdtId, LocalDefId, { crate::check::spec::tab::CLONE_FROM_METHODS }>,
    /// The written `PartialOrd::partial_cmp` methods cgen's `PCmp`
    /// glue may call: like `glue_methods`, but an `Ord` impl may also
    /// exist (the `Cmp` glue then means `Ord::cmp` and cannot serve
    /// both), and only an `lt` override disqualifies (sort compares
    /// with `lt`, whose default is `partial_cmp == Some(Less)`).
    /// Keyed by (Adt, `PartialOrd` trait) (iface: W-CGEN reads this).
    pub pcmp_methods: crate::check::spec::Logged<(AdtId, DefId), LocalDefId, { crate::check::spec::tab::PCMP_METHODS }>,
    /// The written `impl Default for &'static A` methods (a non-generic
    /// impl, `A` a non-generic local Adt): the derive glue's default of
    /// a `&'static A` field calls it (ts-rust's `&'static ExportMember`).
    /// Keyed by `A` (iface: W-CGEN reads this).
    pub ref_default_methods: crate::check::spec::Logged<AdtId, LocalDefId, { crate::check::spec::tab::REF_DEFAULT_METHODS }>,
    /// The user `fmt` method instance for one concrete Adt and fmt
    /// trait (`FmtKind as u8`: Display or Debug), for cgen's Debug and
    /// Display glue (W-STD-B; iface: W-CGEN reads this).
    pub fmt_methods: crate::check::spec::Logged<(AdtId, u8), LocalDefId, { crate::check::spec::tab::FMT_METHODS }>,
    /// Field types of `#[derive(Debug)]` Adts that name a local Adt the
    /// structural rules could not answer at collect (a written `impl
    /// Debug` is not in the index yet): proven in `finish_collect`.
    pub deferred_debug_fields: Vec<(Ty, Span)>,
    /// The user `Hasher` method instances of one concrete Adt, by index
    /// into `check::hashmap::HASHER_METHODS` (methods the impl leaves out
    /// take core's defaults in cgen), and the `BuildHasher::build_hasher`
    /// instance with the impl's `Hasher` type (W-STD-B; iface: W-CGEN
    /// reads these for the hash glue).
    pub hasher_methods: crate::check::spec::Logged<(AdtId, u8), LocalDefId, { crate::check::spec::tab::HASHER_METHODS }>,
    pub build_hashers: crate::check::spec::Logged<AdtId, (LocalDefId, Ty), { crate::check::spec::tab::BUILD_HASHERS }>,
    /// The `Iterator` method instances of one concrete Adt whose impl
    /// is generic (`next`, `size_hint`, `next_back`, and the `Item`
    /// type): the `ByNext` expansion calls them, as it calls the
    /// plain fns of a non-generic impl (check/iter.rs `by_next_fns`;
    /// iface: lower/iter.rs reads this through it).
    pub iter_methods: crate::check::spec::Logged<AdtId, (LocalDefId, Option<LocalDefId>, Option<LocalDefId>, Option<Ty>, bool), { crate::check::spec::tab::ITER_METHODS }>,
    /// The written `Hash::hash` template of a non-generic impl on a
    /// non-generic local Adt (no `hash_slice` of its own), and its
    /// instances by hasher type: the hash glue calls one for a value of
    /// that Adt, as core's and derived impls call the field's impl
    /// (W-STD-B; iface: W-CGEN reads `hash_impls`).
    pub written_hash: crate::check::spec::Logged<AdtId, LocalDefId, { crate::check::spec::tab::WRITTEN_HASH }>,
    pub hash_impls: crate::check::spec::Logged<AdtId, Vec<(Ty, LocalDefId)>, { crate::check::spec::tab::HASH_IMPLS }>,
    /// Map lookups by a dyn key (`impl Borrow<dyn K + 'a> for Key`, with
    /// written `Hash` and `PartialEq` impls for `dyn K + '_`; ts-rust's
    /// module caches): per key Adt, the hash glue's calls (cgen/hash.rs).
    pub dyn_keys: crate::check::spec::Logged<AdtId, DynKey, { crate::check::spec::tab::DYN_KEYS }>,
    /// The written generic `Hash` impls of concrete Adt instances
    /// (`impl<T: Hash> Hash for VecDeque<T>`): the impl's `hash` fn
    /// and the impl args at the instance. `ensure_written_hash` makes
    /// their `hash::<H>` instances into `hash_impls`, as for
    /// `written_hash`.
    pub generic_hash: crate::check::spec::Logged<AdtId, (LocalDefId, Vec<GenericArg>), { crate::check::spec::tab::GENERIC_HASH }>,
    /// The written `Borrow::borrow` of a non-generic `impl Borrow<Q>`
    /// on a non-generic local Adt, by (Adt, Q): a map or set lookup by
    /// `&Q` calls it on each candidate key (W-STD-B; iface: W-CGEN
    /// reads this).
    pub borrow_impls: crate::check::spec::Logged<(AdtId, Ty), LocalDefId, { crate::check::spec::tab::BORROW_IMPLS }>,
    /// True when the program uses any generic or trait form. The
    /// driver then assigns instance slots and forces a full work
    /// set (iface: W-DRIVER reads this).
    pub has_generics: bool,
    /// True when user code (not only spliced std source) sets
    /// `has_generics`. Without it, the generics are std's methods of
    /// the lang enums only, and mono skips work no instance needs
    /// (see `materialize`).
    pub user_generics: bool,
    /// Fns that hand out a `Cow` the caller need not name (`uses_cow` in
    /// collect): a kept program without user generics stands only while
    /// no edited body calls one.
    pub cow_fns: Vec<crate::intern::Sym>,
    /// (templates checked, concrete instances made).
    pub mono_counts: (usize, usize),
    /// The template checks, by checked fn: each template body is
    /// checked as itself (`template_check`), and its trait picks
    /// are recorded there.
    pub template_checks: crate::check::spec::Logged<LocalDefId, LocalDefId, { crate::check::spec::tab::TEMPLATE_CHECKS }>,
    /// Trait picks of template bodies by call expression (ARCH 4.1
    /// `CallTrait`, see `check/picks.rs`): every check of a body other
    /// than its template check reuses them instead of probing again.
    pub trait_picks: crate::check::spec::Logged<crate::ast::ExprId, crate::check::picks::TraitPick, { crate::check::spec::tab::TRAIT_PICKS }>,
    /// The signature stub of each trait method (`add_trait_method_stubs`),
    /// by method def: the callee of calls a template's env proves.
    pub trait_method_stubs: FxMap<DefId, LocalDefId>,
    /// False for `lust check`: materialize makes no instances of
    /// generic fns (closure body fns are made either way; see
    /// `materialize`).
    pub walk_instances: bool,
    /// The driver session's generic reuse cache, lent to this collect
    /// (`collect::collect_reuse`): template checks and discovery skip
    /// bodies whose stored results still hold (W-PERF).
    pub reuse: crate::driver::gen_reuse::GenReuse,
    /// Dyn compatibility and vtable layout per user trait
    /// (`check::object`), computed when trait tables are done.
    pub dyn_infos: FxMap<DefId, crate::check::object::DynInfo>,
    /// The vtables mono made, one per (concrete type, principal
    /// trait ref), both in the global store (iface: W-CGEN reads
    /// these to emit vtable statics).
    pub vtables: Vec<crate::check::object::VtableData>,
    pub vtable_by_key: crate::check::spec::Logged<(Ty, TraitRef), u32, { crate::check::spec::tab::VTABLE_BY_KEY }>,
    /// Methods of `impl dyn Trait` blocks, by (the dyn type with an
    /// erased region, name).
    pub dyn_inherent: FxMap<(Ty, Sym), LocalDefId>,
    /// The self type and span of each `impl dyn Trait` block and each
    /// const or static item type that holds a dyn type, for the dyn
    /// type checks.
    pub dyn_impl_sites: Vec<(Ty, Span)>,
    /// Impls whose header names a dyn type with a `'static` object
    /// lifetime (`impl dyn Tr`, `impl X for dyn Tr`), and their methods.
    /// Using one needs the dyn value to be `'static` (`check::object`).
    pub static_dyn_impls: Vec<DefId>,
    pub static_dyn_fns: Vec<LocalDefId>,
    /// The traits the eager vtable pass took from the `dyn` types of the
    /// source (`mono::vtable::dyn_named_traits`, sorted): the header delta
    /// takes a header with a `dyn` type only while the new Ast names the
    /// same set (driver/kept_delta.rs).
    pub eager_dyn_traits: Vec<DefId>,
    /// True once mono's materialize pass is done: every vtable a
    /// concrete body needs exists from then on.
    pub mono_done: bool,
    /// The session's Adt instance ids, lent to this collect like `reuse`
    /// (`collect::InstOrder`).
    pub inst_order: crate::check::collect::InstOrder,
    /// The Adt template rows (set at the first instance; every row past
    /// them is an instance or a placeholder).
    pub template_rows: Option<u32>,
    /// Adt instances in creation order (ids are not: see `InstOrder`).
    pub adt_created: Vec<AdtId>,
    /// Each plain body's turn in materialize's first discovery round, in
    /// fn order: (fn, the `adt_created` length as its turn began). The
    /// daemon's kept program asks what existed before a body's turn
    /// (`made_before_turn`).
    pub turn_marks: Vec<(LocalDefId, u32)>,
    /// What collect's derive checks saw (a derive delta checks the same,
    /// check/derive_delta.rs): the `adt_created` length at the derive
    /// field checks and at `check_derive_bounds`, and the `fns` length at
    /// `check_written_wf`. Instances made after those exist in a kept
    /// program but not at that point of a collect.
    pub derive_marks: [usize; 3],
    /// The written types of each fn signature and Adt field list that held
    /// a projection before `normalize_signatures`, by fn or Adt def, and of
    /// each impl Self type (by impl def) and const or static type (under
    /// `item_types_key`) that held one before collect normalized it. Well-
    /// formedness ran on these; a derive delta refuses when one names its
    /// reach (it neither normalizes nor checks them again).
    pub written_projections: crate::check::spec::Logged<DefId, Vec<Ty>, { crate::check::spec::tab::WRITTEN_PROJECTIONS }>,
    /// The `Ast::items` index of each struct, enum, type alias, and trait
    /// by flat name (the first one when a name repeats). Param defaults
    /// and generic aliases read their written generics through it.
    pub item_index: FxMap<Sym, u32>,
    /// The resolved param defaults of each struct, enum, trait, and
    /// generic alias that has one (`check::defaults::resolve_all`), by
    /// def: the finish-side WF check proves them, and the driver folds
    /// them into the def's `Sig` fingerprint.
    pub param_defaults: FxMap<DefId, Vec<Option<GenericArg>>>,
    /// Return-position `impl Trait` types by opaque def (ARCH 2.11).
    pub opaques: FxMap<DefId, OpaqueInfo>,
    /// The return type callers check against, for a plain fn whose
    /// `FnInfo::ret` was revealed to its hidden type for codegen
    /// (`check::opaque::reveal_plain`): the opaque type itself.
    pub opaque_ret_of: crate::check::spec::Logged<LocalDefId, Ty, { crate::check::spec::tab::OPAQUE_RET_OF }>,
    /// The hidden type of each `impl Trait` return, over its defining
    /// fn's params (check/opaque.rs): from `reveal_plain` and the
    /// template check. A revealed check substitutes a use's args.
    pub opaque_hidden: crate::check::spec::Logged<DefId, Ty, { crate::check::spec::tab::OPAQUE_HIDDEN }>,
    /// The anonymous consts of signatures (`note_anon_const`).
    pub(crate) anon_wants: AnonWants,
}

impl Default for GenTables {
    fn default() -> Self {
        GenTables {
            lang: LangTraits::new(),
            index: ImplIndex::new(),
            trait_names: crate::driver::read_cover::NameMap::new("trait"),
            trait_scopes: FxMap::default(),
            trait_methods: FxMap::default(),
            lang_method_sigs: FxMap::default(),
            trait_assoc_defaults: FxMap::default(),
            trait_unsafe: FxMap::default(),
            trait_assoc_consts: FxMap::default(),
            wf_headers: Vec::new(),
            adt_info: Vec::new(),
            adt_lifetimes: FxMap::default(),
            generic_aliases: crate::driver::read_cover::NameMap::new("generic alias"),
            adt_generics: Vec::new(),
            adt_envs: Vec::new(),
            adt_scopes: Vec::new(),
            adt_instance_of: Vec::new(),
            fn_templates: Vec::new(),
            fn_scopes: Vec::new(),
            fn_class: Vec::new(),
            instances: Default::default(),
            closures: Default::default(),
            closure_fns: Default::default(),
            template_closures: Default::default(),
            template_calls: Default::default(),
            instance_by_key: Default::default(),
            inherent_methods: FxMap::default(),
            inherent_tmpls: std::sync::OnceLock::new(),
            prim_inherent_methods: FxMap::default(),
            inherent_self_pats: FxMap::default(),
            inherent_impl_self: FxMap::default(),
            inherent_const_self: FxMap::default(),
            assoc_const_tmpls: FxMap::default(),
            traits_by_method: FxMap::default(),
            drop_methods: Default::default(),
            glue_methods: Default::default(),
            clone_from_methods: Default::default(),
            pcmp_methods: Default::default(),
            ref_default_methods: Default::default(),
            fmt_methods: Default::default(),
            deferred_debug_fields: Vec::new(),
            hasher_methods: Default::default(),
            build_hashers: Default::default(),
            iter_methods: Default::default(),
            written_hash: Default::default(),
            hash_impls: Default::default(),
            dyn_keys: Default::default(),
            generic_hash: Default::default(),
            borrow_impls: Default::default(),
            has_generics: false,
            user_generics: false,
            cow_fns: Vec::new(),
            mono_counts: (0, 0),
            template_checks: Default::default(),
            trait_picks: Default::default(),
            trait_method_stubs: FxMap::default(),
            walk_instances: true,
            reuse: Default::default(),
            dyn_infos: FxMap::default(),
            vtables: Vec::new(),
            vtable_by_key: Default::default(),
            dyn_inherent: FxMap::default(),
            dyn_impl_sites: Vec::new(),
            static_dyn_impls: Vec::new(),
            static_dyn_fns: Vec::new(),
            eager_dyn_traits: Vec::new(),
            mono_done: false,
            inst_order: Default::default(),
            template_rows: None,
            adt_created: Vec::new(),
            turn_marks: Vec::new(),
            derive_marks: [0; 3],
            written_projections: Default::default(),
            item_index: FxMap::default(),
            param_defaults: FxMap::default(),
            opaques: FxMap::default(),
            opaque_ret_of: Default::default(),
            opaque_hidden: Default::default(),
            anon_wants: Default::default(),
        }
    }
}

impl GenTables {
    /// The resolve context over the tables built so far.
    /// `resolve_cx` for an item of spliced std source when `std` is set:
    /// no user type, alias, or trait is visible (see `STD_MODULE`).
    pub fn resolve_cx_in<'x>(&'x self, type_names: &'x crate::driver::read_cover::NameMap<AdtId>, aliases: &'x crate::driver::read_cover::NameMap<Ty>, std: bool) -> ResolveCx<'x> {
        static NO_ADTS: crate::driver::read_cover::NameMap<AdtId> = crate::driver::read_cover::NameMap::new("type");
        static NO_TYS: crate::driver::read_cover::NameMap<Ty> = crate::driver::read_cover::NameMap::new("alias");
        static NO_DEFS: crate::driver::read_cover::NameMap<DefId> = crate::driver::read_cover::NameMap::new("trait");
        static NO_ALIASES: crate::driver::read_cover::NameMap<GenericAlias> = crate::driver::read_cover::NameMap::new("generic alias");
        static NO_ITEMS: std::sync::LazyLock<FxMap<Sym, u32>> = std::sync::LazyLock::new(FxMap::default);
        if !std {
            return self.resolve_cx(type_names, aliases);
        }
        ResolveCx {
            type_names: &NO_ADTS,
            adt_info: &self.adt_info,
            adt_lifetimes: &self.adt_lifetimes,
            trait_names: &NO_DEFS,
            aliases: &NO_TYS,
            generic_aliases: &NO_ALIASES,
            index: &self.index,
            lang: &self.lang,
            item_index: &NO_ITEMS,
            anon_wants: None,
        }
    }

    pub fn resolve_cx<'x>(&'x self, type_names: &'x crate::driver::read_cover::NameMap<AdtId>, aliases: &'x crate::driver::read_cover::NameMap<Ty>) -> ResolveCx<'x> {
        ResolveCx {
            type_names,
            adt_info: &self.adt_info,
            adt_lifetimes: &self.adt_lifetimes,
            trait_names: &self.trait_names,
            aliases,
            generic_aliases: &self.generic_aliases,
            index: &self.index,
            lang: &self.lang,
            item_index: &self.item_index,
            anon_wants: Some(&self.anon_wants),
        }
    }
}

/// True when `Param(idx)` occurs anywhere in a type.
pub fn ty_uses_param(tys: &impl TyIntern, t: Ty, idx: u32) -> bool {
    if !tys.flags(t).contains_param() {
        return false;
    }
    match tys.kind(t) {
        TyKind::Param(p) => p.0 == idx,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => ty_uses_param(tys, e, idx),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| ty_uses_param(tys, e, idx)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| ty_uses_param(tys, e, idx)))
        }
        _ => false,
    }
}

/// Inserts the lang trait records into the program's index and
/// def table. Runs first in generic collection.
pub fn init_lang(p: &mut Program) {
    let records = lang_trait_records(&p.gx.lang, &p.interner, &mut p.tys);
    p.gx.lang_method_sigs = lang_method_sigs(&p.gx.lang, &p.interner, &mut p.tys, &records);
    for rec in records {
        let mut data =
            crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Trait, None, rec.name, crate::ty::defs::Vis::Pub, Span::default());
        data.generics = rec.generics.clone();
        p.defs.insert(rec.def, data);
        for (_, mname) in &rec.methods {
            p.gx.traits_by_method.entry(*mname).or_default().push(rec.def);
        }
        p.gx.index.insert_trait(rec);
    }
    let lang = p.gx.lang;
    p.gx.index.structural = vec![lang.sized, lang.send, lang.sync, lang.unpin];
    p.gx.index.derive_family =
        vec![lang.copy, lang.clone, lang.debug, lang.partial_eq, lang.eq, lang.partial_ord, lang.ord, lang.hash, lang.default];
    p.gx.index.sized_only = vec![lang.sized, lang.clone, lang.copy, lang.default];
}

/// How many type/const parameters an AST generics list declares
/// (lifetime parameters are rejected when generics are built, and
/// are not counted).
pub fn ast_param_count(g: &ast::Generics) -> usize {
    g.params.iter().filter(|p| matches!(p, ast::GenericParam::Type { .. } | ast::GenericParam::Const { .. })).count()
}

/// The def of one user trait: hashed from its name and its
/// ordinal among same-named traits (duplicates are errors, the
/// ordinal only keeps their records apart).
fn trait_def_id(p: &Program, interner: &Interner, name: Sym, ordinal: u32) -> DefId {
    DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Trait, interner.get(name), ordinal) }
}

/// The def of one associated item or method of a trait or impl,
/// hashed under its parent's path hash.
pub fn child_def_id(krate: crate::def::CrateId, parent: DefId, interner: &Interner, name: Sym, kind: crate::def::DefKind) -> DefId {
    DefId { krate, hash: crate::def::child_hash(parent.hash, kind, interner.get(name), 0) }
}

/// Pass 0 of generic collection: every user trait gets its def
/// and a placeholder index record with its associated item and
/// method defs, so bounds elsewhere can name the trait and its
/// assoc items before signatures resolve. `build_trait_tables`
/// fills the records in.
pub fn collect_trait_defs(p: &mut Program, errs: &mut Vec<Diag>) {
    let mut ordinals: FxMap<Sym, u32> = FxMap::default();
    for item in &p.ast.items {
        let ast::ItemKind::Trait(tdef) = &item.kind else { continue };
        p.gx.has_generics = true;
        p.gx.user_generics = true;
        let ordinal = ordinals.get(&tdef.name).copied().unwrap_or(0);
        ordinals.insert(tdef.name, ordinal + 1);
        let def = trait_def_id(p, &p.interner, tdef.name, ordinal);
        // The first trait of a name owns it. A duplicate gets no record and
        // no name entry, so later passes never look its items up in the
        // first trait's record (that lookup used to panic).
        if p.gx.trait_names.contains_key(&tdef.name) {
            errs.push(Diag::new(
                "L0106",
                tdef.name_span,
                format!("`{}` is defined more than once", p.display_name(tdef.name)),
                "Rename one of the definitions.",
            ));
            continue;
        }
        p.gx.trait_names.insert(tdef.name, def);
        // Its lifetime params by name (W-BORROW, keyed by the trait's def
        // in the Adts' table): trait refs check their arity against them.
        let lts: Vec<Sym> = tdef
            .generics
            .params
            .iter()
            .filter_map(|g| if let ast::GenericParam::Lifetime { lt, .. } = g { Some(lt.name) } else { None })
            .collect();
        if !lts.is_empty() {
            p.gx.adt_lifetimes.insert(def, lts);
            // A projection through such a trait would carry the trait's
            // regions in a type that has no slots for them: a stated cut.
            if let Some(at) = tdef.types.first() {
                errs.push(Diag::new(
                    "L0203",
                    at.name_span,
                    "associated types in a trait with lifetime parameters are not supported yet",
                    "Move the lifetime to the methods, or make the type a generic parameter of the trait.",
                ));
            }
        }
        // Associated items: types live in the type namespace, consts and
        // methods in the value namespace. A second item of one name in one
        // namespace is a duplicate (rustc E0428) and joins no record.
        let mut assoc_items: Vec<(DefId, Sym, bool)> = Vec::new();
        for at in &tdef.types {
            if assoc_items.iter().any(|&(_, n, is_ty)| is_ty && n == at.name) {
                errs.push(Diag::new(
                    "L0106",
                    at.name_span,
                    format!("`{}` is defined more than once", p.display_name(at.name)),
                    "Rename one of the definitions.",
                ));
                continue;
            }
            assoc_items.push((child_def_id(p.krate, def, &p.interner, at.name, crate::def::DefKind::Assoc), at.name, true));
        }
        for ac in &tdef.consts {
            if assoc_items.iter().any(|&(_, n, is_ty)| !is_ty && n == ac.name) || tdef.fns.iter().any(|f| f.name == ac.name) {
                errs.push(Diag::new(
                    "L0106",
                    ac.name_span,
                    format!("`{}` is defined more than once", p.display_name(ac.name)),
                    "Rename one of the definitions.",
                ));
                continue;
            }
            assoc_items.push((child_def_id(p.krate, def, &p.interner, ac.name, crate::def::DefKind::Assoc), ac.name, false));
        }
        let mut methods: Vec<(DefId, Sym)> = Vec::new();
        for f in &tdef.fns {
            if methods.iter().any(|&(_, n)| n == f.name) {
                errs.push(Diag::new(
                    "L0106",
                    f.name_span,
                    format!("`{}` is defined more than once", p.display_name(f.name)),
                    "Rename one of the definitions.",
                ));
                continue;
            }
            methods.push((child_def_id(p.krate, def, &p.interner, f.name, crate::def::DefKind::Method), f.name));
        }
        // Placeholder generics with the right parameter count, so
        // bounds that name this trait resolve before its own
        // generics are built.
        let mut placeholder = Generics::default();
        for _ in 0..=ast_param_count(&tdef.generics) {
            placeholder.params.push(ParamDef { name: tdef.name, kind: ParamKind::Type, span: tdef.name_span });
        }
        for &(_, mname) in &methods {
            p.gx.traits_by_method.entry(mname).or_default().push(def);
        }
        p.gx.index.insert_trait(TraitRecord {
            def,
            name: tdef.name,
            generics: placeholder,
            assoc_items,
            methods,
            local: true,
            span: tdef.span,
        });
        p.defs.insert(
            def,
            crate::ty::defs::DefData::skeleton(
                crate::ty::defs::DefKind::Trait,
                None,
                tdef.name,
                crate::ty::defs::Vis::Priv,
                tdef.name_span,
            ),
        );
    }
}

/// rustc's receiver rule without `arbitrary_self_types` (E0307,
/// E0658): a typed `self` is `Self`, or `&`, `&mut`, `Box`, `Rc` or
/// `Arc` of a valid receiver (`self: &Arc<Self>`). In a trait, Self is
/// the trait's, so `self: Rc<S>` there is invalid.
fn valid_receiver(tys: &impl TyIntern, t: Ty, self_ty: Ty) -> bool {
    if t == self_ty {
        return true;
    }
    let first = |a: ArgsId| tys.args(a).iter().find_map(|g| g.as_ty());
    match tys.kind(t) {
        TyKind::Ref(_, _, e) => valid_receiver(tys, e, self_ty),
        TyKind::Adt(d, a) if d == tys.builtins().boxed || d == tys.builtins().rc => first(a).is_some_and(|e| valid_receiver(tys, e, self_ty)),
        TyKind::Adt(_, a) if crate::ty::sync::sync_kind(tys, t) == Some(crate::ty::sync::SyncTy::Arc) => {
            first(a).is_some_and(|e| valid_receiver(tys, e, self_ty))
        }
        _ => false,
    }
}

/// Resolves one fn signature in template form: self parameter,
/// params, and return, under the combined scope. Handles
/// `impl Trait` argument sugar by growing the generics. Returns
/// (params with self first, ret, ret_borrows_from, generics, scope,
/// region signature for the borrow checker).
#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
pub fn resolve_fn_sig(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    def: &ast::FnDef,
    mut generics: Generics,
    scope: &Scope,
    self_ty: Option<Ty>,
    owner: Option<DefId>,
    errs: &mut Vec<Diag>,
) -> (Vec<Ty>, Ty, Option<usize>, Generics, Scope, Option<crate::borrowck::RegionSig>, Option<(DefId, OpaqueInfo)>) {
    let mut scope = scope.clone();
    // W-BORROW3: a fn pointer type in the signature may name the item's
    // lifetimes (`FnSig::free_slots`).
    scope.fn_ptr_free = true;
    if scope.self_ty.is_none() {
        scope.self_ty = self_ty;
    }
    let mut params: Vec<Ty> = Vec::new();
    if let (Some(sp), Some(st)) = (&def.self_param, self_ty) {
        if let Some(lt) = sp.lifetime
            && let Err(d) = check_lifetime(interner, &scope, lt)
        {
            errs.push(d);
        }
        params.push(match sp.kind {
            ast::SelfKind::Value => st,
            ast::SelfKind::Ref => tys.mk_ref(false, st),
            ast::SelfKind::RefMut => tys.mk_ref(true, st),
            ast::SelfKind::Typed => match sp.ty {
                Some(t) => match resolve_scoped(ast, interner, known, cx, tys, t, &scope) {
                    Ok(rt) if !valid_receiver(tys, rt, st) => {
                        errs.push(Diag::new(
                            "L0110",
                            ast.ty_span(t),
                            "invalid `self` parameter type: it must be `Self`, or a reference, `Box`, `Rc` or `Arc` of a valid receiver",
                            "Write `self: Self`, `&Self`, `Box<Self>`, `Rc<Self>` or `Arc<Self>`.",
                        ));
                        ERROR
                    }
                    Ok(rt) => rt,
                    Err(d) => {
                        errs.push(d);
                        ERROR
                    }
                },
                None => st,
            },
        });
    }
    // `impl Trait` in argument position is a fresh type parameter with
    // those bounds (section 2.11), also nested in an argument's type.
    for param in &def.params {
        if let Some(span) = super::use_caps::in_arg_type(ast, param.ty) {
            errs.push(Diag::new(
                "L0110",
                span,
                "`use<...>` precise capturing syntax not allowed in argument-position `impl Trait`",
                "Remove the `use<..>` list: an `impl Trait` argument captures nothing itself.",
            ));
        }
        if let TyExpr::ImplTrait { bounds, .. } = ast.ty(param.ty) {
            let lhs = apit_param(ast, interner, known, cx, tys, &mut generics, &mut scope, bounds, param.span, errs);
            params.push(lhs);
            continue;
        }
        let mut nested: Vec<ast::TyId> = Vec::new();
        nested_impl_traits(ast, param.ty, &mut nested);
        for n in nested {
            let TyExpr::ImplTrait { bounds, .. } = ast.ty(n) else { continue };
            let lhs = apit_param(ast, interner, known, cx, tys, &mut generics, &mut scope, bounds, ast.ty_span(n), errs);
            scope.apit.push((n, lhs));
        }
        match resolve_scoped(ast, interner, known, cx, tys, param.ty, &scope) {
            // No Sized check here: a declaration with no body may
            // name unsized params (rustc allows it). The value
            // positions of a fn with a body are `check_written_wf`'s.
            Ok(t) => params.push(t),
            Err(d) => {
                errs.push(d);
                params.push(ERROR);
            }
        }
    }
    // A return-position `impl Trait` (ARCH 2.11) is an opaque type over
    // every param in scope (edition 2024 captures them all). Inside a
    // trait (no owner here) it is not supported yet.
    let mut opaque: Option<(DefId, OpaqueInfo)> = None;
    let ret = match (def.ret, owner) {
        (None, _) => UNIT,
        (Some(t), owner) if matches!(ast.ty(t), TyExpr::ImplTrait { .. }) => {
            let TyExpr::ImplTrait { bounds, .. } = ast.ty(t) else { unreachable!() };
            match owner {
                None => {
                    errs.push(not_yet("L0602", ast.ty_span(t), "`impl Trait` in a trait method's return type"));
                    ERROR
                }
                Some(owner) => {
                    let od = opaque_def(owner);
                    let args: Vec<GenericArg> = generics
                        .params
                        .iter()
                        .enumerate()
                        .map(|(i, prm)| match prm.kind {
                            ParamKind::Const(_) => GenericArg::Const(tys.intern_const(ConstKind::Param(i as u32))),
                            _ => GenericArg::Ty(tys.intern(TyKind::Param(ParamId(i as u32)))),
                        })
                        .collect();
                    let args = tys.intern_args(&args);
                    let oty = tys.intern(TyKind::Opaque(od, args));
                    // The bounds' Self is one more param after the fn's
                    // own, so a use substitutes `args ++ [self]`.
                    let self_param = tys.intern(TyKind::Param(ParamId(generics.params.len() as u32)));
                    let mut preds: Vec<Predicate> = Vec::new();
                    let mut relaxed: Vec<u32> = Vec::new();
                    for b in bounds {
                        // `-> impl Tr + '_` captures the elided input lifetime;
                        // only a param or where bound of `'_` is E0637.
                        if matches!(b, TraitBound::Lifetime(lt) if interner.get(lt.name) == "_") {
                            continue;
                        }
                        bound_predicates(ast, interner, known, cx, tys, &scope, self_param, b, &mut preds, &mut relaxed, errs);
                    }
                    let span = ast.ty_span(t);
                    if !relaxed.is_empty() {
                        errs.push(not_yet("L0602", span, "`?Sized` on an `impl Trait` return type"));
                    }
                    if !preds.iter().any(|pr| matches!(pr, Predicate::Trait(_))) {
                        errs.push(Diag::new(
                            "L0110",
                            span,
                            "at least one trait must be specified in an `impl Trait` type",
                            "Write the trait the returned value implements, such as `impl Iterator<Item = u8>`.",
                        ));
                    }
                    if let TyExpr::ImplTrait { captures: Some(c), .. } = ast.ty(t) {
                        super::use_caps::check_list(interner, &generics, c, errs);
                    }
                    let fn_outs = fn_bounds_in(ast, interner, known, tys, cx, &scope, &[(crate::borrowck::RPIT_PARAM, bounds.as_slice())]);
                    let (item_out, outlives) = rpit_region_bounds(ast, interner, known, cx, tys, &scope, bounds);
                    opaque = Some((od, OpaqueInfo { owner, bounds: preds, fn_outs, item_out, outlives }));
                    oty
                }
            }
        }
        (Some(t), _) => resolve_scoped(ast, interner, known, cx, tys, t, &scope).unwrap_or_else(|d| {
            errs.push(d);
            ERROR
        }),
    };
    // The return type gets no Sized check here either, for the
    // same reason as the params above.
    // The parameter a returned reference borrows from under elision
    // (compat field; the borrow checker reads the region signature).
    // A written `dyn` object lifetime (`+ '_`, `+ 'static`) is one
    // more input lifetime, so that parameter is no single source.
    let mut ret_borrows_from = None;
    if crate::check::collect::contains_ref(tys, ret) {
        let ref_params: Vec<usize> = (0..params.len()).filter(|&i| crate::check::collect::contains_ref(tys, params[i])).collect();
        let dyn_lt = def.params.iter().any(|prm| has_written_dyn_lifetime(ast, prm.ty));
        if def.self_param.as_ref().is_some_and(|s| s.kind != ast::SelfKind::Value) {
            ret_borrows_from = Some(0);
        } else if ref_params.len() == 1 && !dyn_lt {
            ret_borrows_from = Some(ref_params[0]);
        }
    }
    let region_sig = region_sig(ast, interner, known, tys, cx, def, &scope, self_ty, &params, errs);
    (params, ret, ret_borrows_from, generics, scope, region_sig, opaque)
}

/// One `impl Trait` argument's synthetic type param (`impl#N`, after the
/// declared ones): its bounds and an implicit `Sized` unless relaxed.
#[allow(clippy::too_many_arguments)]
fn apit_param(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    generics: &mut Generics,
    scope: &mut Scope,
    bounds: &[ast::TraitBound],
    span: Span,
    errs: &mut Vec<Diag>,
) -> Ty {
    // An elided lifetime in the bound's generic args (`impl
    // IntoIterator<Item = &u8>`) is unstable in rustc (E0658).
    if let Some(at) = bounds.iter().find_map(|b| match b {
        ast::TraitBound::Trait { trait_ref, .. } => trait_ref.path.iter().find_map(|seg| match &seg.args {
            ast::GenericArgs::Angle(args) => args.iter().find_map(|a| match a {
                ast::GenericArg::Type(t) | ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => elided_ref(ast, interner, *t),
                _ => None,
            }),
            _ => None,
        }),
        _ => None,
    }) {
        errs.push(Diag::new(
            "L0203",
            at,
            "an elided lifetime in an argument-position `impl Trait` is not stable Rust",
            "Name the lifetime: `fn f<'a>(x: impl Iterator<Item = &'a T>)`.",
        ));
    }
    let idx = generics.params.len() as u32;
    let name = interner.intern(&format!("impl#{idx}"));
    generics.params.push(ParamDef { name, kind: ParamKind::Type, span });
    scope.type_params.push((name, idx));
    let lhs = tys.intern(TyKind::Param(ParamId(idx)));
    // `impl Trait` in an associated type binding of the bounds
    // (`impl IntoIterator<Item = impl Into<String>>`) is a param of its
    // own, as in rustc. Elsewhere in the bound's generic args it stays
    // L0602 (rustc E0666).
    for b in bounds {
        let ast::TraitBound::Trait { trait_ref, .. } = b else { continue };
        for seg in &trait_ref.path {
            let ast::GenericArgs::Angle(args) = &seg.args else { continue };
            for a in args {
                let ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } = a else { continue };
                let mut nested: Vec<ast::TyId> = Vec::new();
                nested_impl_traits(ast, *t, &mut nested);
                for n in nested {
                    let TyExpr::ImplTrait { bounds: inner, .. } = ast.ty(n) else { continue };
                    let p = apit_param(ast, interner, known, cx, tys, generics, scope, inner, ast.ty_span(n), errs);
                    scope.apit.push((n, p));
                }
            }
        }
    }
    let mut preds: Vec<Predicate> = Vec::new();
    let mut relaxed: Vec<u32> = Vec::new();
    for b in bounds {
        bound_predicates(ast, interner, known, cx, tys, scope, lhs, b, &mut preds, &mut relaxed, errs);
    }
    if !relaxed.contains(&idx) {
        let args = tys.intern_args(&[GenericArg::Ty(lhs)]);
        preds.push(Predicate::Trait(Binder::plain(TraitRef { def: cx.lang.sized, args, bindings: EMPTY_BINDINGS })));
    }
    generics.predicates.extend(preds);
    lhs
}

/// The span of an elided reference lifetime (`&T`, `&'_ T`) in a type
/// written inside an `impl Trait` bound's generic args, not under `Fn`
/// sugar, fn pointers, `dyn`, or a nested `impl Trait` (each has its own
/// elision rules or its own check).
/// An elided reference lifetime (`&T`, `'_`) in a bound's generic args
/// (`C: Extend<&u8>`), not under `Fn(..)` sugar: rustc E0637 there.
fn bound_elided_ref(ast: &Ast, interner: &Interner, b: &TraitBound) -> Option<Span> {
    let TraitBound::Trait { trait_ref, .. } = b else { return None };
    trait_ref.path.iter().find_map(|seg| match &seg.args {
        ast::GenericArgs::Angle(args) => args.iter().find_map(|a| match a {
            ast::GenericArg::Type(t) | ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => elided_ref(ast, interner, *t),
            ast::GenericArg::Lifetime(l) if matches!(interner.get(l.name), "'_" | "_") => Some(l.span),
            _ => None,
        }),
        _ => None,
    })
}

/// rustc E0637 for an elided lifetime in a bound or where-clause type.
fn e0637(span: Span) -> Diag {
    Diag::new("L0203", span, "`&` without an explicit lifetime name cannot be used here", "Name the lifetime, or write `for<'a>` on the bound.")
}

fn elided_ref(ast: &Ast, interner: &Interner, id: ast::TyId) -> Option<Span> {
    match ast.ty(id) {
        TyExpr::Ref { lifetime, inner, .. } => match lifetime {
            None => Some(ast.ty_span(id)),
            Some(l) if matches!(interner.get(l.name), "'_" | "_") => Some(l.span),
            Some(_) => elided_ref(ast, interner, *inner),
        },
        TyExpr::Paren(inner) | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } | TyExpr::Array { inner, .. } => elided_ref(ast, interner, *inner),
        TyExpr::Tuple(elems) => elems.iter().find_map(|&e| elided_ref(ast, interner, e)),
        TyExpr::Path(segs) => segs.iter().find_map(|seg| match &seg.args {
            ast::GenericArgs::Angle(args) => args.iter().find_map(|a| match a {
                ast::GenericArg::Type(t) | ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => elided_ref(ast, interner, *t),
                ast::GenericArg::Lifetime(l) if matches!(interner.get(l.name), "'_" | "_") => Some(l.span),
                _ => None,
            }),
            _ => None,
        }),
        _ => None,
    }
}

/// The `impl Trait` nodes nested in an argument type, outermost first:
/// under references, slices, arrays, tuples, and generic args. Not under
/// fn pointers or `dyn`, where rustc rejects them (E0562), and not inside
/// another `impl Trait`'s bounds.
pub(crate) fn nested_impl_traits(ast: &Ast, id: ast::TyId, out: &mut Vec<ast::TyId>) {
    match ast.ty(id) {
        TyExpr::ImplTrait { .. } => out.push(id),
        TyExpr::Ref { inner, .. } | TyExpr::Paren(inner) | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } => {
            nested_impl_traits(ast, *inner, out)
        }
        TyExpr::Array { inner, .. } => nested_impl_traits(ast, *inner, out),
        TyExpr::Tuple(elems) => elems.iter().for_each(|&e| nested_impl_traits(ast, e, out)),
        TyExpr::Path(segs) => {
            for seg in segs {
                if let ast::GenericArgs::Angle(args) = &seg.args {
                    for a in args {
                        if let ast::GenericArg::Type(t) = a {
                            nested_impl_traits(ast, *t, out);
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

/// The regions of the references in `t` whose referent holds the self
/// type `st` (rustc's `find_lifetime_for_self`, on resolved types).
fn self_ref_regions(tys: &impl TyIntern, t: Ty, st: Ty, out: &mut Vec<Region>) {
    fn holds(tys: &impl TyIntern, t: Ty, st: Ty) -> bool {
        if t == st {
            return true;
        }
        match tys.kind(t) {
            TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) | TyKind::Slice(inner) | TyKind::Array(inner, _) => holds(tys, inner, st),
            TyKind::Adt(_, args) => tys.args(args).iter().any(|g| g.as_ty().is_some_and(|x| holds(tys, x, st))),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&x| holds(tys, x, st)),
            _ => false,
        }
    }
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) => {
            if holds(tys, inner, st) {
                out.push(r);
            }
            self_ref_regions(tys, inner, st, out);
        }
        TyKind::Adt(_, args) => {
            for g in tys.args(args).to_vec() {
                if let Some(x) = g.as_ty() {
                    self_ref_regions(tys, x, st, out);
                }
            }
        }
        _ => {}
    }
}

/// The region signature of one fn (W-BORROW, ARCH 5.2): its params and
/// return resolved again with lifetimes kept. Each elided input lifetime
/// is its own universal region; elided output lifetimes take `&self`'s,
/// else the only input lifetime, else they are L0202 (rustc E0106). None
/// when a type does not resolve (the erased pass reported why).
#[allow(clippy::too_many_arguments)]
fn region_sig(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    def: &ast::FnDef,
    scope: &Scope,
    self_ty: Option<Ty>,
    params: &[Ty],
    errs: &mut Vec<Diag>,
) -> Option<crate::borrowck::RegionSig> {
    use std::sync::atomic::Ordering;
    // Named lifetimes (the impl's, then the fn's own) are universals
    // 0..n; each elided input lifetime takes the next index.
    let n_named = scope.lifetimes.len() as u32;
    let counter = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(n_named));
    let mut ks = scope.clone();
    ks.regions = RegionMode::Keep { next: Some(counter.clone()), elided: None };
    let mut rparams: Vec<Ty> = Vec::new();
    let mut names: Vec<String> = vec![String::new(); n_named as usize];
    for &(n, i) in &scope.lifetimes {
        if let Some(slot) = names.get_mut(i as usize) {
            *slot = format!("lifetime `'{}`", interner.get(n));
        }
    }
    let mut self_region: Option<Region> = None;
    let mut self_ambiguous = false;
    let mut skip = 0;
    let self_ty = scope.self_ty_regioned.or(self_ty);
    if let (Some(sp), Some(st)) = (&def.self_param, self_ty) {
        let t = match sp.kind {
            ast::SelfKind::Value => st,
            ast::SelfKind::Ref | ast::SelfKind::RefMut => {
                let r = scope_region(interner, &ks, sp.lifetime, sp.span).ok()?;
                self_region = Some(r);
                tys.intern(TyKind::Ref(r, Mut::from_bool(sp.kind == ast::SelfKind::RefMut), st))
            }
            ast::SelfKind::Typed => match sp.ty {
                Some(t) => {
                    let t = resolve_scoped(ast, interner, known, cx, tys, t, &ks).ok()?;
                    // rustc's `find_lifetime_for_self`: the one reference
                    // whose referent holds `Self` (`self: &Box<Self>`);
                    // several (`&Box<&Self>`) leave no elision at all.
                    let mut refs = Vec::new();
                    self_ref_regions(tys, t, st, &mut refs);
                    match refs.as_slice() {
                        [r] => self_region = Some(*r),
                        [] => {}
                        _ => self_ambiguous = true,
                    }
                    t
                }
                None => st,
            },
        };
        for _ in names.len()..counter.load(Ordering::Relaxed) as usize {
            names.push("the lifetime of `self`".into());
        }
        rparams.push(t);
        skip = 1;
    }
    for (i, param) in def.params.iter().enumerate() {
        let t = if let TyExpr::ImplTrait { .. } = ast.ty(param.ty) {
            *params.get(skip + i)?
        } else {
            resolve_scoped(ast, interner, known, cx, tys, param.ty, &ks).ok()?
        };
        for _ in names.len()..counter.load(Ordering::Relaxed) as usize {
            names.push(format!("the lifetime of parameter {}", i + 1));
        }
        rparams.push(t);
    }
    // As in rustc, `self` counts for elision only through a reference to
    // `Self` (above): the lifetimes of a by-value `self` (`Self` is
    // `W<'a>`, `Box<Self>`) are not input lifetimes.
    let mut inputs: Vec<Region> = Vec::new();
    for &t in &rparams[skip..] {
        crate::borrowck::elision_regions(tys, t, &mut inputs);
    }
    // A written dyn object lifetime is one more input lifetime (E0106).
    if def.params.iter().any(|prm| has_written_dyn_lifetime(ast, prm.ty)) {
        inputs.push(Region::Erased);
    }
    let elided = if self_ambiguous { None } else { self_region.or(if inputs.len() == 1 { Some(inputs[0]) } else { None }) };
    // The inputs' scope again, for the output: its own elision rule.
    let mut rs = ks;
    rs.regions = RegionMode::Keep { next: None, elided };
    if elided.is_none()
        && let Some(d) = def.ret.and_then(|t| opaque_elision(ast, interner, known, cx, tys, &rs, t))
    {
        errs.push(d);
        return None;
    }
    let opaque_caps = super::use_caps::captured_regions(interner, &rs, ast, def.ret, errs);
    let rret = match def.ret {
        None => UNIT,
        // An `impl Trait` with a `use<..>` list: its region signature
        // goes to `RegionTables::opaque_sigs`, whose rules never read
        // the return.
        Some(t) if opaque_caps.is_some() || matches!(ast.ty(t), TyExpr::ImplTrait { .. }) => UNIT,
        Some(t) => match resolve_scoped(ast, interner, known, cx, tys, t, &rs) {
            Ok(t) => t,
            Err(d) => {
                if d.code == "L0202" {
                    errs.push(d);
                }
                return None;
            }
        },
    };
    let n_univ = counter.load(Ordering::Relaxed);
    let facts: Vec<(Region, Region)> = scope
        .region_facts
        .iter()
        .map(|&(a, b)| (Region::Param(a), if b == STATIC_FACT { Region::Static } else { Region::Param(b) }))
        .collect();
    // A named lifetime is early-bound when a bound names it or no input
    // type does (rustc's split, ARCH 5.5): such a fn does not coerce to a
    // fn pointer that is generic over it.
    let mut in_inputs: Vec<Region> = Vec::new();
    for &t in &rparams {
        crate::borrowck::regions_of(tys, t, &mut in_inputs);
    }
    let early: Vec<bool> = (0..n_named)
        .map(|i| scope.region_facts.iter().any(|&(a, b)| a == i || b == i) || !in_inputs.contains(&Region::Param(i)))
        .collect();
    // `impl Trait` args (`f: impl Fn(&'a u8)`, `w: &mut impl Tr<'d>`)
    // bound their synthetic type params like declared ones.
    let mut bounded = param_bounds(ast, scope, &def.generics, &def.where_clause);
    let mut apit: Vec<(Ty, &[TraitBound])> = Vec::new();
    let top = def.params.iter().zip(params.get(skip..).unwrap_or_default()).map(|(p, &t)| (p.ty, t));
    for (n, t) in top.chain(scope.apit.iter().copied()) {
        if let TyExpr::ImplTrait { bounds, .. } = ast.ty(n)
            && let TyKind::Param(j) = tys.kind(t)
        {
            bounded.push((j.0, bounds));
            apit.push((t, bounds));
        }
    }
    let bounds = regioned_bound_preds(ast, interner, known, cx, tys, scope, &def.generics, &def.where_clause, &apit).1;
    let fn_bounds = fn_bounds_in(ast, interner, known, tys, cx, scope, &bounded);
    let trait_bounds = trait_lts_in(interner, known, cx, scope, &bounded);
    let item_bounds = item_bounds_in(ast, interner, known, tys, cx, scope, &bounded);
    let header = scope.header_regioned.clone();
    Some(crate::borrowck::RegionSig { n_univ, params: rparams, ret: rret, facts, names, early, fn_bounds, trait_bounds, item_bounds, opaque_caps, header, bounds })
}

/// The lifetime args of one written trait ref, for a trait with lifetime
/// params, resolved with regions kept in `scope` (`Region::Param` of its
/// lifetimes, or `'static`). None for a trait without lifetimes or a ref
/// that does not resolve (the erased pass reports why).
fn trait_ref_lts(interner: &Interner, known: &Known, cx: &ResolveCx, scope: &Scope, tref: &ast::TraitRefExpr) -> Option<(DefId, Vec<Region>)> {
    let trait_def = trait_def_of_path(cx, interner, known, &tref.path, Span::default()).ok()?;
    let n = cx.adt_lifetimes.get(&trait_def).map_or(0, |v| v.len());
    if n == 0 {
        return None;
    }
    let mut ks = scope.clone();
    ks.regions = RegionMode::Keep { next: None, elided: None };
    let GenericArgs::Angle(args) = &tref.path.last()?.args else { return None };
    let mut lts = Vec::with_capacity(n);
    for a in args {
        if let AstArg::Lifetime(lt) = a {
            lts.push(scope_region(interner, &ks, Some(*lt), lt.span).ok()?);
        }
    }
    (lts.len() == n).then_some((trait_def, lts))
}

/// The `T: Tr<'a, ..>` bounds that a generics list and its where clause
/// put on type params of `scope`, for traits with lifetime params
/// (W-BORROW, `RegionSig::trait_bounds`). A method also takes its impl's
/// or trait's.
pub fn trait_lts_of(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    scope: &Scope,
    generics: &ast::Generics,
    where_clause: &ast::WhereClause,
) -> Vec<crate::borrowck::TraitLts> {
    trait_lts_in(interner, known, cx, scope, &param_bounds(ast, scope, generics, where_clause))
}

/// `trait_lts_of` over bounds already found, by type param index.
fn trait_lts_in(interner: &Interner, known: &Known, cx: &ResolveCx, scope: &Scope, bounded: &[(u32, &[TraitBound])]) -> Vec<crate::borrowck::TraitLts> {
    let mut out = Vec::new();
    for &(j, bounds) in bounded {
        for b in bounds {
            if let TraitBound::Trait { trait_ref, .. } = b
                && let Some((trait_def, lifetimes)) = trait_ref_lts(interner, known, cx, scope, trait_ref)
            {
                out.push(crate::borrowck::TraitLts { param: j, trait_def, lifetimes });
            }
        }
    }
    out
}

/// The types the bounds of a generics list, a where clause, and `extra`
/// bounds (`(Self, bounds)`: supertraits, `impl Trait` args) name, with
/// regions kept, for `check::outlives`: each bound's trait args (Self
/// included) and bound types. An elided region is `Region::Bound` (it
/// puts no requirement); a bound that does not resolve is left out, as
/// the erased pass reports it.
#[allow(clippy::too_many_arguments)]
pub fn regioned_bound_tys(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    generics: &ast::Generics,
    where_clause: &ast::WhereClause,
    extra: &[(Ty, &[TraitBound])],
) -> Vec<Ty> {
    let (mut out, preds) = regioned_bound_preds(ast, interner, known, cx, tys, scope, generics, where_clause, extra);
    for pred in preds {
        if let Predicate::Trait(b) = pred {
            crate::check::outlives::trait_ref_wf_tys(tys, b.value, &mut out);
        }
    }
    out
}

/// The predicates the bounds of a generics list, a where clause, and
/// `extra` bounds put on types, with regions kept (an elided one is
/// `Region::Bound`), and the left-hand types of the where clause. Borrowck
/// replays the impl a trait predicate selects (`RegionSig::bounds`,
/// `ImplRegions::preds`). A bound that does not resolve is left out.
#[allow(clippy::too_many_arguments)]
pub fn regioned_bound_preds(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    generics: &ast::Generics,
    where_clause: &ast::WhereClause,
    extra: &[(Ty, &[TraitBound])],
) -> (Vec<Ty>, Vec<Predicate>) {
    let bounded = generics.params.iter().any(|gp| matches!(gp, ast::GenericParam::Type { bounds, .. } if !bounds.is_empty()));
    if !bounded && where_clause.preds.is_empty() && extra.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let mut ks = scope.clone();
    ks.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    let mut lhs_bounds: Vec<(Ty, &[TraitBound])> = extra.to_vec();
    for gp in &generics.params {
        if let ast::GenericParam::Type { name, bounds, .. } = gp
            && let Some(j) = scope.param_of(*name)
        {
            lhs_bounds.push((tys.intern(TyKind::Param(ParamId(j))), bounds));
        }
    }
    let mut lhs_tys = Vec::new();
    for pred in &where_clause.preds {
        if let ast::WherePred::Type { ty, bounds, .. } = pred
            && let Ok(lhs) = resolve_scoped(ast, interner, known, cx, tys, *ty, &ks)
        {
            lhs_tys.push(lhs);
            lhs_bounds.push((lhs, bounds));
        }
    }
    let (mut preds, mut relaxed, mut errs) = (Vec::new(), Vec::new(), Vec::new());
    for (lhs, bounds) in lhs_bounds {
        for b in bounds {
            bound_predicates(ast, interner, known, cx, tys, &ks, lhs, b, &mut preds, &mut relaxed, &mut errs);
        }
    }
    (lhs_tys, preds)
}

/// The types a fn may assume well-formed (`check::outlives`): its params
/// and return resolved with regions kept and elided ones erased (a bound
/// can name only the named ones), and its impl's header types. `params`
/// are the erased param types (self first): an `impl Trait` arg keeps its
/// synthetic param. A type that does not resolve is left out.
#[allow(clippy::too_many_arguments)]
pub fn implied_sig_tys(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    def: &ast::FnDef,
    params: &[Ty],
) -> Vec<Ty> {
    let mut ks = scope.clone();
    ks.regions = RegionMode::Keep { next: None, elided: Some(Region::Erased) };
    let mut out: Vec<Ty> = scope.header_regioned.clone();
    let skip = usize::from(def.self_param.is_some());
    if let (Some(sp), Some(st)) = (&def.self_param, scope.self_ty_regioned.or(scope.self_ty)) {
        match (sp.kind, sp.ty) {
            (ast::SelfKind::Typed, Some(t)) => out.extend(resolve_scoped(ast, interner, known, cx, tys, t, &ks).ok()),
            // `&'a self` gives `Self: 'a` (its params outlive `'a`).
            (ast::SelfKind::Ref | ast::SelfKind::RefMut, _) => match scope_region(interner, &ks, sp.lifetime, sp.span) {
                Ok(r) => out.push(tys.intern(TyKind::Ref(r, Mut::from_bool(sp.kind == ast::SelfKind::RefMut), st))),
                Err(_) => out.push(st),
            },
            _ => out.push(st),
        }
    }
    for (prm, &t) in def.params.iter().zip(params.get(skip..).unwrap_or_default()) {
        if matches!(ast.ty(prm.ty), TyExpr::ImplTrait { .. }) {
            out.push(t);
        } else {
            out.extend(resolve_scoped(ast, interner, known, cx, tys, prm.ty, &ks).ok());
        }
    }
    if let Some(r) = def.ret
        && !matches!(ast.ty(r), TyExpr::ImplTrait { .. })
    {
        out.extend(resolve_scoped(ast, interner, known, cx, tys, r, &ks).ok());
    }
    out
}

/// The `impl Trait` args of a fn (top-level and nested), as `(param,
/// bounds)` for `regioned_bound_tys`. `params` are the fn's erased param
/// types after `self`.
pub fn apit_bounds<'a>(ast: &'a Ast, def: &ast::FnDef, params: &[Ty], scope: &Scope) -> Vec<(Ty, &'a [TraitBound])> {
    let mut out: Vec<(Ty, &[TraitBound])> = Vec::new();
    for (prm, &t) in def.params.iter().zip(params) {
        if let TyExpr::ImplTrait { bounds, .. } = ast.ty(prm.ty) {
            out.push((t, bounds));
        }
    }
    for &(n, t) in &scope.apit {
        if let TyExpr::ImplTrait { bounds, .. } = ast.ty(n) {
            out.push((t, bounds));
        }
    }
    out
}

/// The bounds that a generics list and its where clause put on the type
/// params of `scope`, by param index.
fn param_bounds<'a>(ast: &'a Ast, scope: &Scope, generics: &'a ast::Generics, where_clause: &'a ast::WhereClause) -> Vec<(u32, &'a [TraitBound])> {
    let param = |name| scope.type_params.iter().find(|&&(n, _)| n == name).map(|&(_, j)| j);
    let mut bounded: Vec<(u32, &[TraitBound])> = Vec::new();
    for gp in &generics.params {
        if let ast::GenericParam::Type { name, bounds, .. } = gp
            && let Some(j) = param(*name)
        {
            bounded.push((j, bounds));
        }
    }
    for pred in &where_clause.preds {
        if let ast::WherePred::Type { ty, bounds, .. } = pred
            && let TyExpr::Path(segs) = ast.ty(*ty)
            && let [seg] = &segs[..]
            && matches!(seg.args, ast::GenericArgs::None)
            && let Some(j) = param(seg.name)
        {
            bounded.push((j, bounds));
        }
    }
    bounded
}

/// The `F: Fn*(A..) -> R` bounds that a generics list and its where
/// clause put on type params of `scope` (W-BORROW, `RegionSig::fn_bounds`;
/// parenthesized sugar names only those traits): inputs and output with
/// written lifetimes kept and elided ones bound by the sugar
/// (`Region::Bound`), so borrowck knows which are higher-ranked. A method
/// also takes its impl's or trait's. A bound it cannot resolve is left out.
#[allow(clippy::too_many_arguments)]
pub fn fn_bounds_of(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    scope: &Scope,
    generics: &ast::Generics,
    where_clause: &ast::WhereClause,
) -> Vec<crate::borrowck::FnBound> {
    fn_bounds_in(ast, interner, known, tys, cx, scope, &param_bounds(ast, scope, generics, where_clause))
}

/// The `I: Tr<Item = X>` bounds a generics list and its where clause put
/// on type params of `scope` (`RegionSig::item_bounds`): a method also
/// takes its impl's or trait's.
#[allow(clippy::too_many_arguments)]
pub fn item_bounds_of(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    scope: &Scope,
    generics: &ast::Generics,
    where_clause: &ast::WhereClause,
) -> Vec<(u32, DefId, Ty)> {
    item_bounds_in(ast, interner, known, tys, cx, scope, &param_bounds(ast, scope, generics, where_clause))
}

/// rustc E0106 in the bounds of a returned `impl Trait` (`impl
/// Iterator<Item = &T>`, `impl Sized + '_`) when the output has no
/// elided lifetime to take (`region_sig`, scope `rs`): the return type
/// itself resolves to the opaque without its bounds. The L0202 of the
/// first such bound, if any.
fn opaque_elision(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    rs: &Scope,
    ret: ast::TyId,
) -> Option<Diag> {
    let mut nodes: Vec<ast::TyId> = Vec::new();
    nested_impl_traits(ast, ret, &mut nodes);
    let lhs = tys.intern(TyKind::Param(ParamId(u32::MAX)));
    for n in nodes {
        let TyExpr::ImplTrait { bounds, .. } = ast.ty(n) else { continue };
        for b in bounds {
            if let TraitBound::Lifetime(lt) = b
                && interner.get(lt.name) == "_"
            {
                return scope_region(interner, rs, Some(*lt), lt.span).err();
            }
            // `Fn(&u8) -> &u8` sugar is its own elision scope.
            if let TraitBound::Trait { trait_ref, .. } = b
                && trait_ref.path.last().is_some_and(|s| matches!(s.args, GenericArgs::Parenthesized { .. }))
            {
                continue;
            }
            let (mut preds, mut relaxed, mut errs) = (Vec::new(), Vec::new(), Vec::new());
            bound_predicates(ast, interner, known, cx, tys, rs, lhs, b, &mut preds, &mut relaxed, &mut errs);
            if let Some(d) = errs.into_iter().find(|d| d.code == "L0202") {
                return Some(d);
            }
        }
    }
    None
}

/// rustc E0106 inside `Fn` sugar and fn pointer types, which are their
/// own elision scope: an elided lifetime in the output needs exactly one
/// lifetime (written or elided) in the inputs (L0202). Resolves both with
/// regions kept; the main resolution erases them and reports any other
/// error. Returns that one input lifetime (`Region::Bound(0)` when it is
/// elided), which an elided output lifetime is.
#[allow(clippy::too_many_arguments)]
fn sugar_elision(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    inputs: &[ast::TyId],
    output: Option<ast::TyId>,
) -> Result<Option<Region>, Diag> {
    let Some(out) = output else { return Ok(None) };
    let mut ks = scope.clone();
    ks.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    ks.late_elided = false;
    let mut lts: Vec<Region> = Vec::new();
    for &t in inputs {
        let Ok(t) = resolve_scoped(ast, interner, known, cx, tys, t, &ks) else { return Ok(None) };
        crate::borrowck::elision_regions(tys, t, &mut lts);
    }
    // Only lifetimes written in the inputs count, as rustc counts them:
    // the regions a substituted type argument carries (`K = &str` in an
    // instance of `fn(&(K, V)) -> (&K, &V)`, erased in a body) are not
    // elision candidates (W-STD-C: BTreeMap<_, &str>::iter). Elided
    // (`Bound(0)`) and named (`Param`) written ones stay.
    lts.retain(|r| *r != Region::Erased);
    let one = if let [r] = lts[..] { Some(r) } else { None };
    ks.regions = RegionMode::Keep { next: None, elided: one };
    match resolve_scoped(ast, interner, known, cx, tys, out, &ks) {
        Err(d) if d.code == "L0202" => Err(d),
        _ => Ok(one),
    }
}

/// `fn_bounds_of` over bounds already found, by type param index. An
/// elided output lifetime is the only input lifetime, as in a fn
/// signature (`sugar_elision` reports the rest).
#[allow(clippy::too_many_arguments)]
fn fn_bounds_in(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    scope: &Scope,
    bounded: &[(u32, &[TraitBound])],
) -> Vec<crate::borrowck::FnBound> {
    let mut bs = scope.clone();
    bs.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    bs.fn_ptr_free = false;
    let mut out = Vec::new();
    for &(j, bounds) in bounded {
        for b in bounds {
            let TraitBound::Trait { trait_ref, .. } = b else { continue };
            let Some(ast::GenericArgs::Parenthesized { inputs, output }) = trait_ref.path.last().map(|s| &s.args) else { continue };
            let Some(inputs) = inputs.iter().map(|&t| resolve_scoped(ast, interner, known, cx, tys, t, &bs).ok()).collect::<Option<Vec<Ty>>>() else { continue };
            let out_ty = match output {
                Some(t) => {
                    let mut lts: Vec<Region> = Vec::new();
                    for &it in &inputs {
                        crate::borrowck::elision_regions(tys, it, &mut lts);
                    }
                    let mut os = scope.clone();
                    os.fn_ptr_free = false;
                    os.regions = RegionMode::Keep { next: None, elided: if let [r] = lts[..] { Some(r) } else { None } };
                    match resolve_scoped(ast, interner, known, cx, tys, *t, &os) {
                        Ok(t) => Some(t),
                        Err(_) => continue,
                    }
                }
                None => None,
            };
            out.push(crate::borrowck::FnBound { param: j, inputs, output: out_ty });
        }
    }
    out
}

/// The `I: Tr<Item = X>` bounds of `bounded` with `X` resolved, regions
/// kept (`RegionSig::item_bounds`; an elided region is `Region::Bound`).
fn item_bounds_in(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    scope: &Scope,
    bounded: &[(u32, &[TraitBound])],
) -> Vec<(u32, DefId, Ty)> {
    let mut bs = scope.clone();
    bs.regions = RegionMode::Keep { next: None, elided: Some(Region::Bound(0)) };
    let mut out = Vec::new();
    for &(j, bounds) in bounded {
        for b in bounds {
            let TraitBound::Trait { trait_ref, .. } = b else { continue };
            let Some(GenericArgs::Angle(args)) = trait_ref.path.last().map(|s| &s.args) else { continue };
            for a in args {
                if let AstArg::Binding { name, kind: ast::BindingKind::EqTy(t), .. } = a
                    && interner.get(*name) == "Item"
                    && let Ok(trait_def) = trait_def_of_path(cx, interner, known, &trait_ref.path, Span::default())
                    && let Ok(t) = resolve_scoped(ast, interner, known, cx, tys, *t, &bs)
                {
                    out.push((j, trait_def, t));
                }
            }
        }
    }
    out
}

/// True when a written type holds a `dyn` type with a written object
/// lifetime (`dyn Tr + '_`, `dyn Tr + 'static`).
fn has_written_dyn_lifetime(ast: &Ast, id: ast::TyId) -> bool {
    match ast.ty(id) {
        TyExpr::Dyn { bounds, lifetime, .. } => lifetime.is_some() || bounds.iter().any(|b| matches!(b, TraitBound::Lifetime(_))),
        TyExpr::Ref { inner, .. }
        | TyExpr::Paren(inner)
        | TyExpr::Array { inner, .. }
        | TyExpr::Slice(inner)
        | TyExpr::Ptr { inner, .. } => has_written_dyn_lifetime(ast, *inner),
        TyExpr::Tuple(elems) => elems.iter().any(|&e| has_written_dyn_lifetime(ast, e)),
        TyExpr::Path(segs) => segs.iter().any(|seg| match &seg.args {
            GenericArgs::Angle(args) => args.iter().any(|a| matches!(a, AstArg::Type(t) if has_written_dyn_lifetime(ast, *t))),
            _ => false,
        }),
        _ => false,
    }
}


/// Fills in every user trait: its generics and supertraits, its
/// method signature templates, and its associated type defaults.
/// Runs after Adt names exist (signatures name Adts) and before
/// fields and fns resolve (bounds name traits).
pub fn build_trait_tables(p: &mut Program, errs: &mut Vec<Diag>) {
    // Only the first trait of a name is built: a duplicate was reported in
    // pass 0 and owns no record, so building it would look its methods up in
    // the first trait's record.
    let mut seen_traits: Vec<Sym> = Vec::new();
    let trait_items: Vec<(usize, DefId)> = p
        .ast
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match &item.kind {
            ast::ItemKind::Trait(tdef) => {
                if seen_traits.contains(&tdef.name) {
                    None
                } else {
                    seen_traits.push(tdef.name);
                    p.gx.trait_names.get(&tdef.name).map(|&d| (i, d))
                }
            }
            _ => None,
        })
        .collect();
    for (item_i, trait_def) in trait_items {
        let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
        if tdef.is_unsafe {
            p.gx.trait_unsafe.insert(trait_def, true);
        }
        // Clone the AST-side pieces the build needs, so the mutable
        // program borrows below stay simple.
        let tdef_generics = tdef.generics.clone();
        let tdef_where = tdef.where_clause.clone();
        let tdef_bounds = tdef.bounds.clone();
        let (mut generics, mut scope) = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            build_trait_generics(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &tdef_generics, &tdef_where, &tdef_bounds, errs)
        };
        // The types the trait's own bounds name assume nothing.
        {
            let self_ty = p.tys.intern(TyKind::Param(ParamId(0)));
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let mut ss = scope.clone();
            ss.self_ty = Some(self_ty);
            let required =
                regioned_bound_tys(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &ss, &tdef_generics, &tdef_where, &[(self_ty, &tdef_bounds)]);
            // Its trait bounds with regions: each impl owes them by regions
            // too (`borrowck::check_impl_supers`).
            let (_, preds) =
                regioned_bound_preds(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &ss, &tdef_generics, &tdef_where, &[(self_ty, &tdef_bounds)]);
            let preds: Vec<Predicate> = preds.into_iter().filter(|q| matches!(q, Predicate::Trait(b) if b.count == 0)).collect();
            if !preds.is_empty() && !p.in_lang_methods(p.ast.items[item_i].span) && p.shipped_crate_at(p.ast.items[item_i].span).is_none() {
                p.regions.trait_preds.insert(trait_def, preds);
            }
            let item = crate::check::outlives::Item {
                implied: Vec::new(),
                required,
                facts: scope.region_facts.clone(),
                preds: generics.predicates.clone(),
                span: p.ast.items[item_i].span,
            };
            if crate::check::outlives::wanted(p, &item) {
                p.regions.outlives_items.push(item);
            }
        }
        let defaults = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            crate::check::defaults::resolve_all(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &tdef_generics, true, errs)
        };
        if defaults.iter().any(Option::is_some) {
            p.gx.param_defaults.insert(trait_def, defaults);
        }
        // The trait's own associated items are sources on its Self.
        {
            let rec = p.gx.index.trait_record(trait_def).cloned();
            if let Some(rec) = rec {
                let self_args: Vec<GenericArg> = (0..generics.params.len() as u32)
                    .map(|i| {
                        let t = p.tys.intern(TyKind::Param(ParamId(i)));
                        GenericArg::Ty(t)
                    })
                    .collect();
                let args = p.tys.intern_args(&self_args);
                scope.assoc_srcs.push(AssocSrc {
                    self_ty: scope.self_ty.unwrap_or(ERROR),
                    trait_def,
                    args,
                    assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
                });
            }
        }
        // Associated types: bounds become predicates on the
        // projection; defaults resolve under the trait scope.
        let assoc_defs: Vec<(usize, DefId)> = {
            // A name with no record entry is a duplicate dropped in pass 0;
            // it was already reported there, so skip it here.
            let Some(rec) = p.gx.index.trait_record(trait_def) else { continue };
            tdef.types.iter().enumerate().filter_map(|(i, at)| rec.assoc_by_name(at.name).map(|d| (i, d))).collect()
        };
        for (at_i, assoc_def) in assoc_defs {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            let at = &tdef.types[at_i];
            if !at.generics.params.is_empty() {
                errs.push(not_yet("L0621", at.generics.span, "generic associated types"));
            }
            let self_args: Vec<GenericArg> = (0..generics.params.len() as u32)
                .map(|i| {
                    let t = p.tys.intern(TyKind::Param(ParamId(i)));
                    GenericArg::Ty(t)
                })
                .collect();
            let trait_args = p.tys.intern_args(&self_args);
            let proj = p.tys.intern(TyKind::Projection(AssocId(assoc_def), trait_args));
            let at_bounds = at.bounds.clone();
            let at_where = at.where_clause.clone();
            let at_default = at.default;
            {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                let mut relaxed: Vec<u32> = Vec::new();
                let mut preds: Vec<Predicate> = Vec::new();
                for b in &at_bounds {
                    bound_predicates(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &scope, proj, b, &mut preds, &mut relaxed, errs);
                }
                // An associated type has an implicit `Sized` bound
                // unless the trait writes `type A: ?Sized` (rustc
                // E0277 on an unsized binding at the impl).
                let has_sized = preds.iter().any(|pred| {
                    matches!(pred, Predicate::Trait(b) if b.value.def == cx.lang.sized
                        && p.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(proj))
                });
                if !relaxed.contains(&u32::MAX) && !has_sized {
                    let args = p.tys.intern_args(&[GenericArg::Ty(proj)]);
                    preds.push(Predicate::Trait(Binder::plain(TraitRef { def: cx.lang.sized, args, bindings: EMPTY_BINDINGS })));
                }
                generics.predicates.extend(preds);
                let _ = at_where;
                if at_default.is_some() {
                    // Associated type defaults are unstable in
                    // rustc (E0658); rule zero rejects them.
                    errs.push(not_yet("L0621", at.span, "associated type defaults"));
                }
                if let Some(d) = at_default {
                    match resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, d, &scope) {
                        Ok(t) => {
                            p.gx.trait_assoc_defaults.insert(assoc_def, t);
                        }
                        Err(diag) => errs.push(diag),
                    }
                }
            }
        }
        // Associated consts: resolve and store the type for impl
        // validation. The values ride the const evaluator when a
        // use needs them.
        let const_parts: Vec<(Sym, ast::TyId, bool)> = {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            tdef.consts.iter().map(|ac| (ac.name, ac.ty, ac.default.is_some())).collect()
        };
        for (ac_name, ty, has_default) in const_parts {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            match resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, ty, &scope) {
                Ok(t) => {
                    if let Some(assoc) = p.gx.index.trait_record(trait_def).and_then(|r| r.assoc_by_name(ac_name)) {
                        p.gx.trait_assoc_consts.insert(assoc, (t, has_default));
                    }
                }
                Err(d) => errs.push(d),
            }
        }
        // Method signature templates over trait ++ own generics.
        let fn_count = {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            tdef.fns.len()
        };
        let env = elaborate_env(&mut p.tys, &p.gx.index, &generics.predicates);
        for fn_i in 0..fn_count {
            let Some((fdef, method_def)) = ({
                let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
                let f = &tdef.fns[fn_i];
                // No record entry means a duplicate dropped in pass 0.
                p.gx.index.trait_record(trait_def).and_then(|rec| rec.method_by_name(f.name)).map(|d| (f, d))
            }) else {
                continue;
            };
            let shift = generics.params.len() as u32;
            let (own_generics, own_scope) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                build_generics_shifted(
                    &p.ast,
                    &p.interner,
                    &p.known,
                    &cx,
                    &mut p.tys,
                    &fdef.generics,
                    &fdef.where_clause,
                    shift,
                    &scope,
                    errs,
                )
            };
            let mut combined = generics.clone();
            combined.params.extend(own_generics.params.iter().cloned());
            combined.predicates.extend(own_generics.predicates.iter().copied());
            // No shadowing of the trait's parameters (E0403). Duplicates
            // inside one list are reported by `build_generics_shifted`.
            for param in &own_generics.params {
                if generics.params.iter().any(|q| q.name == param.name) {
                    errs.push(Diag::new(
                        "L0106",
                        param.span,
                        format!("the parameter `{}` is already used for a parameter of an enclosing item", p.name(param.name)),
                        "Rename one of the parameters.",
                    ));
                }
            }
            let mut mscope = scope.clone();
            mscope.lifetimes.extend(own_scope.lifetimes.iter().copied());
            mscope.region_facts.extend(own_scope.region_facts.iter().copied());
            mscope.type_params.extend(own_scope.type_params.iter().copied());
            mscope.const_params.extend(own_scope.const_params.iter().copied());
            mscope.param_tys.extend(own_scope.param_tys.iter().copied());
            let (params, ret, ret_borrows_from, combined, mscope, region_sig, _) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                resolve_fn_sig(&p.ast, &p.interner, &p.known, &mut p.tys, &cx, fdef, combined, &mscope, scope.self_ty, None, errs)
            };
            {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                let skip = usize::from(fdef.self_param.is_some());
                let extra = apit_bounds(&p.ast, fdef, &params[skip.min(params.len())..], &mscope);
                let mut required =
                    regioned_bound_tys(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &mscope, &fdef.generics, &fdef.where_clause, &extra);
                let copied_proj = params.iter().chain([&ret]).any(|&t| crate::check::outlives::has_copied_projection(&p.tys, t));
                let implied = if required.is_empty() && !copied_proj {
                    Vec::new()
                } else {
                    implied_sig_tys(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, &mscope, fdef, &params)
                };
                required.extend(crate::check::outlives::copied_projection_selves(&p.tys, &implied));
                let item = crate::check::outlives::Item {
                    implied,
                    required,
                    facts: mscope.region_facts.clone(),
                    preds: combined.predicates.clone(),
                    span: fdef.name_span,
                };
                if crate::check::outlives::wanted(p, &item) {
                p.regions.outlives_items.push(item);
            }
            }
            if let Some(mut rs) = region_sig {
                // `F: Fn*` and `T: Tr<'a>` bounds on the trait's own type
                // params too (W-BORROW).
                let ast = p.ast.clone();
                if let ast::ItemKind::Trait(tdef) = &ast.items[item_i].kind {
                    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    rs.fn_bounds.extend(fn_bounds_of(
                        &ast,
                        &p.interner,
                        &p.known,
                        &mut p.tys,
                        &cx,
                        &mscope,
                        &tdef.generics,
                        &tdef.where_clause,
                    ));
                    rs.trait_bounds.extend(trait_lts_of(&ast, &p.interner, &p.known, &cx, &mscope, &tdef.generics, &tdef.where_clause));
                    rs.item_bounds.extend(item_bounds_of(&ast, &p.interner, &p.known, &mut p.tys, &cx, &mscope, &tdef.generics, &tdef.where_clause));
                    // The trait's bounds and supertraits, and the implicit
                    // `Self: Tr<P..>` of its methods, with regions.
                    let self_param = p.tys.intern(TyKind::Param(ParamId(0)));
                    let extra: Vec<(Ty, &[TraitBound])> = vec![(self_param, &tdef.bounds)];
                    let (_, preds) =
                        regioned_bound_preds(&ast, &p.interner, &p.known, &cx, &mut p.tys, &mscope, &tdef.generics, &tdef.where_clause, &extra);
                    rs.bounds.extend(preds);
                    let mut args = vec![GenericArg::Ty(self_param)];
                    for gp in &tdef.generics.params {
                        if let ast::GenericParam::Type { name, .. } = gp
                            && let Some(j) = scope.param_of(*name)
                        {
                            args.push(GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(j)))));
                        }
                    }
                    let args = p.tys.intern_args(&args);
                    rs.bounds.push(Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS })));
                }
                p.regions.trait_methods.insert(method_def, rs);
            }
            let menv = body_env(&mut p.tys, &p.gx.index, &combined.predicates);
            p.gx.trait_methods.insert(
                method_def,
                TraitMethodTemplate {
                    loc: crate::check::collect::FnLoc::Trait(item_i as u32, fn_i as u32),
                    name: fdef.name,
                    self_kind: fdef.self_param.as_ref().map(|s| s.kind),
                    params,
                    ret,
                    ret_borrows_from,
                    generics: combined,
                    env: menv,
                    scope: mscope,
                },
            );
        }
        // Replace the placeholder record with the full one.
        {
            let Some(old) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            p.gx.index.insert_trait(TraitRecord { generics: generics.clone(), ..old });
            let mut data =
                crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Trait, None, old.name, crate::ty::defs::Vis::Priv, old.span);
            data.generics = generics;
            p.defs.insert(trait_def, data);
        }
        scope.assoc_srcs = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            assoc_srcs_of(&cx, &p.tys, &env)
        };
        p.gx.trait_scopes.insert(trait_def, scope);
    }
}

/// One synthetic (derive or lang) impl def, minted under the
/// local crate so slot and cache identity stay inside it.
fn synthetic_impl_def(p: &Program, ordinal: u32) -> DefId {
    DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &["<synthetic>"], crate::def::DefKind::Impl, "impl", ordinal) }
}

/// Builds the next synthetic impl record in the index. Returns
/// its id, or None when the Self pattern has no indexed head.
pub(crate) fn insert_synthetic(
    p: &mut Program,
    ordinal: &mut u32,
    trait_def: DefId,
    self_pat: Ty,
    rest: &[Ty],
    generics: Generics,
    assoc_tys: Vec<(DefId, Ty)>,
    synthetic: crate::traits::index::Synthetic,
    local: bool,
    span: Span,
) -> Option<crate::traits::ImplId> {
    use crate::traits::index::{ImplRecord, pattern_head};
    let mut all = vec![GenericArg::Ty(self_pat)];
    all.extend(rest.iter().map(|&t| GenericArg::Ty(t)));
    let args = p.tys.intern_args(&all);
    let (head, blanket) = pattern_head(&p.tys, self_pat, &[])?;
    let def = synthetic_impl_def(p, *ordinal);
    *ordinal += 1;
    Some(p.gx.index.insert_impl(ImplRecord {
        def,
        trait_def,
        trait_ref: TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS },
        generics,
        assoc_tys,
        assoc_consts: Vec::new(),
        items: Vec::new(),
        synthetic,
        local,
        span,
        head,
        blanket,
    }))
}

/// `trait Tr: 'static` and `type A: 'static` in the trait: the impl's
/// Self type and its binding of `A`, in region form (the impl scope's
/// `self_ty_regioned` and `assoc_regioned`), must name no lifetime but
/// `'static` (rustc E0477, E0478). The erased check in
/// `check_impl_obligations` sees no lifetime args of an Adt
/// (`impl<'a> Tr for S<'a>`). A `'a: 'static` bound is not read, so
/// such an impl is a false reject.
fn static_header_regions(p: &mut Program, imp: &ast::ImplDef, rec: &TraitRecord, scope: &Scope, errs: &mut Vec<Diag>) {
    let self_param = p.tys.intern(TyKind::Param(ParamId(0)));
    let mut wants: Vec<Ty> = Vec::new();
    for pred in &rec.generics.predicates {
        let Predicate::TypeOutlives(x, Region::Static) = *pred else { continue };
        if x == self_param {
            wants.extend(scope.self_ty_regioned);
        } else if let TyKind::Projection(assoc, a) = p.tys.kind(x)
            && p.tys.args(a).first().and_then(|g| g.as_ty()) == Some(self_param)
            && let Some(&(_, name, _)) = rec.assoc_items.iter().find(|(d, _, _)| *d == assoc.0)
        {
            wants.extend(scope.assoc_regioned.iter().filter(|(n, _)| *n == name).map(|&(_, t)| t));
        }
    }
    for t in wants {
        let mut rs = Vec::new();
        crate::borrowck::regions_of(&p.tys, t, &mut rs);
        if rs.iter().any(|r| matches!(r, Region::Param(_))) {
            let tname = p.display_path(rec.name);
            errs.push(Diag::new(
                "L0612",
                imp.span,
                format!("this impl of `{tname}` does not satisfy the `'static` bound the trait requires: a lifetime in it is not `'static`"),
                "Implement the trait for a type without references, or add `'static` bounds to the impl's type parameters.",
            ));
            return;
        }
    }
}

/// Finishes one trait impl: associated bindings, the index
/// record, the orphan check, and method signature validation
/// against the trait. Called from collect's fn pass after the
/// impl's methods are in `fns`.
#[allow(clippy::too_many_arguments)]
pub fn finish_trait_impl(
    p: &mut Program,
    imp: &ast::ImplDef,
    impl_def: DefId,
    impl_generics: Generics,
    self_pat: Ty,
    tr: TraitRef,
    scope: &Scope,
    method_ids: &[LocalDefId],
    errs: &mut Vec<Diag>,
) {
    use crate::traits::index::{ImplRecord, Synthetic, pattern_head};
    let Some(rec) = p.gx.index.trait_record(tr.def).cloned() else { return };
    static_header_regions(p, imp, &rec, scope, errs);
    // One impl may define each associated name once (rustc E0201): types
    // in the type namespace, consts and methods in the value namespace.
    {
        let mut seen: Vec<Sym> = Vec::new();
        for at in &imp.types {
            if seen.contains(&at.name) {
                errs.push(Diag::new(
                    "L0106",
                    at.name_span,
                    format!("`{}` is defined more than once", p.display_name(at.name)),
                    "Rename one of the definitions.",
                ));
            } else {
                seen.push(at.name);
            }
        }
        let mut seen: Vec<Sym> = Vec::new();
        for (name, span) in imp.consts.iter().map(|c| (c.name, c.name_span)).chain(imp.fns.iter().map(|f| (f.name, f.name_span))) {
            if seen.contains(&name) {
                errs.push(Diag::new(
                    "L0106",
                    span,
                    format!("`{}` is defined more than once", p.display_name(name)),
                    "Rename one of the definitions.",
                ));
            } else {
                seen.push(name);
            }
        }
    }
    // Associated types: resolve the written bindings, fill the
    // rest from trait defaults, and require every assoc type.
    let mut assoc_tys: Vec<(DefId, Ty)> = Vec::new();
    for at in &imp.types {
        let Some(assoc) = rec.assoc_by_name(at.name) else {
            errs.push(Diag::new(
                "L0102",
                at.name_span,
                format!("trait has no associated type named `{}`", p.name(at.name)),
                "Check the spelling against the trait definition.",
            ));
            continue;
        };
        match at.default {
            Some(d) => {
                // An assoc type's value elides no lifetime (rustc E0637);
                // its names were checked by `resolve_scoped`.
                let names: Vec<Sym> = scope.lifetimes.iter().map(|&(n, _)| n).collect();
                if let Some(diag) = item_ty_lifetime_err(&p.ast, &p.interner, d, &names, false) {
                    errs.push(diag);
                }
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                match resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, d, scope) {
                    Ok(t) => assoc_tys.push((assoc, t)),
                    Err(diag) => errs.push(diag),
                }
            }
            None => errs.push(Diag::new(
                "L0110",
                at.name_span,
                "an associated type in an impl must be assigned a type",
                format!("Write `type {} = Type;`.", p.name(at.name)),
            )),
        }
    }
    for &(assoc, _name, is_type) in &rec.assoc_items {
        if !is_type || assoc_tys.iter().any(|(d, _)| *d == assoc) {
            continue;
        }
        match p.gx.trait_assoc_defaults.get(&assoc).copied() {
            Some(default) => {
                let args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
                let t = subst(&mut p.tys, default, &args);
                assoc_tys.push((assoc, t));
            }
            None => errs.push(Diag::new(
                "L0110",
                imp.span,
                "the impl does not bind every associated type of the trait",
                "Add the missing `type Name = Type;` items.",
            )),
        }
    }
    // Associated consts: presence is required the same way (a
    // trait default covers a missing one), and a written const
    // must have the trait's type for it. Their values are
    // const-evaluated at use sites.
    for ac in &imp.consts {
        let Some(assoc) = rec.assoc_by_name(ac.name) else {
            errs.push(Diag::new(
                "L0102",
                ac.name_span,
                format!("trait has no associated const named `{}`", p.name(ac.name)),
                "Check the spelling against the trait definition.",
            ));
            continue;
        };
        if let Some(&(want, _)) = p.gx.trait_assoc_consts.get(&assoc) {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            // `Self::A` in the written type names this impl's binding
            // for `A` (`const MIN: Self::Primitive = 0;`).
            let args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
            let self_ty = args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
            let mut sc = scope.clone();
            sc.assoc_srcs.push(AssocSrc {
                self_ty,
                trait_def: tr.def,
                args: tr.args,
                assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
            });
            match resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, ac.ty, &sc) {
                Ok(got) => {
                    let got = rewrite_impl_projections(p, got, self_ty, &assoc_tys);
                    let want = subst(&mut p.tys, want, &args);
                    // `Self::A` in the declared type is this impl's
                    // binding for `A` (as for method signatures).
                    let want = rewrite_impl_projections(p, want, self_ty, &assoc_tys);
                    if got != want {
                        errs.push(Diag::new(
                            "L0110",
                            ac.name_span,
                            format!("associated const `{}` has a different type than the trait declares", p.name(ac.name)),
                            "Match the type in the trait definition.",
                        ));
                    }
                }
                Err(diag) => errs.push(diag),
            }
        }
    }
    for &(assoc, cname, is_type) in &rec.assoc_items {
        if is_type || imp.consts.iter().any(|ac| ac.name == cname) {
            continue;
        }
        // Lang traits store no const types here; only user-trait
        // consts (recorded above) can be required.
        if p.gx.trait_assoc_consts.get(&assoc).is_some_and(|&(_, d)| !d) {
            errs.push(Diag::new(
                "L0110",
                imp.span,
                format!("the impl is missing the associated const `{}`", p.name(cname)),
                "Add the const to the impl.",
            ));
        }
    }
    let Some((head, blanket)) = pattern_head(&p.tys, self_pat, &[]) else {
        errs.push(not_yet("L0614", imp.span, "impls for this Self type form"));
        return;
    };
    let items: Vec<DefId> = method_ids.iter().map(|&id| p.def_id(id)).collect();
    // A std or lang trait impl: the user Adts its trait ref names key the
    // `LangImpls` reads of the bodies that can select it
    // (`ImplIndex::name_adts`).
    let named: Vec<DefId> = if p.impls_read_covered(tr.def) { Vec::new() } else { p.lang_named_adts(tr.args) };
    let impl_id = p.gx.index.insert_impl(ImplRecord {
        def: impl_def,
        trait_def: tr.def,
        trait_ref: tr,
        generics: impl_generics.clone(),
        assoc_tys: assoc_tys.clone(),
        assoc_consts: Vec::new(),
        items,
        synthetic: Synthetic::None,
        local: true,
        span: imp.span,
        head,
        blanket,
    });
    p.gx.index.name_adts(impl_id, &named);
    // The orphan rule (section 2.3). Std source impls are std's own;
    // std source module types are foreign to user impls (W-STD-C).
    if !p.std_source_span(imp.span) {
        let rec_scoped = p.gx.index.get(impl_id).clone();
        // A def of a shipped crate in the session (an adapter, or the
        // std platform crate of W-SHIM) is foreign to every other crate.
        let impl_crate = p.shipped_crate_at(imp.span);
        // A std source module type (W-STD-C) is foreign too.
        let is_local = |d: DefId| {
            d.krate == p.krate
                && p.defs.get(d).is_none_or(|x| p.shipped_crate_at(x.span) == impl_crate)
                && !p.tys.local_adt_of(d).is_some_and(|a| p.is_std_adt(a))
        };
        // `Box` is fundamental: `Box<Local>` counts as local.
        let fundamental = [p.tys.builtins().boxed];
        if !p.gx.index.orphan_ok(&p.tys, &rec_scoped, &fundamental, &is_local) {
            errs.push(Diag::new(
                "L0616",
                imp.span,
                "this impl is not allowed here: neither the trait nor the type is defined in this file",
                "Implement the trait for a local type, or define the trait locally.",
            ));
        }
    }
    check_impl_rules(p, imp, &impl_generics, self_pat, tr, errs);
    errs.extend(crate::check::platform::user_impl_of_hidden(p, imp.span, tr.def, method_ids));
    crate::check::fmt::check_fmt_impl(p, imp, tr, self_pat, method_ids, errs);
    // Method validation against the trait's templates.
    let impl_parent_n = impl_generics.params.len();
    for (method_def, mname) in &rec.methods {
        let found = method_ids.iter().copied().find(|&id| p.fn_info(id).name == *mname);
        let Some(tmpl) = p.gx.trait_methods.get(method_def).cloned() else {
            // A lang trait's method has no template (`fmt` is checked
            // by check_fmt_impl).
            if tr.def != p.gx.lang.debug && tr.def != p.gx.lang.display {
                check_lang_method(p, imp, tr, *method_def, *mname, found, impl_parent_n, &assoc_tys, imp.span, errs);
            }
            continue;
        };
        let Some(local) = found else {
            if tmpl.def(&p.ast).body.is_none() {
                errs.push(Diag::new(
                    "L0110",
                    imp.span,
                    format!("the impl is missing the trait method `{}`", p.name(*mname)),
                    "Add the method to the impl.",
                ));
            }
            continue;
        };
        validate_method_sig(p, &tmpl, local, tr, impl_parent_n, &impl_generics.predicates.clone(), &assoc_tys, imp.span, errs);
    }
    // A method signature that names this impl's own associated types
    // (`fn next(&mut self) -> Option<Self::Item>`) means its bindings:
    // the signature callers and codegen read holds the bound types (the
    // projection stayed, and codegen typed it `()`).
    for &local in method_ids {
        let (params, ret) = (p.fn_info(local).params.clone(), p.fn_info(local).ret);
        let params: Vec<Ty> = params.into_iter().map(|t| rewrite_own_projections(p, t, tr.args, &assoc_tys)).collect();
        let ret = rewrite_own_projections(p, ret, tr.args, &assoc_tys);
        let f = &mut p.fns[local.0 as usize];
        f.params = params;
        f.ret = ret;
    }
    for &local in method_ids {
        let name = p.fn_info(local).name;
        if rec.method_by_name(name).is_none() {
            errs.push(Diag::new(
                "L0110",
                p.fn_def(local).name_span,
                format!("`{}` is not a member of the trait being implemented", p.name(name)),
                "Move it to an inherent impl, or add it to the trait.",
            ));
        }
    }
}

/// The trait of the trait impl that holds method `f`, when the header
/// delta can take an edit of `f` (driver/kept_delta.rs): a local user
/// trait outside std whose impls `ImplSet` reads cover
/// (`Program::impls_read_covered`), with a written template for the
/// method. Operators and `for` loops reach only lang traits, which name
/// no read; these callers all read the trait's impl buckets.
pub(crate) fn delta_impl_trait(p: &Program, f: LocalDefId) -> Option<DefId> {
    let impl_def = p.defs.get(p.def_id(f)).and_then(|d| d.parent)?;
    let (_, rec) = p.gx.index.by_def(impl_def)?;
    let tr = p.gx.index.trait_record(rec.trait_def)?;
    let user = tr.local && !p.std_source_span(tr.span) && p.shipped_crate_at(tr.span).is_none() && p.impls_read_covered(tr.def);
    let method = tr.method_by_name(p.fn_info(f).name)?;
    (user && matches!(rec.synthetic, crate::traits::index::Synthetic::None) && p.gx.trait_methods.contains_key(&method)).then_some(tr.def)
}

/// `finish_trait_impl`'s work for one method `f` of a trait impl, after a
/// header delta wrote its new record (`delta_audit::redo_sig`): the compare
/// against the trait method, then the rewrite of the impl's own
/// associated types in its signature. False when `f` is not such a method.
pub(crate) fn redo_impl_method(p: &mut Program, f: LocalDefId, errs: &mut Vec<Diag>) -> bool {
    let Some(impl_def) = p.defs.get(p.def_id(f)).and_then(|d| d.parent) else { return false };
    let Some((_, rec)) = p.gx.index.by_def(impl_def) else { return false };
    let (tr, generics, assoc_tys, span) = (rec.trait_ref, rec.generics.clone(), rec.assoc_tys.clone(), rec.span);
    let Some(method) = p.gx.index.trait_record(tr.def).and_then(|r| r.method_by_name(p.fn_info(f).name)) else { return false };
    let Some(tmpl) = p.gx.trait_methods.get(&method).cloned() else { return false };
    validate_method_sig(p, &tmpl, f, tr, generics.params.len(), &generics.predicates, &assoc_tys, span, errs);
    let (params, ret) = (p.fn_info(f).params.clone(), p.fn_info(f).ret);
    let params: Vec<Ty> = params.into_iter().map(|t| rewrite_own_projections(p, t, tr.args, &assoc_tys)).collect();
    let ret = rewrite_own_projections(p, ret, tr.args, &assoc_tys);
    let info = &mut p.fns[f.0 as usize];
    (info.params, info.ret) = (params, ret);
    true
}

/// True when const parameter `idx` occurs in a type (in an
/// array length or a const argument).
pub fn ty_uses_const_param(tys: &impl TyIntern, t: Ty, idx: u32) -> bool {
    let in_const = |c: ConstId| matches!(tys.const_kind(c), ConstKind::Param(p) if p == idx);
    let in_args = |a: ArgsId| {
        tys.args(a).iter().any(|g| match g {
            GenericArg::Ty(e) => ty_uses_const_param(tys, *e, idx),
            GenericArg::Const(c) => in_const(*c),
            GenericArg::Lifetime(_) => false,
        })
    };
    match tys.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) => ty_uses_const_param(tys, e, idx),
        TyKind::Array(e, n) => in_const(n) || ty_uses_const_param(tys, e, idx),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| ty_uses_const_param(tys, e, idx)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => in_args(a),
        _ => false,
    }
}

/// The header rules of one trait impl that are not about its
/// items: `Sized` cannot be implemented, an auto trait needs a
/// local nominal Self type, `unsafe` must match
/// between trait and impl, a `Drop` impl must cover the Adt as
/// written with no extra bounds, and every impl parameter must
/// be constrained by the trait ref (Self or a trait input).
fn check_impl_rules(p: &mut Program, imp: &ast::ImplDef, generics: &Generics, self_pat: Ty, tr: TraitRef, errs: &mut Vec<Diag>) {
    let lang = p.gx.lang;
    if tr.def == lang.sized {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "the `Sized` trait cannot be implemented in user code",
            "Remove the impl; sizedness is automatic.",
        ));
    }
    // An auto trait (`Send`, `Sync`, `Unpin`) can only be implemented
    // for a struct, enum, or union of this file (rustc E0321); std
    // source impls are std's own.
    if lang.is_auto(tr.def) && !p.std_source_span(imp.span) {
        let nominal = p.tys.local_adt(self_pat).is_some_and(|a| !p.is_std_adt(a));
        if !nominal {
            let name = if tr.def == lang.send {
                "Send"
            } else if tr.def == lang.sync {
                "Sync"
            } else {
                "Unpin"
            };
            errs.push(Diag::new(
                "L0110",
                imp.span,
                format!("`{name}` can only be implemented for a struct, enum, or union defined in this file"),
                "Implement it for a local struct, enum, or union, or remove the impl.",
            ));
        }
    }
    let trait_unsafe = p.gx.trait_unsafe.get(&tr.def).copied().unwrap_or(false) || tr.def == lang.send || tr.def == lang.sync;
    if trait_unsafe && !imp.is_unsafe {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "this trait is unsafe, so its impl must be `unsafe impl`",
            "Write `unsafe impl`, after checking the trait's contract holds.",
        ));
    } else if !trait_unsafe && imp.is_unsafe {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "this trait is not unsafe, so its impl cannot be `unsafe impl`",
            "Remove `unsafe` from the impl.",
        ));
    }
    // Every parameter must be constrained by the header: it
    // occurs in the trait ref, or it is the value of an
    // associated type binding in the trait ref or a where
    // clause (`Item = U`). Occurring only in an associated
    // type definition, or only bounded in a where clause, does
    // not constrain it (rustc E0207).
    let mut ref_tys: Vec<Ty> = p.tys.args(tr.args).iter().filter_map(|g| g.as_ty()).collect();
    ref_tys.extend(p.tys.bindings(tr.bindings).iter().filter_map(|(_, g)| g.as_ty()));
    for pred in &generics.predicates {
        match pred {
            Predicate::AssocEq(b) => ref_tys.push(b.value.ty),
            Predicate::Trait(b) => ref_tys.extend(p.tys.bindings(b.value.bindings).iter().filter_map(|(_, g)| g.as_ty())),
            _ => {}
        }
    }
    for (i, param) in generics.params.iter().enumerate() {
        let used = match param.kind {
            ParamKind::Type => ref_tys.iter().any(|&t| ty_uses_param(&p.tys, t, i as u32)),
            ParamKind::Const(_) => ref_tys.iter().any(|&t| ty_uses_const_param(&p.tys, t, i as u32)),
            ParamKind::Lifetime => continue,
        };
        if !used {
            errs.push(Diag::new(
                "L0110",
                param.span,
                format!(
                    "the {} parameter `{}` is not used in the impl header",
                    if matches!(param.kind, ParamKind::Const(_)) { "const" } else { "type" },
                    p.name(param.name)
                ),
                "Use it in the Self type or a trait input, or remove it.",
            ));
        }
    }
    if tr.def == lang.drop {
        check_drop_impl(p, imp, generics, self_pat, errs);
    }
}

/// The `Drop` header rules: the Self type must be the Adt
/// applied to its own parameters in order (no `Drop for
/// G<u8>`), and the impl may not require more bounds than the
/// Adt itself declares (rustc E0366 and E0367).
fn check_drop_impl(p: &Program, imp: &ast::ImplDef, generics: &Generics, self_pat: Ty, errs: &mut Vec<Diag>) {
    let TyKind::Adt(def, args) = p.tys.kind(self_pat) else {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "`Drop` can only be implemented for a struct or enum",
            "Implement `Drop` on the type itself.",
        ));
        return;
    };
    let Some(adt_idx) = p.gx.adt_info.iter().position(|&(d, _)| d == def) else { return };
    let n_params = p.gx.adt_generics[adt_idx].params.len();
    let written: Vec<GenericArg> = p.tys.args(args).to_vec();
    let in_order = written.len() == n_params
        && written.iter().enumerate().all(|(i, g)| match g {
            GenericArg::Ty(t) => matches!(p.tys.kind(*t), TyKind::Param(pid) if pid.0 as usize == i),
            GenericArg::Const(c) => matches!(p.tys.const_kind(*c), ConstKind::Param(cp) if cp as usize == i),
            GenericArg::Lifetime(_) => true,
        });
    if !in_order {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "`Drop` must be implemented for the type with its own parameters, not one instance of it",
            "Write `impl<T> Drop for Type<T>` with the type's own parameter list.",
        ));
        return;
    }
    let adt_preds: Vec<TraitRef> = p.gx.adt_generics[adt_idx]
        .predicates
        .iter()
        .filter_map(|p2| match p2 {
            Predicate::Trait(b) => Some(b.value),
            _ => None,
        })
        .collect();
    for pred in &generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        if b.value.def == p.gx.lang.sized {
            continue;
        }
        if !adt_preds.contains(&b.value) {
            errs.push(Diag::new(
                "L0110",
                imp.span,
                "a `Drop` impl cannot require bounds the type does not declare",
                "Move the bound to the type definition, or remove it from the impl.",
            ));
            return;
        }
    }
}

/// Rewrites projections of this impl's associated types on its Self
/// type `self_ty` to the impl's bindings (in impl parameter space).
/// Used when the solver cannot normalize them because the Self type
/// is still a parameter.
fn rewrite_impl_projections(p: &mut Program, t: Ty, self_ty: Ty, assoc_tys: &[(DefId, Ty)]) -> Ty {
    rewrite_projections_at(p, t, self_ty, assoc_tys, 0)
}

/// The type a trait impl's const `assoc` has by the trait's
/// declaration, in the impl's parameter space: the trait args and the
/// impl's associated type bindings filled in (`const MIN:
/// Self::Primitive` in an impl with `type Primitive = i16;` is `i16`).
/// None when the impl has no record or the type still names a
/// parameter. Collect uses it when the plain resolver cannot read the
/// written type; `finish_trait_impl` checks that the two agree.
pub(crate) fn impl_const_decl_ty(p: &mut Program, impl_def: DefId, assoc: DefId) -> Option<Ty> {
    let (want, _) = p.gx.trait_assoc_consts.get(&assoc).copied()?;
    let (_, rec) = p.gx.index.by_def(impl_def)?;
    let (args, assoc_tys) = (rec.trait_ref.args, rec.assoc_tys.clone());
    let args: Vec<GenericArg> = p.tys.args(args).to_vec();
    let self_ty = args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
    let t = subst(&mut p.tys, want, &args);
    let t = rewrite_impl_projections(p, t, self_ty, &assoc_tys);
    (!p.tys.flags(t).contains_param()).then_some(t)
}

/// `rewrite_impl_projections` at nesting `depth`: a projection on
/// another type (`I::Item` in `type Item = I::Item`) stays, and a
/// binding that names itself stops at a fixed depth instead of looping.
fn rewrite_projections_at(p: &mut Program, t: Ty, self_ty: Ty, assoc_tys: &[(DefId, Ty)], depth: u32) -> Ty {
    if depth > 16 {
        return t;
    }
    let assoc_tys_ref = assoc_tys;
    let rw = |p: &mut Program, e: Ty| rewrite_projections_at(p, e, self_ty, assoc_tys_ref, depth + 1);
    match p.tys.kind(t) {
        TyKind::Projection(assoc, args) => match assoc_tys.iter().find(|(d, _)| *d == assoc.0) {
            Some((_, bound)) if p.tys.args(args).first().and_then(|g| g.as_ty()) == Some(self_ty) => rw(p, *bound),
            _ => t,
        },
        TyKind::Ref(r, m, e) => {
            let e = rw(p, e);
            p.tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::Adt(d, a) => {
            let raw: Vec<GenericArg> = p.tys.args(a).to_vec();
            let out: Vec<GenericArg> = raw
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(rw(p, e)),
                    other => other,
                })
                .collect();
            let a = p.tys.intern_args(&out);
            p.tys.intern(TyKind::Adt(d, a))
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            let out: Vec<Ty> = elems.iter().map(|&e| rw(p, e)).collect();
            let ts = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Slice(e) => {
            let e = rw(p, e);
            p.tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = rw(p, e);
            p.tys.intern(TyKind::Array(e, n))
        }
        _ => t,
    }
}

/// `t` with every projection of this impl's own trait ref (`Self::A`,
/// args equal to `trait_args`) replaced by the impl's binding.
fn rewrite_own_projections(p: &mut Program, t: Ty, trait_args: ArgsId, assoc_tys: &[(DefId, Ty)]) -> Ty {
    if !p.tys.flags(t).contains_projection() {
        return t;
    }
    match p.tys.kind(t) {
        TyKind::Projection(assoc, a) if a == trait_args => match assoc_tys.iter().find(|(d, _)| *d == assoc.0) {
            Some(&(_, bound)) if bound != t => rewrite_own_projections(p, bound, trait_args, assoc_tys),
            _ => t,
        },
        TyKind::Ref(r, m, e) => {
            let e = rewrite_own_projections(p, e, trait_args, assoc_tys);
            p.tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::RawPtr(m, e) => {
            let e = rewrite_own_projections(p, e, trait_args, assoc_tys);
            p.tys.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = rewrite_own_projections(p, e, trait_args, assoc_tys);
            p.tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = rewrite_own_projections(p, e, trait_args, assoc_tys);
            p.tys.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            let out: Vec<Ty> = elems.into_iter().map(|e| rewrite_own_projections(p, e, trait_args, assoc_tys)).collect();
            let ts = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let raw: Vec<GenericArg> = p.tys.args(a).to_vec();
            let out: Vec<GenericArg> = raw
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(rewrite_own_projections(p, e, trait_args, assoc_tys)),
                    other => other,
                })
                .collect();
            let a = p.tys.intern_args(&out);
            p.tys.intern(TyKind::Adt(d, a))
        }
        TyKind::FnPtr(sig) => {
            let b = p.tys.sig(sig);
            let ins: Vec<Ty> = p.tys.tys_of(b.value.inputs).to_vec();
            let ins: Vec<Ty> = ins.into_iter().map(|e| rewrite_own_projections(p, e, trait_args, assoc_tys)).collect();
            let output = rewrite_own_projections(p, b.value.output, trait_args, assoc_tys);
            let inputs = p.tys.intern_tys(&ins);
            let sig = p.tys.intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..b.value } });
            p.tys.intern(TyKind::FnPtr(sig))
        }
        _ => t,
    }
}

/// The provided methods of the lang traits: an impl may leave them
/// out. Every other method in a lang trait record is required.
fn lang_provided(lang: &LangTraits, tr: DefId, name: &str) -> bool {
    match name {
        "ne" => tr == lang.partial_eq,
        "lt" | "le" | "gt" | "ge" => tr == lang.partial_ord,
        "max" | "min" | "clamp" => tr == lang.ord,
        "len" => tr == lang.exact_size_iterator,
        "size_hint" => tr == lang.iterator,
        "clone_into" => tr == lang.to_owned,
        "clone_from" => tr == lang.clone,
        "hash_one" => tr == lang.build_hasher,
        "hash_slice" => tr == lang.hash,
        "contains" => tr == lang.range_bounds,
        n => tr == lang.hasher && n != "finish" && n != "write",
    }
}

/// An impl's method of a lang trait, which has no AST template: a
/// required method must be written (rustc E0046), and a written one
/// must have the trait's signature (E0053, E0050, E0049, E0185,
/// E0186): the lang signature table's, with the trait ref's args and
/// the impl's associated types put in. `hash<H: Hasher>` and
/// `hash_slice<H: Hasher>` take one type parameter, which may have no
/// bound but `Hasher`.
#[allow(clippy::too_many_arguments)]
fn check_lang_method(
    p: &mut Program,
    imp: &ast::ImplDef,
    tr: TraitRef,
    method_def: DefId,
    name: Sym,
    found: Option<LocalDefId>,
    impl_parent_n: usize,
    assoc_tys: &[(DefId, Ty)],
    span: Span,
    errs: &mut Vec<Diag>,
) {
    use crate::traits::solve::{PureCx, Solver, normalize};
    use ast::SelfKind::{Ref, RefMut};
    let lang = p.gx.lang;
    let n = p.name(name).to_string();
    let Some(local) = found else {
        if !lang_provided(&lang, tr.def, &n) {
            errs.push(Diag::new("L0110", span, format!("the impl is missing the trait method `{n}`"), "Add the method to the impl."));
        }
        return;
    };
    let p0 = p.tys.intern(TyKind::Param(ParamId(0)));
    let own: Vec<ParamDef> = p
        .gx
        .fn_templates
        .get(local.0 as usize)
        .cloned()
        .flatten()
        .map_or(Vec::new(), |t| t.generics.params.into_iter().skip(impl_parent_n).collect());
    let own_tys: Vec<&ParamDef> = own.iter().filter(|g| !matches!(g.kind, ParamKind::Lifetime)).collect();
    let is_hash = tr.def == lang.hash && (n == "hash" || n == "hash_slice");
    // `fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T)` takes
    // one type parameter like `hash`.
    let is_extend = tr.def == lang.extend && n == "extend";
    // `hash`'s H: in the signature, the parameter after the trait's
    // (Self); in the impl method, its first own type parameter.
    let trait_n = p.tys.args(tr.args).len() as u32;
    let h_impl = own.iter().position(|g| !matches!(g.kind, ParamKind::Lifetime)).map(|i| p.tys.intern(TyKind::Param(ParamId(impl_parent_n as u32 + i as u32))));
    let sig = match p.gx.lang_method_sigs.get(&method_def) {
        Some(s) => s.clone(),
        None if tr.def == lang.drop && n == "drop" => {
            let m0 = p.tys.mk_ref(true, p0);
            LangMethodSig { self_kind: Some(RefMut), params: vec![m0], ret: UNIT, ret_borrows_from: None }
        }
        None if tr.def == lang.iterator && n == "size_hint" => {
            let r0 = p.tys.mk_ref(false, p0);
            let hi = p.tys.mk_option(USIZE);
            let ts = p.tys.intern_tys(&[USIZE, hi]);
            let ret = p.tys.intern(TyKind::Tuple(ts));
            LangMethodSig { self_kind: Some(Ref), params: vec![r0], ret, ret_borrows_from: None }
        }
        // `fn hash<H: Hasher>(&self, state: &mut H)`: H is the method's
        // first own parameter, after the impl's.
        // `fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)`.
        None if is_hash && own_tys.len() == 1 && matches!(own_tys[0].kind, ParamKind::Type) => {
            let h = p.tys.intern(TyKind::Param(ParamId(trait_n)));
            let mh = p.tys.mk_ref(true, h);
            if n == "hash" {
                let r0 = p.tys.mk_ref(false, p0);
                LangMethodSig { self_kind: Some(Ref), params: vec![r0, mh], ret: UNIT, ret_borrows_from: None }
            } else {
                let sl = p.tys.intern(TyKind::Slice(p0));
                let data = p.tys.mk_ref(false, sl);
                LangMethodSig { self_kind: None, params: vec![data, mh], ret: UNIT, ret_borrows_from: None }
            }
        }
        None if is_extend && own_tys.len() == 1 && matches!(own_tys[0].kind, ParamKind::Type) => {
            let m0 = p.tys.mk_ref(true, p0);
            let t = p.tys.intern(TyKind::Param(ParamId(trait_n)));
            LangMethodSig { self_kind: Some(RefMut), params: vec![m0, t], ret: UNIT, ret_borrows_from: None }
        }
        None if is_hash || is_extend => {
            let f_name_span = p.fn_def(local).name_span;
            errs.push(Diag::new(
                "L0110",
                f_name_span,
                "method has a different number of generic parameters than the trait method",
                if n == "hash_slice" {
                    "Write `fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)`."
                } else if is_hash {
                    "Write `fn hash<H: Hasher>(&self, state: &mut H)`."
                } else {
                    "Write `fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T)`."
                },
            ));
            return;
        }
        // No signature known for this method (`from_iter`, `call`): not
        // checked here.
        None => return,
    };
    let (f_self_kind, f_name_span, got_params, got_ret) = {
        let f = p.fn_info(local);
        (f.self_kind, f.def(&p.ast).name_span, f.params.clone(), f.ret)
    };
    let fix = "Match the signature of the std trait method.";
    // `self` forms must match; a typed `self: T` compares by type below.
    let typed = matches!(f_self_kind, Some(ast::SelfKind::Typed));
    if f_self_kind.is_some() != sig.self_kind.is_some() || (!typed && f_self_kind != sig.self_kind) {
        errs.push(Diag::new("L0110", f_name_span, "method receiver does not match the trait method", fix));
        return;
    }
    if got_params.len() != sig.params.len() {
        errs.push(Diag::new("L0110", f_name_span, "method takes a different number of parameters than the trait method", fix));
        return;
    }
    if own_tys.len() != usize::from(is_hash || is_extend) {
        errs.push(Diag::new("L0110", f_name_span, "method has a different number of generic parameters than the trait method", fix));
        return;
    }
    if (is_hash || is_extend) && let Some(h) = h_impl {
        // A stricter bound on the parameter than the trait's (E0276):
        // `H: Hasher`, or `T: IntoIterator<Item = A>`.
        let preds = p.gx.fn_templates.get(local.0 as usize).cloned().flatten().map_or(Vec::new(), |t| t.generics.predicates);
        let a = p.tys.args(tr.args).get(1).and_then(|g| g.as_ty());
        let allowed = if is_hash { lang.hasher } else { lang.into_iterator };
        let extra = preds.iter().any(|pred| match pred {
            Predicate::Trait(b) => {
                let on_h = p.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(h);
                // `T: IntoIterator<Item = X>` with X not the trait's A.
                let other_item = p.tys.bindings(b.value.bindings).iter().any(|&(d, g)| d != lang.assoc_into_item || g.as_ty() != a);
                on_h && (b.count != 0 || (b.value.def != allowed && b.value.def != lang.sized) || other_item)
            }
            Predicate::AssocEq(b) => {
                let on_h = p.tys.args(b.value.trait_args).first().and_then(|g| g.as_ty()) == Some(h);
                on_h && (b.value.assoc != lang.assoc_into_item || Some(b.value.ty) != a)
            }
            _ => false,
        });
        if extra {
            errs.push(Diag::new("L0110", f_name_span, "this method requires more of its generic parameters than the trait method does", fix));
            return;
        }
    }
    let mut args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
    let self_raw = args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
    // rustc's object lifetime defaults: a `dyn` written with no bound is
    // `'static` in the impl's Self type, an associated type or a trait
    // argument, and takes the lifetime of a reference right above it.
    // Erased signatures keep only a written `'static`, so each side
    // gets its object lifetimes back from what it wrote (`canon_dyn`):
    // `impl Deref` with `Target = dyn Tr` must return `&(dyn Tr +
    // 'static)`, not `&dyn Tr`; `Borrow<dyn K + 'a>` returns `&(dyn K
    // + 'a)`.
    let mut anon = u32::MAX;
    let self_ty = canon_dyn(p, Some(imp.self_ty), self_raw, None, true, self_raw, None, &mut anon);
    let sc = Some(self_ty);
    let written: Vec<ast::TyId> = match imp.trait_ref.as_ref().and_then(|t| t.path.last()).map(|s| &s.args) {
        Some(GenericArgs::Angle(xs)) => xs.iter().filter_map(|g| if let AstArg::Type(t) = g { Some(*t) } else { None }).collect(),
        _ => Vec::new(),
    };
    for (i, g) in args.iter_mut().enumerate() {
        if let GenericArg::Ty(t) = *g {
            // An omitted arg is its default (`Rhs = Self`): Self's form.
            *g = GenericArg::Ty(match i {
                0 => self_ty,
                _ => canon_dyn(p, written.get(i - 1).copied(), t, None, true, self_raw, sc, &mut anon),
            });
        }
    }
    let trec = p.gx.index.trait_record(tr.def).cloned();
    let assoc_tys: Vec<(DefId, Ty)> = assoc_tys
        .iter()
        .map(|&(d, t)| {
            let a = imp.types.iter().find(|at| trec.as_ref().and_then(|r| r.assoc_by_name(at.name)) == Some(d)).and_then(|at| at.default);
            (d, canon_dyn(p, a, t, None, true, self_raw, sc, &mut anon))
        })
        .collect();
    let (param_asts, ret_ast) = {
        let def = p.fn_info(local).def(&p.ast);
        let mut v: Vec<Option<ast::TyId>> = Vec::new();
        if let Some(sp) = &def.self_param {
            v.push(sp.ty);
        }
        v.extend(def.params.iter().map(|x| Some(x.ty)));
        (v, def.ret)
    };
    let got_params: Vec<Ty> =
        got_params.iter().enumerate().map(|(i, &t)| canon_dyn(p, param_asts.get(i).copied().flatten(), t, None, false, self_raw, sc, &mut anon)).collect();
    let got_ret = canon_dyn(p, ret_ast, got_ret, None, false, self_raw, sc, &mut anon);
    if (is_hash || is_extend) && let Some(h) = h_impl {
        args.push(GenericArg::Ty(h));
    }
    let want_params: Vec<Ty> = sig
        .params
        .iter()
        .map(|&t| {
            let t = subst(&mut p.tys, t, &args);
            rewrite_impl_projections(p, t, self_ty, &assoc_tys)
        })
        .collect();
    let want_ret = {
        let t = subst(&mut p.tys, sig.ret, &args);
        rewrite_impl_projections(p, t, self_ty, &assoc_tys)
    };
    // The method's own bounds (the impl's included) are the env: a
    // supertrait's `Self::Item` may be fixed only through one
    // (`impl<A, F: FnOnce() -> A> DoubleEndedIterator for OnceWith<F>`).
    let preds = p.gx.fn_templates.get(local.0 as usize).cloned().flatten().map_or(Vec::new(), |t| t.generics.predicates);
    let env = crate::traits::solve::elaborate_in(&mut p.tys, &p.gx.index, &preds);
    let mut cx = PureCx::new(&p.tys);
    let mut solver = Solver::new();
    let mut norm = |t: Ty| normalize(&mut solver, &mut cx, &p.gx.index, &env, t);
    // An elided param lifetime is free (late-bound) unless the return
    // can borrow from it: no `self` and a reference in the return.
    let free_params = f_self_kind.is_some() || !mentions_ref(&p.tys, got_ret);
    let boxed = p.tys.builtins().boxed;
    let pairs: Vec<(Ty, Ty)> = want_params.iter().zip(&got_params).map(|(&w, &g)| (norm(w), norm(g))).collect();
    let ret_pair = (norm(want_ret), norm(got_ret));
    let same = pairs.iter().all(|&(w, g)| dyn_sub_ok(&p.tys, w, g, false, true, free_params, boxed))
        && dyn_sub_ok(&p.tys, ret_pair.0, ret_pair.1, true, true, false, boxed);
    if !same {
        errs.push(Diag::new("L0110", f_name_span, format!("method `{n}` has an incompatible type for the trait"), fix));
    } else if elided_ret_takes_self_lifetime(p, local, sig.ret) {
        errs.push(elided_ret_diag(f_name_span));
    } else if input_fixes_method_lifetime(p, local, None, &sig.params) {
        errs.push(fixed_input_diag(f_name_span));
    }
}

/// rustc's impl method lifetime check for one common shape (`impl`
/// item signature doesn't match `trait` item signature, E0803,
/// E0491): a return type that elides a lifetime takes the lifetime of
/// the `&self` receiver, which is the method's own. Where the trait's
/// return type has a type from the impl header (`T`, `Self`,
/// `Self::Item`), the references in it carry the impl's lifetimes,
/// never the method's, so an elided one there differs from the trait
/// (`impl AsRef<&L> for Box<L> { fn as_ref(&self) -> &&L }`, or
/// `type Item = &'a u8; fn next(&mut self) -> Option<&u8>`). `want`
/// is the trait method's return type before substitution. A receiver
/// with a written lifetime, or an elision source other than `&self`,
/// is not judged here.
fn elided_ret_takes_self_lifetime(p: &Program, local: LocalDefId, want: Ty) -> bool {
    let def = p.fn_def(local);
    let Some(sp) = &def.self_param else { return false };
    if !matches!(sp.kind, ast::SelfKind::Ref | ast::SelfKind::RefMut) || sp.lifetime.is_some() {
        return false;
    }
    def.ret.is_some_and(|ret| header_part_elides(p, want, ret))
}

/// Walks the trait's return type `want` along the impl's written
/// return type `got`: true when a part that comes from the impl
/// header is written with an elided lifetime.
fn header_part_elides(p: &Program, want: Ty, got: ast::TyId) -> bool {
    match (p.tys.kind(want), p.ast.ty(got)) {
        (TyKind::Param(_) | TyKind::Projection(..), _) => writes_elided_lifetime(p, got),
        (TyKind::Ref(_, _, w), TyExpr::Ref { inner, .. }) => header_part_elides(p, w, *inner),
        (TyKind::Array(w, _), TyExpr::Array { inner, .. }) | (TyKind::Slice(w), TyExpr::Slice(inner)) => header_part_elides(p, w, *inner),
        (TyKind::Tuple(ws), TyExpr::Tuple(gs)) => {
            let ws = p.tys.tys_of(ws);
            ws.len() == gs.len() && ws.iter().zip(gs).any(|(&w, &g)| header_part_elides(p, w, g))
        }
        (TyKind::Adt(_, a), TyExpr::Path(segs)) => {
            let ws: Vec<Ty> = p.tys.args(a).iter().filter_map(|g| g.as_ty()).collect();
            let gs = segs.last().map_or(Vec::new(), |s| s.type_args());
            ws.len() == gs.len() && ws.iter().zip(&gs).any(|(&w, &g)| header_part_elides(p, w, g))
        }
        _ => false,
    }
}

/// True when the written type has a reference or path lifetime that
/// is elided or `'_` (fn pointer and trait object types bind their
/// own).
fn writes_elided_lifetime(p: &Program, t: ast::TyId) -> bool {
    let anon = |l: &ast::Lifetime| matches!(p.name(l.name), "'_" | "_");
    match p.ast.ty(t) {
        TyExpr::Ref { lifetime, inner, .. } => lifetime.as_ref().is_none_or(anon) || writes_elided_lifetime(p, *inner),
        TyExpr::Tuple(ts) => ts.iter().any(|&x| writes_elided_lifetime(p, x)),
        TyExpr::Array { inner, .. } | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } => writes_elided_lifetime(p, *inner),
        TyExpr::Path(segs) => segs.iter().any(|s| match &s.args {
            ast::GenericArgs::Angle(args) => args.iter().any(|a| match a {
                ast::GenericArg::Type(x) => writes_elided_lifetime(p, *x),
                ast::GenericArg::Lifetime(l) => anon(l),
                _ => false,
            }),
            _ => false,
        }),
        _ => false,
    }
}

/// The other half of that check, for inputs: an impl method must take
/// every input the trait method takes, so where the trait's reference
/// has a lifetime of the method (elided, `'_`, or the method's own
/// parameter), the impl may not fix it to one of the impl's lifetimes
/// or `'static` (`impl<'a> AsRef<u8> for W<'a> { fn as_ref(&'a self)
/// -> &u8 }`, rustc E0308 "method not compatible with trait"). User
/// traits compare the trait method as written (`trait_fn`); a lang
/// trait's table (`want`, the receiver first) has method lifetimes only.
fn input_fixes_method_lifetime(p: &Program, local: LocalDefId, trait_fn: Option<&ast::FnDef>, want: &[Ty]) -> bool {
    let def = p.fn_def(local);
    let lts = |g: &ast::Generics| -> Vec<Sym> {
        g.params
            .iter()
            .filter_map(|g| match g {
                ast::GenericParam::Lifetime { lt, .. } => Some(lt.name),
                _ => None,
            })
            .collect()
    };
    let anon = |l: &ast::Lifetime| matches!(p.name(l.name), "'_" | "_");
    let own = lts(&def.generics);
    let fixed = |l: &ast::Lifetime| !anon(l) && !own.contains(&l.name);
    let trait_own = trait_fn.map_or(Vec::new(), |f| lts(&f.generics));
    let method_lt = |l: &Option<ast::Lifetime>| l.as_ref().is_none_or(|l| anon(l) || trait_own.contains(&l.name));
    if let Some(sp) = &def.self_param
        && matches!(sp.kind, ast::SelfKind::Ref | ast::SelfKind::RefMut)
        && sp.lifetime.as_ref().is_some_and(fixed)
    {
        let trait_recv_method = match trait_fn {
            Some(f) => f.self_param.as_ref().is_some_and(|t| matches!(t.kind, ast::SelfKind::Ref | ast::SelfKind::RefMut) && method_lt(&t.lifetime)),
            None => want.first().is_some_and(|&w| matches!(p.tys.kind(w), TyKind::Ref(..))),
        };
        if trait_recv_method {
            return true;
        }
    }
    match trait_fn {
        Some(f) => def.params.iter().zip(&f.params).any(|(i, t)| ast_fixes_method_lt(p, t.ty, i.ty, &method_lt, &fixed)),
        None => {
            let rest = if def.self_param.is_some() { want.get(1..).unwrap_or(&[]) } else { want };
            def.params.iter().zip(rest).any(|(prm, &w)| ty_fixes_method_lt(p, w, prm.ty, &fixed))
        }
    }
}

/// `input_fixes_method_lifetime` over a user trait's written type `want`.
fn ast_fixes_method_lt(
    p: &Program,
    want: ast::TyId,
    got: ast::TyId,
    method_lt: &dyn Fn(&Option<ast::Lifetime>) -> bool,
    fixed: &dyn Fn(&ast::Lifetime) -> bool,
) -> bool {
    let rec = |w: ast::TyId, g: ast::TyId| ast_fixes_method_lt(p, w, g, method_lt, fixed);
    match (p.ast.ty(want), p.ast.ty(got)) {
        (TyExpr::Ref { lifetime: wl, inner: wi, .. }, TyExpr::Ref { lifetime: gl, inner: gi, .. }) => {
            (method_lt(wl) && gl.as_ref().is_some_and(fixed)) || rec(*wi, *gi)
        }
        (TyExpr::Array { inner: w, .. }, TyExpr::Array { inner: g, .. }) | (TyExpr::Slice(w), TyExpr::Slice(g)) => rec(*w, *g),
        (TyExpr::Tuple(ws), TyExpr::Tuple(gs)) => ws.len() == gs.len() && ws.iter().zip(gs).any(|(&w, &g)| rec(w, g)),
        (TyExpr::Path(ws), TyExpr::Path(gs)) => {
            let (wa, ga) = (ws.last().map_or(Vec::new(), |s| s.type_args()), gs.last().map_or(Vec::new(), |s| s.type_args()));
            wa.len() == ga.len() && wa.iter().zip(&ga).any(|(&w, &g)| rec(w, g))
        }
        _ => false,
    }
}

/// `input_fixes_method_lifetime` over a lang trait's table type `want`:
/// its references are the method's own; a parameter is the impl's.
fn ty_fixes_method_lt(p: &Program, want: Ty, got: ast::TyId, fixed: &dyn Fn(&ast::Lifetime) -> bool) -> bool {
    match (p.tys.kind(want), p.ast.ty(got)) {
        (TyKind::Ref(_, _, w), TyExpr::Ref { lifetime, inner, .. }) => lifetime.as_ref().is_some_and(fixed) || ty_fixes_method_lt(p, w, *inner, fixed),
        (TyKind::Array(w, _), TyExpr::Array { inner, .. }) | (TyKind::Slice(w), TyExpr::Slice(inner)) => ty_fixes_method_lt(p, w, *inner, fixed),
        (TyKind::Tuple(ws), TyExpr::Tuple(gs)) => {
            let ws = p.tys.tys_of(ws);
            ws.len() == gs.len() && ws.iter().zip(gs).any(|(&w, &g)| ty_fixes_method_lt(p, w, g, fixed))
        }
        (TyKind::Adt(_, a), TyExpr::Path(segs)) => {
            let ws: Vec<Ty> = p.tys.args(a).iter().filter_map(|g| g.as_ty()).collect();
            let gs = segs.last().map_or(Vec::new(), |s| s.type_args());
            ws.len() == gs.len() && ws.iter().zip(&gs).any(|(&w, &g)| ty_fixes_method_lt(p, w, g, fixed))
        }
        _ => false,
    }
}

fn fixed_input_diag(span: Span) -> Diag {
    Diag::new(
        "L0734",
        span,
        "method signature does not match the trait method: an input lifetime is fixed where the trait takes any",
        "Leave the lifetime elided (`&self`), as the trait method does.",
    )
}

fn elided_ret_diag(span: Span) -> Diag {
    Diag::new(
        "L0734",
        span,
        "method signature does not match the trait method: the elided lifetime in its return type is the `&self` lifetime, not the impl's",
        "Write the impl's lifetime in the return type (`impl<'a> .. { fn f(&self) -> &&'a T }`), as the trait's signature has it.",
    )
}

/// Checks one impl method signature against its trait method
/// template: substitute the trait template with the impl's trait
/// ref, normalize both sides (associated types through this
/// impl), and compare.
fn validate_method_sig(
    p: &mut Program,
    tmpl: &TraitMethodTemplate,
    local: LocalDefId,
    tr: TraitRef,
    impl_parent_n: usize,
    impl_preds: &[Predicate],
    assoc_tys: &[(DefId, Ty)],
    span: Span,
    errs: &mut Vec<Diag>,
) {
    use crate::traits::solve::{PureCx, Solver, normalize};
    let (f_self_kind, f_params_len, f_name_span) = {
        let f = p.fn_info(local);
        (f.self_kind, f.params.len(), f.def(&p.ast).name_span)
    };
    if f_self_kind != tmpl.self_kind {
        // Typed receivers compare by their resolved type below;
        // plain forms must match here.
        if !(matches!(f_self_kind, Some(ast::SelfKind::Typed)) || matches!(tmpl.self_kind, Some(ast::SelfKind::Typed))) {
            errs.push(Diag::new(
                "L0110",
                f_name_span,
                "method receiver does not match the trait method",
                "Match the receiver form in the trait definition.",
            ));
            return;
        }
    }
    if f_params_len != tmpl.params.len() {
        errs.push(Diag::new(
            "L0110",
            f_name_span,
            "method takes a different number of parameters than the trait method",
            "Match the signature in the trait definition.",
        ));
        return;
    }
    // The method's own generics must line up with the trait's:
    // the same number and kinds (rustc E0049), no `impl Trait`
    // written for a generic parameter or the reverse (E0643),
    // and no requirement on them the trait does not imply
    // (E0276: a looser impl is fine, a stricter one is not).
    let trait_n = p.gx.index.trait_record(tr.def).map_or(0, |r| r.generics.params.len());
    let own_trait = tmpl.generics.params.len().saturating_sub(trait_n);
    let impl_gen: Option<Generics> = p.gx.fn_templates.get(local.0 as usize).cloned().flatten().map(|t| t.generics);
    let own_impl = impl_gen.as_ref().map_or(0, |g| g.params.len().saturating_sub(impl_parent_n));
    let kind_class = |k: &ParamKind| match k {
        ParamKind::Type => 0,
        ParamKind::Const(_) => 1,
        ParamKind::Lifetime => 2,
    };
    let kinds_match = own_impl == own_trait
        && impl_gen.as_ref().is_none_or(|g| {
            (0..own_trait).all(|j| kind_class(&g.params[impl_parent_n + j].kind) == kind_class(&tmpl.generics.params[trait_n + j].kind))
        });
    if !kinds_match {
        errs.push(Diag::new(
            "L0110",
            f_name_span,
            "method has a different number of generic parameters than the trait method",
            "Match the generic parameters in the trait definition.",
        ));
        return;
    }
    {
        let idef = p.fn_def(local);
        for (ip, tp) in idef.params.iter().zip(tmpl.def(&p.ast).params.iter()) {
            let i_impl = matches!(p.ast.ty(ip.ty), TyExpr::ImplTrait { .. });
            let t_impl = matches!(p.ast.ty(tp.ty), TyExpr::ImplTrait { .. });
            if i_impl != t_impl {
                errs.push(Diag::new(
                    "L0110",
                    f_name_span,
                    "method writes `impl Trait` where the trait writes a generic parameter (or the reverse)",
                    "Match the parameter form in the trait definition.",
                ));
                return;
            }
        }
    }
    // Substitution for the trait template: trait params from the
    // impl's trait ref, method params onto the impl's own.
    let mut subst_args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
    let own = own_trait;
    for j in 0..own {
        let t = p.tys.intern(TyKind::Param(ParamId((impl_parent_n + j) as u32)));
        subst_args.push(GenericArg::Ty(t));
    }
    if let Some(ig) = &impl_gen {
        use crate::traits::index::subst_predicate;
        // Every requirement of the impl method must follow from
        // what a caller of the trait method knows: the trait
        // method's own predicates (substituted) and the impl
        // header's. A stricter impl method (rustc E0276) can be
        // called through the trait without its extra bound, on
        // the method's own params (`U: Copy`) or the impl's
        // (`where T: Copy`, `Vec<T>: Clone`, `Self: Copy`).
        let mut env_subst: Vec<Predicate> = tmpl.generics.predicates.iter().map(|&pr| subst_predicate(&mut p.tys, pr, &subst_args)).collect();
        env_subst.extend_from_slice(impl_preds);
        let env = elaborate_env(&mut p.tys, &p.gx.index, &env_subst);
        let header_self = subst_args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
        for pred in &ig.predicates {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || b.value.def == p.gx.lang.sized {
                continue;
            }
            let raw_args: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            let goal_args: Vec<GenericArg> = raw_args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(rewrite_impl_projections(p, t, header_self, assoc_tys)),
                    other => other,
                })
                .collect();
            let goal = TraitRef { def: b.value.def, args: p.tys.intern_args(&goal_args), bindings: b.value.bindings };
            // A bound over concrete types only (`where i64: Default`)
            // holds or fails for every caller alike, so it needs no
            // implication from the trait. `check_wf_item` proves it
            // later, when the solver has the std scalar impls (here,
            // in collect, the derive family's scalar impls are not
            // there yet), and rejects one that does not hold
            // (`where String: Copy`, L0612).
            let concrete = goal_args.iter().all(|g| match g {
                GenericArg::Ty(t) => !p.tys.flags(*t).contains_param() && !p.tys.flags(*t).contains_infer(),
                _ => true,
            });
            if concrete {
                continue;
            }
            if !prove_goal(p, &env, goal) && !prove_goal(p, &[], goal) {
                let gname = p.gx.index.trait_record(goal.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
                errs.push(Diag::new(
                    "L0110",
                    f_name_span,
                    format!("impl has stricter requirements than the trait method: the `{gname}` bound here is not implied by the trait"),
                    "Remove the extra bound, or add it to the trait definition.",
                ));
                break;
            }
        }
    }
    let self_ty = subst_args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
    // Object lifetime defaults where each type was written, as in
    // `check_lang_method` (`type Out = dyn Tr` with `fn get(&self) ->
    // &Self::Out` needs `&(dyn Tr + 'static)` in the impl).
    let assoc_tys: Vec<(DefId, Ty)> = assoc_tys.iter().map(|&(d, t)| (d, obj_default(&mut p.tys, t, false))).collect();
    let subst_args: Vec<GenericArg> = subst_args
        .iter()
        .enumerate()
        .map(|(i, &g)| match g {
            GenericArg::Ty(t) if i > 0 => GenericArg::Ty(obj_default(&mut p.tys, t, false)),
            x => x,
        })
        .collect();
    let want_params: Vec<Ty> = tmpl
        .params
        .iter()
        .map(|&t| {
            let t = obj_default(&mut p.tys, t, false);
            let t = subst(&mut p.tys, t, &subst_args);
            rewrite_impl_projections(p, t, self_ty, &assoc_tys)
        })
        .collect();
    let want_ret = {
        let t = obj_default(&mut p.tys, tmpl.ret, false);
        let t = subst(&mut p.tys, t, &subst_args);
        rewrite_impl_projections(p, t, self_ty, &assoc_tys)
    };
    let got_params: Vec<Ty> = p.fn_info(local).params.clone().into_iter().map(|t| obj_default(&mut p.tys, t, false)).collect();
    let got_ret = p.fn_info(local).ret;
    let got_ret = obj_default(&mut p.tys, got_ret, false);
    let mut cx = PureCx::new(&p.tys);
    let mut solver = Solver::new();
    let same = want_params.len() == got_params.len()
        && want_params
            .iter()
            .zip(&got_params)
            .all(|(&w, &g)| normalize(&mut solver, &mut cx, &p.gx.index, &[], w) == normalize(&mut solver, &mut cx, &p.gx.index, &[], g))
        && normalize(&mut solver, &mut cx, &p.gx.index, &[], want_ret) == normalize(&mut solver, &mut cx, &p.gx.index, &[], got_ret);
    if !same {
        errs.push(Diag::new(
            "L0110",
            f_name_span,
            "method signature does not match the trait method",
            "Match the parameter and return types in the trait definition, after associated types are substituted.",
        ));
    } else if elided_ret_takes_self_lifetime(p, local, tmpl.ret) {
        errs.push(elided_ret_diag(f_name_span));
    } else if input_fixes_method_lifetime(p, local, Some(tmpl.def(&p.ast)), &tmpl.params) {
        errs.push(fixed_input_diag(f_name_span));
    }
    let _ = span;
}

/// The derived impl record of trait `k` (in `Derives` flag order: Clone,
/// Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default) for the
/// Adt template row `a`, with a bound per type parameter and per `T::Item`
/// field part (`Field::derive_bounds`), as rustc writes
/// them. `add_synthetic_impls` makes every derive's record with it; a
/// derive delta makes the record of a trait the Adt never derived before
/// with it too (check/derive_delta.rs), so both get the same record.
pub(crate) fn insert_derived(p: &mut Program, a: usize, k: usize, ordinal: &mut u32) -> Option<crate::traits::ImplId> {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let traits = [lang.clone, lang.copy, lang.debug, lang.partial_eq, lang.eq, lang.hash, lang.partial_ord, lang.ord, lang.default];
    let names = ["Clone", "Copy", "Debug", "PartialEq", "Eq", "Hash", "PartialOrd", "Ord", "Default"];
    let (trait_def, dname) = (traits[k], p.interner.intern(names[k]));
    let adt = AdtId(a as u32);
    let (def, n_params) = p.gx.adt_info[a];
    let is_enum = p.adt(adt).is_enum;
    // A const parameter is a const arg (`ArrayStr<N>`), as in
    // written impl headers; the others are type args.
    let param_args: Vec<GenericArg> = (0..n_params as u32)
        .map(|i| match p.gx.adt_generics[a].params.get(i as usize).map(|prm| prm.kind) {
            Some(ParamKind::Const(_)) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i))),
            _ => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i)))),
        })
        .collect();
    let self_pat = p.tys.mk_adt(def, &param_args);
    let with_rhs = trait_def == lang.partial_eq || trait_def == lang.partial_ord;
    let rest: Vec<Ty> = if with_rhs { vec![self_pat] } else { Vec::new() };
    let mut preds: Vec<Predicate> = Vec::new();
    // rustc bounds every type parameter by the derived trait,
    // except `Default` on an enum: its default variant is a
    // unit variant, so that impl has no bounds at all.
    // Std's `PhantomData<T>` impls have no bounds (std source,
    // W-STD-C).
    let bounded = !(trait_def == lang.default && is_enum) && !p.is_phantom_adt(adt);
    // Then each field part written as a path from a type param
    // (`T::Item`: `Field::derive_bounds`), as rustc's derive bounds it.
    let mut on: Vec<Ty> = Vec::new();
    for (i, param) in p.gx.adt_generics[a].params.iter().enumerate() {
        if bounded && param.kind == ParamKind::Type {
            on.push(p.tys.intern(TyKind::Param(ParamId(i as u32))));
        }
    }
    if bounded {
        for f in p.adts[a].variants.iter().flat_map(|v| v.fields.iter()) {
            for &b in &f.derive_bounds {
                if !on.contains(&b) {
                    on.push(b);
                }
            }
        }
    }
    for t in on {
        let mut tr_args = vec![GenericArg::Ty(t)];
        if with_rhs {
            tr_args.push(GenericArg::Ty(t));
        }
        let args = p.tys.intern_args(&tr_args);
        preds.push(Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS })));
    }
    let generics = Generics { parent: None, params: p.gx.adt_generics[a].params.clone(), predicates: preds };
    insert_synthetic(p, ordinal, trait_def, self_pat, &rest, generics, Vec::new(), Synthetic::Derive(dname, 1 << k), true, Span::default())
}

/// Derives and lang facts as synthetic impls (sections 2.2 and
/// 2.6), inserted after every written impl so coherence sees one
/// impl set. Bodies stay in the builtin derive paths until
/// source std replaces them; these records carry selection and
/// coherence only.
pub fn add_synthetic_impls(p: &mut Program) {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let mut ordinal = 0u32;
    let span = Span::default();
    // The lang facts alone are about 1300 records (the shift operators
    // take every int on the right), plus up to 9 derives per Adt.
    p.gx.index.reserve(1400 + 9 * p.gx.adt_info.len());
    // Derives: one record per (Adt template, derived trait).
    for a in 0..p.gx.adt_info.len() {
        let derives = p.derives_of(AdtId(a as u32));
        let on = [derives.clone, derives.copy, derives.debug, derives.partial_eq, derives.eq, derives.hash, derives.partial_ord, derives.ord, derives.default];
        for k in (0..9).filter(|&k| on[k]) {
            insert_derived(p, a, k, &mut ordinal);
        }
    }
    // Lang facts for builtin types.
    let g0 = Generics::default();
    // core's `impl<I: Iterator + ?Sized> Iterator for &mut I` (Item =
    // I::Item), and its DoubleEndedIterator and ExactSizeIterator twins:
    // `total(&mut it)`, `for x in &mut it` (lowered as a `ByNext` over the
    // reference, lower/iter.rs `by_mut_builtin`).
    {
        let i0 = p.tys.intern(TyKind::Param(ParamId(0)));
        let one_i = Generics { parent: None, params: vec![ParamDef { name: p.interner.intern("I"), kind: ParamKind::Type, span }], predicates: Vec::new() };
        let ia = p.tys.intern_args(&[GenericArg::Ty(i0)]);
        let self_pat = p.tys.intern(TyKind::Ref(Region::Erased, Mut::Mut, i0));
        let item = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_item), ia));
        for tr in [lang.iterator, lang.double_ended_iterator, lang.exact_size_iterator] {
            let pred = Predicate::Trait(Binder::plain(TraitRef { def: tr, args: ia, bindings: EMPTY_BINDINGS }));
            let assoc = if tr == lang.iterator { vec![(lang.assoc_item, item)] } else { Vec::new() };
            let g = Generics { predicates: vec![pred], ..one_i.clone() };
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[], g, assoc, Synthetic::Lang, false, span);
        }
    }
    // core's `impl<A, F: Fn<A> + ?Sized> Fn<A> for &F` (and `FnMut`,
    // `FnOnce`) and `impl<A, F: FnMut<A> + ?Sized> FnMut<A> for &mut F`
    // (and `FnOnce`), with `Output = <F as FnOnce<A>>::Output`: a generic
    // callable passed on by reference (`walk(node, &mut callback)`).
    // Closures, fn items and fn pointers behind a reference are answered
    // structurally first (`closure_select_impl`).
    if let Some(out) = lang.output_of(lang.fn_once) {
        let a = p.tys.intern(TyKind::Param(ParamId(0)));
        let f = p.tys.intern(TyKind::Param(ParamId(1)));
        let params = vec![
            ParamDef { name: p.interner.intern("Args"), kind: ParamKind::Type, span },
            ParamDef { name: p.interner.intern("F"), kind: ParamKind::Type, span },
        ];
        let fa = p.tys.intern_args(&[GenericArg::Ty(f), GenericArg::Ty(a)]);
        let output = p.tys.intern(TyKind::Projection(AssocId(out), fa));
        for (m, base, traits) in [(Mut::Shared, lang.fn_, [lang.fn_, lang.fn_mut, lang.fn_once].as_slice()), (Mut::Mut, lang.fn_mut, [lang.fn_mut, lang.fn_once].as_slice())] {
            let self_pat = p.tys.intern(TyKind::Ref(Region::Erased, m, f));
            let pred = Predicate::Trait(Binder::plain(TraitRef { def: base, args: fa, bindings: EMPTY_BINDINGS }));
            let generics = Generics { parent: None, params: params.clone(), predicates: vec![pred] };
            for &tr in traits {
                let assoc = if tr == lang.fn_once { vec![(out, output)] } else { Vec::new() };
                insert_synthetic(p, &mut ordinal, tr, self_pat, &[a], generics.clone(), assoc, Synthetic::Lang, false, span);
            }
        }
    }
    let scalar_traits = [lang.copy, lang.clone, lang.debug, lang.eq, lang.hash, lang.default];
    let mut scalars: Vec<Ty> = IntTy::ALL_SUPPORTED.iter().map(|&i| int(i)).collect();
    scalars.extend([BOOL, CHAR, UNIT]);
    // Operator traits on scalars, exactly core's impl sets (the
    // operations themselves stay on the builtin scalar path; these
    // records answer selection and associated-type normalization,
    // so an over-broad set would prove bounds rustc rejects).
    // Ints have every operator except that `Neg` is signed-only;
    // bool has the bit operators and `Not`; char and unit have none.
    let ints: Vec<Ty> = IntTy::ALL_SUPPORTED.iter().map(|&i| int(i)).collect();
    let op_impls = |p: &mut Program, ordinal: &mut u32, t: Ty, binops: &[DefId], unops: &[DefId], assigns: &[DefId]| {
        for &tr in binops {
            if let Some(out) = lang.output_of(tr) {
                // Shifts take any int right side (`impl Shl<i64> for
                // i32`), so `{integer}: Shl<i64>` stays ambiguous
                // until the literal fallback, as in rustc.
                if tr == lang.shl || tr == lang.shr {
                    for &r in &ints {
                        insert_synthetic(p, ordinal, tr, t, &[r], g0.clone(), vec![(out, t)], Synthetic::Lang, false, span);
                    }
                } else {
                    insert_synthetic(p, ordinal, tr, t, &[t], g0.clone(), vec![(out, t)], Synthetic::Lang, false, span);
                }
            }
        }
        for &tr in unops {
            if let Some(out) = lang.output_of(tr) {
                insert_synthetic(p, ordinal, tr, t, &[], g0.clone(), vec![(out, t)], Synthetic::Lang, false, span);
            }
        }
        for &tr in assigns {
            let rhs: &[Ty] = if tr == lang.shl_assign || tr == lang.shr_assign { &ints } else { std::slice::from_ref(&t) };
            for &r in rhs {
                insert_synthetic(p, ordinal, tr, t, &[r], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
        }
    };
    let int_binops = [lang.add, lang.sub, lang.mul, lang.div, lang.rem, lang.bit_and, lang.bit_or, lang.bit_xor, lang.shl, lang.shr];
    let int_assigns = [
        lang.add_assign,
        lang.sub_assign,
        lang.mul_assign,
        lang.div_assign,
        lang.rem_assign,
        lang.bit_and_assign,
        lang.bit_or_assign,
        lang.bit_xor_assign,
        lang.shl_assign,
        lang.shr_assign,
    ];
    for t in scalars {
        for tr in scalar_traits {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.partial_eq, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.partial_ord, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.ord, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        match p.tys.kind(t) {
            TyKind::Int(i) if i.signed() => op_impls(p, &mut ordinal, t, &int_binops, &[lang.neg, lang.not], &int_assigns),
            TyKind::Int(_) => op_impls(p, &mut ordinal, t, &int_binops, &[lang.not], &int_assigns),
            TyKind::Bool => op_impls(
                p,
                &mut ordinal,
                t,
                &[lang.bit_and, lang.bit_or, lang.bit_xor],
                &[lang.not],
                &[lang.bit_and_assign, lang.bit_or_assign, lang.bit_xor_assign],
            ),
            _ => {}
        }
    }
    // Floats have the scalar facts except Eq, Ord, Hash, and the
    // bit operators (std has no impls of those for f32 and f64).
    for f in [FloatTy::F32, FloatTy::F64] {
        let t = p.tys.float_ty(f);
        for tr in [lang.copy, lang.clone, lang.debug, lang.default] {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.partial_eq, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.partial_ord, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        op_impls(
            p,
            &mut ordinal,
            t,
            &[lang.add, lang.sub, lang.mul, lang.div, lang.rem],
            &[lang.neg],
            &[lang.add_assign, lang.sub_assign, lang.mul_assign, lang.div_assign, lang.rem_assign],
        );
    }
    // `process::ExitCode` (W-STD-A): Copy, Clone, Debug, PartialEq.
    // Std has no `Eq` for it; its `Default` is not in lust yet.
    {
        let t = p.tys.exit_code_ty();
        for tr in [lang.copy, lang.clone, lang.debug] {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.partial_eq, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // `thread::AccessError` (W-TLS): Copy, Clone, Debug, Display,
    // PartialEq, Eq, as in std; std source's `Result::unwrap` asks
    // `E: Debug` of it.
    {
        let def = p.tys.builtins().access_error;
        let t = p.tys.mk_adt(def, &[]);
        for tr in [lang.copy, lang.clone, lang.debug, lang.display, lang.eq] {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.partial_eq, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // `fmt::Arguments` (R9): Copy, Clone, Debug, and Display, as in
    // core. Both fmt impls format the parts with a fresh Formatter,
    // the outer specs ignored; cgen/fmt.rs has the rendering.
    {
        let t = crate::ty::fmt::fmt_ty(&mut p.tys, crate::ty::fmt::FmtTy::Arguments);
        for tr in [lang.copy, lang.clone, lang.debug, lang.display] {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
    }
    let p0 = p.tys.intern(TyKind::Param(ParamId(0)));
    let p1 = p.tys.intern(TyKind::Param(ParamId(1)));
    let one = Generics {
        parent: None,
        params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }],
        predicates: Vec::new(),
    };
    let pred_on = |p: &mut Program, trait_def: DefId, t: Ty| -> Predicate {
        let mut a = vec![GenericArg::Ty(t)];
        if trait_def == lang.partial_eq || trait_def == lang.partial_ord {
            a.push(GenericArg::Ty(t));
        }
        let args = p.tys.intern_args(&a);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    };
    let pred_on_p0 = |p: &mut Program, trait_def: DefId| -> Vec<Predicate> {
        let t = p.tys.intern(TyKind::Param(ParamId(0)));
        vec![pred_on(p, trait_def, t)]
    };
    // An impl whose trait takes `Rhs = Self` (`PartialEq`,
    // `PartialOrd`) names Self again as its input.
    let rhs_of = |trait_def: DefId, self_pat: Ty| -> Vec<Ty> {
        if trait_def == lang.partial_eq || trait_def == lang.partial_ord { vec![self_pat] } else { Vec::new() }
    };
    // `str` compares, orders, and hashes by its bytes.
    for tr in [lang.eq, lang.hash, lang.partial_eq, lang.partial_ord, lang.ord] {
        insert_synthetic(p, &mut ordinal, tr, STR, &rhs_of(tr, STR), g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // &T: Copy + Clone unconditionally, the rest through T.
    let ref_p0 = p.tys.mk_ref(false, p0);
    insert_synthetic(p, &mut ordinal, lang.copy, ref_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    insert_synthetic(p, &mut ordinal, lang.clone, ref_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    // Raw pointers (w-cinterop): Copy and Clone for every pointee, as in
    // core. Eq, Ord, Hash, and Debug act on the address of a sized
    // pointee only; a fat pointer (tf-fatptr) has `PartialEq`/`Eq` for
    // `str` and `[T]` (address and length) and none of the rest: lust
    // does not build them, and a dyn pointer's `==` compares vtable
    // addresses, which rustc does not fix. So a `T: ?Sized` generic
    // `*const T` has none of them either.
    let one_sized = Generics { predicates: vec![pred_on(p, lang.sized, p0)], ..one.clone() };
    for m in [Mut::Shared, Mut::Mut] {
        let self_pat = p.tys.intern(TyKind::RawPtr(m, p0));
        for tr in [lang.copy, lang.clone] {
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        for tr in [lang.eq, lang.hash, lang.ord, lang.debug] {
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[], one_sized.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        for tr in [lang.partial_eq, lang.partial_ord] {
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[self_pat], one_sized.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        let slice_p0 = p.tys.intern(TyKind::Slice(p0));
        for (pointee, g) in [(STR, g0.clone()), (slice_p0, one.clone())] {
            let fat = p.tys.intern(TyKind::RawPtr(m, pointee));
            insert_synthetic(p, &mut ordinal, lang.eq, fat, &[], g.clone(), Vec::new(), Synthetic::Lang, false, span);
            insert_synthetic(p, &mut ordinal, lang.partial_eq, fat, &[fat], g, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // Display: the std scalars, str, and String, and `&T` and `&mut T`
    // through T, so a `T: Display` bound holds at those types.
    let mut shown: Vec<Ty> = IntTy::ALL_SUPPORTED.iter().map(|&i| int(i)).collect();
    shown.extend([BOOL, CHAR, STR, STRING]);
    shown.extend([p.tys.float_ty(FloatTy::F32), p.tys.float_ty(FloatTy::F64)]);
    for t in shown {
        insert_synthetic(p, &mut ordinal, lang.display, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    let mut_p0 = p.tys.mk_ref(true, p0);
    for self_pat in [ref_p0, mut_p0] {
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.display);
        insert_synthetic(p, &mut ordinal, lang.display, self_pat, &[], g1, Vec::new(), Synthetic::Lang, false, span);
    }
    // String and the generic builtin containers.
    for tr in [lang.clone, lang.debug, lang.eq, lang.hash, lang.default, lang.partial_eq, lang.partial_ord, lang.ord] {
        insert_synthetic(p, &mut ordinal, tr, STRING, &rhs_of(tr, STRING), g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // Deref and DerefMut, as alloc and core have them: String to str,
    // Vec<T> to [T], &T to T, and &mut T to T (both). Calls of
    // `deref`/`deref_mut` on these are conversion builtins (check/convert.rs).
    let vec_p0 = p.tys.mk_vec(p0);
    let slice_p0 = p.tys.intern(TyKind::Slice(p0));
    for (self_pat, target, g, has_mut) in [
        (STRING, STR, g0.clone(), true),
        (vec_p0, slice_p0, one.clone(), true),
        (ref_p0, p0, one.clone(), false),
        (mut_p0, p0, one.clone(), true),
    ] {
        insert_synthetic(p, &mut ordinal, lang.deref, self_pat, &[], g.clone(), vec![(lang.assoc_target, target)], Synthetic::Lang, false, span);
        if has_mut {
            insert_synthetic(p, &mut ordinal, lang.deref_mut, self_pat, &[], g, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    let opt_p0 = p.tys.mk_option(p0);
    for (self_pat, with_copy) in [(vec_p0, false), (opt_p0, true)] {
        // `Default` for `Vec<T>` and `Option<T>` holds for every T.
        insert_synthetic(p, &mut ordinal, lang.default, self_pat, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        for tr in [lang.clone, lang.debug, lang.eq, lang.hash, lang.partial_eq, lang.partial_ord, lang.ord] {
            let preds = pred_on_p0(p, tr);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, tr, self_pat, &rhs_of(tr, self_pat), g1, Vec::new(), Synthetic::Lang, false, span);
        }
        if with_copy {
            let preds = pred_on_p0(p, lang.copy);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, lang.copy, self_pat, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // Result<T, E>: the derive-shaped traits through both params.
    {
        let two = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("E"), kind: ParamKind::Type, span },
            ],
            predicates: Vec::new(),
        };
        let res_pat = p.tys.mk_result(p0, p1);
        for tr in [lang.copy, lang.clone, lang.debug, lang.eq, lang.hash, lang.partial_eq, lang.partial_ord, lang.ord] {
            let mut g2 = two.clone();
            g2.predicates = vec![pred_on(p, tr, p0), pred_on(p, tr, p1)];
            insert_synthetic(p, &mut ordinal, tr, res_pat, &rhs_of(tr, res_pat), g2, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // Box<T>: like Vec for the derive-shaped traits, plus Deref
    // and DerefMut to T with no bounds of their own.
    {
        let box_p0 = p.tys.mk_boxed(p0);
        for tr in [lang.clone, lang.debug, lang.eq, lang.hash, lang.default, lang.partial_eq, lang.partial_ord, lang.ord] {
            let preds = pred_on_p0(p, tr);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, tr, box_p0, &rhs_of(tr, box_p0), g1, Vec::new(), Synthetic::Lang, false, span);
        }
        for tr in [lang.deref, lang.deref_mut] {
            insert_synthetic(
                p,
                &mut ordinal,
                tr,
                box_p0,
                &[],
                one.clone(),
                vec![(lang.assoc_target, p0)],
                Synthetic::Lang,
                false,
                span,
            );
        }
        // alloc's separate `impl<T> Default for Box<[T]>`: the empty
        // boxed slice, with no bound on `T` (a slice itself has no
        // `Default`, so the `Box<T: Default>` impl above never
        // applies to it).
        let slice_p0 = p.tys.intern(TyKind::Slice(p0));
        let box_slice_p0 = p.tys.mk_boxed(slice_p0);
        insert_synthetic(p, &mut ordinal, lang.default, box_slice_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // RefCell<T> and Cell<T>: core's `impl<T: Default> Default` and
    // Debug (`RefCell<T: Debug>`, `Cell<T: Copy + Debug>`); the guards
    // `Ref<T>` and `RefMut<T>` are Debug and Display through `T`
    // (W-STD-B; the default and fmt glue build and print them).
    {
        let refcell_p0 = p.tys.mk_builtin1(|d| d.refcell, p0);
        let cell_p0 = p.tys.mk_builtin1(|d| d.cell, p0);
        for t in [refcell_p0, cell_p0] {
            let mut g1 = one.clone();
            g1.predicates = pred_on_p0(p, lang.default);
            insert_synthetic(p, &mut ordinal, lang.default, t, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        }
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.debug);
        insert_synthetic(p, &mut ordinal, lang.debug, refcell_p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        let mut g1 = one.clone();
        g1.predicates = [pred_on_p0(p, lang.copy), pred_on_p0(p, lang.debug)].concat();
        insert_synthetic(p, &mut ordinal, lang.debug, cell_p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        for which in [(|d: &crate::ty::BuiltinDefs| d.ref_guard) as fn(&crate::ty::BuiltinDefs) -> DefId, |d| d.ref_mut_guard] {
            let guard = p.tys.mk_builtin1(which, p0);
            for tr in [lang.debug, lang.display] {
                let mut g1 = one.clone();
                g1.predicates = pred_on_p0(p, tr);
                insert_synthetic(p, &mut ordinal, tr, guard, &[], g1, Vec::new(), Synthetic::Lang, false, span);
            }
        }
        // The RefCell guards deref to `T` (R08), as in core: `Ref`
        // and `RefMut`, and `RefMut` also `DerefMut`. The lock guards'
        // records are in check/sync.rs. A `deref` call on a guard lowers
        // as a reborrow of its target (check/convert.rs).
        let guards = [(p.tys.mk_builtin1(|d| d.ref_guard, p0), false), (p.tys.mk_builtin1(|d| d.ref_mut_guard, p0), true)];
        for (guard, has_mut) in guards {
            let target = vec![(lang.assoc_target, p0)];
            insert_synthetic(p, &mut ordinal, lang.deref, guard, &[], one.clone(), target, Synthetic::Lang, false, span);
            if has_mut {
                insert_synthetic(p, &mut ordinal, lang.deref_mut, guard, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
        }
    }
    // `NonZero<T>` (TRIAGE T5): Debug and Display forward to the
    // integer, as core's impls do (glue in cgen/fmt.rs). The value
    // traits are the Adt's derives (collect.rs).
    {
        let nz_p0 = nonzero_ty(&mut p.tys, p0);
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.display);
        insert_synthetic(p, &mut ordinal, lang.display, nz_p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
    }
    // `TrySendError<T>` (TRIAGE T5): Display is std's text, with
    // no bound on T (glue in cgen/fmt.rs). Its Debug hides the
    // value, also with no bound (collect's glue_debug list).
    {
        let tse_p0 = try_send_error_ty(&mut p.tys, p0);
        insert_synthetic(p, &mut ordinal, lang.display, tse_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.debug, tse_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // `TryLockError<T>`: Debug (`"Poisoned(..)"`, `"WouldBlock"`) and
    // Display are std's texts with no bound on T (glue in cgen/fmt.rs).
    {
        let tle_p0 = try_lock_error_ty(&mut p.tys, p0);
        insert_synthetic(p, &mut ordinal, lang.display, tle_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.debug, tle_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // Rc<T>: Clone needs no bound on T (it bumps the count);
    // the rest follow the pointee like Box, with Deref only.
    {
        let rc_p0 = p.tys.mk_rc(p0);
        insert_synthetic(p, &mut ordinal, lang.clone, rc_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        for tr in [lang.debug, lang.eq, lang.hash, lang.default, lang.partial_eq, lang.partial_ord, lang.ord] {
            let preds = pred_on_p0(p, tr);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, tr, rc_p0, &rhs_of(tr, rc_p0), g1, Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(
            p,
            &mut ordinal,
            lang.deref,
            rc_p0,
            &[],
            one.clone(),
            vec![(lang.assoc_target, p0)],
            Synthetic::Lang,
            false,
            span,
        );
        // rc::Weak<T>: Debug (prints `(Weak)`) and Clone with no bound
        // on T, as in alloc (`OnceCell<S>: Debug` with a `Weak` field
        // in `S`, R26).
        let weak_p0 = p.tys.mk_builtin1(|d| d.weak, p0);
        for tr in [lang.debug, lang.clone] {
            insert_synthetic(p, &mut ordinal, tr, weak_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // alloc's `impl<T> Default for Weak<T>` is `Weak::new()`, with
        // `T: Sized` (`rc::Weak<dyn Fn()>` has no default), as for
        // `sync::Weak` (check/sync.rs).
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.sized);
        insert_synthetic(p, &mut ordinal, lang.default, weak_p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
    }
    // From<T> for T, and Into through From.
    insert_synthetic(p, &mut ordinal, lang.from, p0, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    // The std `From` impls whose `into` calls stay builtin (check/into.rs):
    // String from &str, &String, and char; Box<T> and Rc<T> from T.
    {
        let ref_string = p.tys.mk_ref(false, STRING);
        for src in [REF_STR, ref_string, CHAR] {
            insert_synthetic(p, &mut ordinal, lang.from, STRING, &[src], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        let (box_p0, rc_p0) = (p.tys.mk_boxed(p0), p.tys.mk_rc(p0));
        for t in [box_p0, rc_p0] {
            insert_synthetic(p, &mut ordinal, lang.from, t, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // core's `From<NonZero<T>> for T` per integer (convert.rs
        // `FromConv::NonZeroGet`; `available_parallelism().map_or(4, Into::into)`).
        for &i in IntTy::ALL_SUPPORTED.iter() {
            let nz = nonzero_ty(&mut p.tys, int(i));
            insert_synthetic(p, &mut ordinal, lang.from, int(i), &[nz], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
    }
    {
        // impl<T, U> Into<U> for T where U: From<T>
        let args = p.tys.intern_args(&[GenericArg::Ty(p1), GenericArg::Ty(p0)]);
        let g2 = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("U"), kind: ParamKind::Type, span },
            ],
            predicates: vec![Predicate::Trait(Binder::plain(TraitRef { def: lang.from, args, bindings: EMPTY_BINDINGS }))],
        };
        insert_synthetic(p, &mut ordinal, lang.into, p0, &[p1], g2, Vec::new(), Synthetic::Lang, false, span);
    }
    // The rest of std's `From` impls between builtin types (W-STD-B,
    // check/convert.rs `std_from`, which also answers the array forms by
    // structure; the block above has String from &str, &String, and
    // char, and Box<T> and Rc<T> from T): selection and coherence only;
    // calls are `Builtin::ConvInto`.
    {
        let ref_str = p.tys.mk_ref(false, STR);
        let mut_str = p.tys.mk_ref(true, STR);
        let ref_string = p.tys.mk_ref(false, STRING);
        let cow_str = p.tys.mk_adt(cow_def(), &[GenericArg::Ty(STR)]);
        let bytes = p.tys.mk_vec(int(IntTy::U8));
        let slice_p0 = p.tys.intern(TyKind::Slice(p0));
        let vec_p0 = p.tys.mk_vec(p0);
        let cow_slice = p.tys.mk_adt(cow_def(), &[GenericArg::Ty(slice_p0)]);
        let ref_slice = p.tys.mk_ref(false, slice_p0);
        let mut_slice = p.tys.mk_ref(true, slice_p0);
        let ref_vec = p.tys.mk_ref(false, vec_p0);
        let box_slice = p.tys.mk_boxed(slice_p0);
        let mut cloned = one.clone();
        cloned.predicates = pred_on_p0(p, lang.clone);
        for (dst, src) in [(STRING, mut_str), (STRING, cow_str), (bytes, STRING), (bytes, ref_str)] {
            insert_synthetic(p, &mut ordinal, lang.from, dst, &[src], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // alloc::borrow's two generic Cow impls, for every
        // `B: ?Sized + ToOwned`: `From<&B>` and `From<B::Owned>`.
        // They cover Cow<str> from &str and String and Cow<[T]> from
        // &[T] and Vec<T>; the &String and &Vec view impls of alloc
        // stay specific below.
        {
            let cow_p0 = p.tys.mk_adt(cow_def(), &[GenericArg::Ty(p0)]);
            let ref_p0 = p.tys.mk_ref(false, p0);
            let a = p.tys.intern_args(&[GenericArg::Ty(p0)]);
            let owned_p0 = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_owned), a));
            let mut g = one.clone();
            g.predicates = pred_on_p0(p, lang.to_owned);
            for src in [ref_p0, owned_p0] {
                insert_synthetic(p, &mut ordinal, lang.from, cow_p0, &[src], g.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
        }
        insert_synthetic(p, &mut ordinal, lang.from, cow_str, &[ref_string], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        for (dst, src) in [
            (vec_p0, ref_slice),
            (vec_p0, mut_slice),
            (vec_p0, cow_slice),
            (cow_slice, ref_vec),
        ] {
            insert_synthetic(p, &mut ordinal, lang.from, dst, &[src], cloned.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        let opt_p0 = p.tys.mk_option(p0);
        for (dst, src) in [(vec_p0, box_slice), (box_slice, vec_p0), (opt_p0, p0)] {
            insert_synthetic(p, &mut ordinal, lang.from, dst, &[src], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // TryFrom through Into (Error = Infallible), TryInto through
    // TryFrom (fx-tryfrom; core::convert's two blankets), and the
    // `Display` records of core's conversion error types. The scalar
    // `TryFrom` pairs are builtins (check/tryfrom.rs), like numeric
    // `From`: selection answers them ahead of these records.
    {
        let inf = p.tys.intern(TyKind::Adt(infallible_def(), EMPTY_ARGS));
        let (nt, nu) = (p.interner.intern("T"), p.interner.intern("U"));
        let pred = |p: &mut Program, pred_def: DefId| {
            let args = p.tys.intern_args(&[GenericArg::Ty(p1), GenericArg::Ty(p0)]);
            Generics {
                parent: None,
                params: vec![
                    ParamDef { name: nt, kind: ParamKind::Type, span },
                    ParamDef { name: nu, kind: ParamKind::Type, span },
                ],
                predicates: vec![Predicate::Trait(Binder::plain(TraitRef { def: pred_def, args, bindings: EMPTY_BINDINGS }))],
            }
        };
        let g = pred(p, lang.into);
        insert_synthetic(p, &mut ordinal, lang.try_from, p0, &[p1], g, vec![(lang.assoc_try_from_error, inf)], Synthetic::Lang, false, span);
        let err_args = p.tys.intern_args(&[GenericArg::Ty(p1), GenericArg::Ty(p0)]);
        let err_proj = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_try_from_error), err_args));
        let g = pred(p, lang.try_from);
        insert_synthetic(p, &mut ordinal, lang.try_into, p0, &[p1], g, vec![(lang.assoc_try_into_error, err_proj)], Synthetic::Lang, false, span);
        // core's `Display` for its conversion errors (the text is
        // `display_glue_body`'s): a record, so the source `Error`
        // impls in library/core/src/error.rs meet their supertrait.
        for def in [try_from_int_error_def(), char_try_from_error_def(), try_from_char_error_def(), infallible_def(), parse_int_error_def(), parse_float_error_def(), parse_bool_error_def(), parse_char_error_def(), try_from_slice_error_def()] {
            let t = p.tys.intern(TyKind::Adt(def, EMPTY_ARGS));
            insert_synthetic(p, &mut ordinal, lang.display, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // The conversion traits (W-STD-B, check/convert.rs), as core and
    // alloc declare them for the types lust has. Arrays also answer
    // by structure in the method probe.
    {
        let tp = |p: &mut Program, tr: DefId, s: Ty, r: Ty| {
            let a = p.tys.intern_args(&[GenericArg::Ty(s), GenericArg::Ty(r)]);
            Predicate::Trait(Binder::plain(TraitRef { def: tr, args: a, bindings: EMPTY_BINDINGS }))
        };
        let two = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("U"), kind: ParamKind::Type, span },
            ],
            predicates: Vec::new(),
        };
        let bytes = p.tys.intern(TyKind::Slice(int(IntTy::U8)));
        let slice_p0 = p.tys.intern(TyKind::Slice(p0));
        let vec_p0 = p.tys.mk_vec(p0);
        let box_p0 = p.tys.mk_boxed(p0);
        let rc_p0 = p.tys.mk_rc(p0);
        let ref_p0 = p.tys.mk_ref(false, p0);
        let mut_p0 = p.tys.mk_ref(true, p0);
        // AsRef: through & and &mut, str and String to str and [u8],
        // [T] and Vec<T> to [T], Vec<T> to itself, Box and Rc to T.
        for self_pat in [ref_p0, mut_p0] {
            let mut g = two.clone();
            g.predicates = vec![tp(p, lang.as_ref, p0, p1)];
            insert_synthetic(p, &mut ordinal, lang.as_ref, self_pat, &[p1], g, Vec::new(), Synthetic::Lang, false, span);
        }
        for (s, t) in [(STR, STR), (STR, bytes), (STRING, STR), (STRING, bytes)] {
            insert_synthetic(p, &mut ordinal, lang.as_ref, s, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        for (s, t) in [(slice_p0, slice_p0), (vec_p0, slice_p0), (vec_p0, vec_p0), (box_p0, p0), (rc_p0, p0)] {
            insert_synthetic(p, &mut ordinal, lang.as_ref, s, &[t], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // `[T; N]` to `[T]` for every conversion trait (core's array
        // impls): a const-param record, so a generic bound such as
        // `B: AsRef<[u8]>` holds for an array argument, as the method
        // probe already answers for a direct `as_ref()` call.
        let arr_g = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("N"), kind: ParamKind::Const(USIZE), span },
            ],
            predicates: Vec::new(),
        };
        let n_param = p.tys.intern_const(ConstKind::Param(1));
        let arr_p0 = p.tys.intern(TyKind::Array(p0, n_param));
        for tr in [lang.as_ref, lang.as_mut, lang.borrow, lang.borrow_mut] {
            insert_synthetic(p, &mut ordinal, tr, arr_p0, &[slice_p0], arr_g.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // AsMut: through &mut, str and String to str, [T] and Vec<T>
        // to [T], Vec<T> to itself, Box to T.
        {
            let mut g = two.clone();
            g.predicates = vec![tp(p, lang.as_mut, p0, p1)];
            insert_synthetic(p, &mut ordinal, lang.as_mut, mut_p0, &[p1], g, Vec::new(), Synthetic::Lang, false, span);
        }
        for (s, t) in [(STR, STR), (STRING, STR)] {
            insert_synthetic(p, &mut ordinal, lang.as_mut, s, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        for (s, t) in [(slice_p0, slice_p0), (vec_p0, slice_p0), (vec_p0, vec_p0), (box_p0, p0)] {
            insert_synthetic(p, &mut ordinal, lang.as_mut, s, &[t], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // Borrow: T to itself, &T and &mut T to T, String to str, Vec<T>
        // to [T], Box and Rc to T. BorrowMut: T, &mut T, String, Vec, Box.
        for (s, t) in [(p0, p0), (ref_p0, p0), (mut_p0, p0), (vec_p0, slice_p0), (box_p0, p0), (rc_p0, p0)] {
            insert_synthetic(p, &mut ordinal, lang.borrow, s, &[t], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.borrow, STRING, &[STR], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        for (s, t) in [(p0, p0), (mut_p0, p0), (vec_p0, slice_p0), (box_p0, p0)] {
            insert_synthetic(p, &mut ordinal, lang.borrow_mut, s, &[t], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.borrow_mut, STRING, &[STR], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        // ToOwned: str to String, [T: Clone] to Vec<T>, T: Clone to T.
        insert_synthetic(p, &mut ordinal, lang.to_owned, STR, &[], g0.clone(), vec![(lang.assoc_owned, STRING)], Synthetic::Lang, false, span);
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.clone);
        insert_synthetic(p, &mut ordinal, lang.to_owned, slice_p0, &[], g1.clone(), vec![(lang.assoc_owned, vec_p0)], Synthetic::Lang, false, span);
        // The blanket `impl<T: Clone> ToOwned for T` has core's implicit
        // `T: Sized`, which keeps `[T]` and `str` out of it.
        g1.predicates.extend(pred_on_p0(p, lang.sized));
        insert_synthetic(p, &mut ordinal, lang.to_owned, p0, &[], g1, vec![(lang.assoc_owned, p0)], Synthetic::Lang, false, span);
        // `impl<T: Display + ?Sized> ToString for T`.
        let mut g1 = one.clone();
        g1.predicates = pred_on_p0(p, lang.display);
        insert_synthetic(p, &mut ordinal, lang.to_string, p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
    }
    // Iterator for the builtin iterator structs (ty/iter.rs, W-STD-A):
    // selection and `Item` normalization only; `next` and the
    // adapters stay builtin calls.
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        let names = ["I", "F", "B"];
        for k in K::ALL {
            if !k.is_iterator() {
                continue;
            }
            let params: Vec<ParamDef> =
                (0..k.n_args()).map(|i| ParamDef { name: p.interner.intern(names[i]), kind: ParamKind::Type, span }).collect();
            let ps: Vec<Ty> = (0..k.n_args() as u32).map(|i| p.tys.intern(TyKind::Param(ParamId(i)))).collect();
            let self_pat = mk_iter(&mut p.tys, k, &ps);
            let proj = |p: &mut Program, t: Ty| {
                let a = p.tys.intern_args(&[GenericArg::Ty(t)]);
                p.tys.intern(TyKind::Projection(AssocId(lang.assoc_item), a))
            };
            let item = match k {
                K::SliceIter => p.tys.mk_ref(false, ps[0]),
                K::SliceIterMut => p.tys.mk_ref(true, ps[0]),
                K::Windows => {
                    let s = p.tys.intern(TyKind::Slice(ps[0]));
                    p.tys.mk_ref(false, s)
                }
                K::Chunks | K::ChunksExact => {
                    let s = p.tys.intern(TyKind::Slice(ps[0]));
                    p.tys.mk_ref(false, s)
                }
                K::SliceSplit | K::SliceSplitMut => {
                    let s = p.tys.intern(TyKind::Slice(ps[0]));
                    p.tys.mk_ref(k == K::SliceSplitMut, s)
                }
                K::ChunkBy | K::ChunkByMut => {
                    let s = p.tys.intern(TyKind::Slice(ps[0]));
                    p.tys.mk_ref(k == K::ChunkByMut, s)
                }
                K::ChunksMut | K::ChunksExactMut => {
                    let s = p.tys.intern(TyKind::Slice(ps[0]));
                    p.tys.mk_ref(true, s)
                }
                K::Utf8Chunks => mk_iter(&mut p.tys, K::Utf8Chunk, &[ps[0]]),
                K::CharIndices => {
                    let ts = p.tys.intern_tys(&[USIZE, CHAR]);
                    p.tys.intern(TyKind::Tuple(ts))
                }
                K::EncodeUtf16 => int(IntTy::U16),
                K::Flatten => proj(p, ps[1]),
                K::OptionIntoIter | K::ResultIntoIter => ps[0],
                K::OptionIter | K::ResultIter => p.tys.mk_ref(false, ps[0]),
                K::OptionIterMut | K::ResultIterMut => p.tys.mk_ref(true, ps[0]),
                K::VecIntoIter | K::Range | K::RangeInclusive | K::RangeFrom | K::VecDrain => ps[0],
                K::StringDrain => CHAR,
                K::Map | K::FilterMap | K::MapWhile => ps[2],
                K::Copied | K::Cloned => ps[1],
                // The hashed-collection iterators (W-STD-B).
                K::MapIter | K::MapIterMut => {
                    let kr = p.tys.mk_ref(false, ps[0]);
                    let vr = p.tys.mk_ref(k == K::MapIterMut, ps[1]);
                    let ts = p.tys.intern_tys(&[kr, vr]);
                    p.tys.intern(TyKind::Tuple(ts))
                }
                K::MapKeys | K::SetIter => p.tys.mk_ref(false, ps[0]),
                K::MapValues => p.tys.mk_ref(false, ps[1]),
                K::MapValuesMut => p.tys.mk_ref(true, ps[1]),
                K::MapIntoIter | K::MapDrain => {
                    let ts = p.tys.intern_tys(&[ps[0], ps[1]]);
                    p.tys.intern(TyKind::Tuple(ts))
                }
                K::MapIntoKeys | K::SetIntoIter | K::SetDrain | K::RepeatN | K::ArrayIntoIter => ps[0],
                K::MapIntoValues | K::ByNext => ps[1],
                K::Args => STRING,
                K::Enumerate => {
                    let inner = proj(p, ps[0]);
                    let ts = p.tys.intern_tys(&[USIZE, inner]);
                    p.tys.intern(TyKind::Tuple(ts))
                }
                K::Zip => {
                    let (x, y) = (proj(p, ps[0]), proj(p, ps[1]));
                    let ts = p.tys.intern_tys(&[x, y]);
                    p.tys.intern(TyKind::Tuple(ts))
                }
                _ => proj(p, ps[0]),
            };
            // The where clauses of core's `Iterator` impl for an adapter,
            // which every selection and `Item` normalization proves: the
            // wrapped iterators are iterators, and `Copied` / `Cloned`
            // need `T: Copy` / `T: Clone` (their `I: Iterator<Item = &T>`
            // binds `T`; lowering checked the item shape), and `Chain`'s
            // sides have one item type. `Rev`'s `I: DoubleEndedIterator`
            // is checked where the type is written (`stdtypes`).
            let mut base: Vec<Predicate> = if k.is_adapter() { vec![pred_on(p, lang.iterator, ps[0])] } else { Vec::new() };
            match k {
                // `B: Iterator<Item = A::Item>`.
                K::Chain => {
                    let a_item = proj(p, ps[0]);
                    let args = p.tys.intern_args(&[GenericArg::Ty(ps[1])]);
                    let bindings = p.tys.intern_bindings(&[(lang.assoc_item, GenericArg::Ty(a_item))]);
                    base.push(Predicate::Trait(Binder::plain(TraitRef { def: lang.iterator, args, bindings })));
                }
                K::Zip | K::Flatten => base.push(pred_on(p, lang.iterator, ps[1])),
                K::Copied => base.push(pred_on(p, lang.copy, ps[1])),
                K::Cloned => base.push(pred_on(p, lang.clone, ps[1])),
                _ => {}
            }
            let g = Generics { parent: None, params, predicates: base.clone() };
            insert_synthetic(p, &mut ordinal, lang.iterator, self_pat, &[], g.clone(), vec![(lang.assoc_item, item)], Synthetic::Lang, false, span);
            // `ExactSizeIterator` and `DoubleEndedIterator` for the
            // kinds core marks so (fx-option-rest; the same sets as
            // check/iter.rs `exact_size` and `double_ended`).
            // Selection only: `len` and `next_back` stay builtin calls.
            let exact: Option<Vec<Predicate>> = match k {
                K::ArrayIntoIter
                | K::RepeatN
                | K::Windows
                | K::Chunks
                | K::ChunksMut
                | K::ChunksExact
                | K::ChunksExactMut
                | K::OptionIter
                | K::OptionIterMut
                | K::OptionIntoIter
                | K::ResultIter
                | K::ResultIterMut
                | K::ResultIntoIter
                | K::MapIter
                | K::MapIterMut
                | K::MapKeys
                | K::MapValues
                | K::MapValuesMut
                | K::MapIntoIter
                | K::MapIntoKeys
                | K::MapIntoValues
                | K::SetIter
                | K::SetIntoIter
                | K::MapDrain
                | K::SetDrain
                | K::Args => Some(Vec::new()),
                K::Map | K::Copied | K::Cloned | K::Rev | K::Enumerate | K::Inspect | K::Take | K::Skip | K::StepBy | K::Peekable => {
                    Some(vec![pred_on(p, lang.exact_size_iterator, ps[0])])
                }
                K::Zip => Some(vec![pred_on(p, lang.exact_size_iterator, ps[0]), pred_on(p, lang.exact_size_iterator, ps[1])]),
                _ => None,
            };
            if let Some(mut predicates) = exact {
                predicates.extend(base.iter().copied());
                let ge = Generics { parent: None, params: g.params.clone(), predicates };
                insert_synthetic(p, &mut ordinal, lang.exact_size_iterator, self_pat, &[], ge, Vec::new(), Synthetic::Lang, false, span);
            }
            let double_ended: Option<Vec<Predicate>> = match k {
                K::Windows
                | K::Chunks
                | K::ChunksMut
                | K::ChunksExact
                | K::ChunksExactMut
                | K::CharIndices
                | K::ArrayIntoIter
                | K::RepeatN
                | K::OptionIter
                | K::OptionIterMut
                | K::OptionIntoIter
                | K::ResultIter
                | K::ResultIterMut
                | K::ResultIntoIter
                | K::Args => Some(Vec::new()),
                K::Map | K::Filter | K::FilterMap | K::Rev | K::Copied | K::Cloned | K::Inspect | K::Peekable => {
                    Some(vec![pred_on(p, lang.double_ended_iterator, ps[0])])
                }
                K::Chain => Some(vec![pred_on(p, lang.double_ended_iterator, ps[0]), pred_on(p, lang.double_ended_iterator, ps[1])]),
                _ => None,
            };
            if let Some(mut predicates) = double_ended {
                predicates.extend(base.iter().copied());
                let gd = Generics { parent: None, params: g.params.clone(), predicates };
                insert_synthetic(p, &mut ordinal, lang.double_ended_iterator, self_pat, &[], gd, Vec::new(), Synthetic::Lang, false, span);
            }
        }
        let chars = CHARS;
        insert_synthetic(p, &mut ordinal, lang.iterator, chars, &[], g0.clone(), vec![(lang.assoc_item, CHAR)], Synthetic::Lang, false, span);
    }
    // `FromStr` for the primitive types (tf-str): selection and the
    // `Err` normalization only; `str::parse` runs through its own
    // builtin (lower/iter.rs), as `next` does for `Iterator` above.
    {
        use crate::ty::{FloatTy, IntTy};
        let pie = parse_int_error_ty(&mut p.tys);
        for i in [
            IntTy::I8,
            IntTy::I16,
            IntTy::I32,
            IntTy::I64,
            IntTy::I128,
            IntTy::Isize,
            IntTy::U8,
            IntTy::U16,
            IntTy::U32,
            IntTy::U64,
            IntTy::U128,
            IntTy::Usize,
        ] {
            let t = p.tys.intern(TyKind::Int(i));
            insert_synthetic(p, &mut ordinal, lang.from_str, t, &[], g0.clone(), vec![(lang.assoc_from_str_err, pie)], Synthetic::Lang, false, span);
        }
        let pfe = parse_float_error_ty(&mut p.tys);
        for f in [FloatTy::F32, FloatTy::F64] {
            let t = p.tys.intern(TyKind::Float(f));
            insert_synthetic(p, &mut ordinal, lang.from_str, t, &[], g0.clone(), vec![(lang.assoc_from_str_err, pfe)], Synthetic::Lang, false, span);
        }
        let pbe = parse_bool_error_ty(&mut p.tys);
        insert_synthetic(p, &mut ordinal, lang.from_str, BOOL, &[], g0.clone(), vec![(lang.assoc_from_str_err, pbe)], Synthetic::Lang, false, span);
        let pce = parse_char_error_ty(&mut p.tys);
        insert_synthetic(p, &mut ordinal, lang.from_str, CHAR, &[], g0.clone(), vec![(lang.assoc_from_str_err, pce)], Synthetic::Lang, false, span);
        let inf = infallible_ty(&mut p.tys);
        insert_synthetic(p, &mut ordinal, lang.from_str, STRING, &[], g0.clone(), vec![(lang.assoc_from_str_err, inf)], Synthetic::Lang, false, span);
    }
    // ExactSizeIterator and DoubleEndedIterator for the builtin
    // iterator sources: selection only, like `Iterator` above. The
    // adapters' conditional impls wait (a bound on an adapter type
    // rejects instead of proving).
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        for k in [K::SliceIter, K::SliceIterMut, K::VecIntoIter, K::VecDrain, K::Range] {
            let self_pat = mk_iter(&mut p.tys, k, &[p0]);
            if k != K::Range {
                insert_synthetic(p, &mut ordinal, lang.exact_size_iterator, self_pat, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
            insert_synthetic(p, &mut ordinal, lang.double_ended_iterator, self_pat, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        // `Range` is exact size over core's `range_exact_iter_impl!`
        // list only (not 64-bit, 128-bit, or `char` ranges).
        {
            use crate::ty::IntTy as I;
            for i in [I::Usize, I::U8, I::U16, I::U32, I::Isize, I::I8, I::I16, I::I32] {
                let t = p.tys.intern(TyKind::Int(i));
                let self_pat = mk_iter(&mut p.tys, K::Range, &[t]);
                insert_synthetic(p, &mut ordinal, lang.exact_size_iterator, self_pat, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
        }
        // `RangeInclusive` is double-ended; it is exact size over core's
        // `range_incl_exact_iter_impl!` list only (a wider one can hold
        // `usize::MAX + 1` items).
        {
            use crate::ty::IntTy as I;
            for i in [I::U8, I::I8, I::U16, I::I16] {
                let t = p.tys.intern(TyKind::Int(i));
                let self_pat = mk_iter(&mut p.tys, K::RangeInclusive, &[t]);
                insert_synthetic(p, &mut ordinal, lang.exact_size_iterator, self_pat, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
            }
        }
        let ri = mk_iter(&mut p.tys, K::RangeInclusive, &[p0]);
        insert_synthetic(p, &mut ordinal, lang.double_ended_iterator, ri, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        let sd = mk_iter(&mut p.tys, K::StringDrain, &[]);
        insert_synthetic(p, &mut ordinal, lang.double_ended_iterator, sd, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.double_ended_iterator, CHARS, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // RangeBounds for the six range kinds and the `(Bound, Bound)`
    // pair (core::ops; std has no reference impl). Selection
    // only: `start_bound` and `end_bound` stay builtin calls on the
    // concrete kinds.
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        for k in [K::Range, K::RangeInclusive, K::RangeFrom, K::RangeTo, K::RangeToInclusive] {
            let self_pat = mk_iter(&mut p.tys, k, &[p0]);
            insert_synthetic(p, &mut ordinal, lang.range_bounds, self_pat, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        let full = mk_iter(&mut p.tys, K::RangeFull, &[]);
        insert_synthetic(p, &mut ordinal, lang.range_bounds, full, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        let b0 = bound_ty(&mut p.tys, p0);
        let pair_ts = p.tys.intern_tys(&[b0, b0]);
        let pair = p.tys.intern(TyKind::Tuple(pair_ts));
        insert_synthetic(p, &mut ordinal, lang.range_bounds, pair, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        let rp0 = p.tys.mk_ref(false, p0);
        let br = bound_ty(&mut p.tys, rp0);
        let pairr_ts = p.tys.intern_tys(&[br, br]);
        let pairr = p.tys.intern(TyKind::Tuple(pairr_ts));
        insert_synthetic(p, &mut ordinal, lang.range_bounds, pairr, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    // The six range kinds derive PartialEq, Eq, and Hash over their
    // fields in core (`RangeFull` with no bound; its Hash is left out
    // here); the glue compares and hashes their C tuples
    // (`collect::range_elem`).
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        for k in [K::Range, K::RangeInclusive, K::RangeFrom, K::RangeTo, K::RangeToInclusive, K::RangeFull] {
            let full = k == K::RangeFull;
            let self_pat = if full { mk_iter(&mut p.tys, k, &[]) } else { mk_iter(&mut p.tys, k, &[p0]) };
            for tr in [lang.partial_eq, lang.eq, lang.hash] {
                // `RangeFull` hashes no glue (`collect::range_elem`).
                if full && tr == lang.hash {
                    continue;
                }
                let g = if full {
                    g0.clone()
                } else {
                    let mut g1 = one.clone();
                    g1.predicates = pred_on_p0(p, tr);
                    g1
                };
                insert_synthetic(p, &mut ordinal, tr, self_pat, &rhs_of(tr, self_pat), g, Vec::new(), Synthetic::Lang, false, span);
            }
        }
    }
    // IntoIterator for the builtin collections, as alloc and core
    // declare it: Vec<T> by value (vec::IntoIter<T>), &Vec<T> and &[T]
    // (slice::Iter), &mut Vec<T> and &mut [T] (slice::IterMut). Their
    // `into_iter` stays a builtin call.
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        let t = p.tys.intern(TyKind::Param(ParamId(0)));
        let vec_t = p.tys.mk_vec(t);
        let slice_t = p.tys.intern(TyKind::Slice(t));
        let (ref_t, mut_t) = (p.tys.mk_ref(false, t), p.tys.mk_ref(true, t));
        let (iter, iter_mut, into_iter) =
            (mk_iter(&mut p.tys, K::SliceIter, &[t]), mk_iter(&mut p.tys, K::SliceIterMut, &[t]), mk_iter(&mut p.tys, K::VecIntoIter, &[t]));
        let g1 = Generics { parent: None, params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }], predicates: Vec::new() };
        let entries = [
            (vec_t, into_iter, t),
            (p.tys.mk_ref(false, vec_t), iter, ref_t),
            (p.tys.mk_ref(true, vec_t), iter_mut, mut_t),
            (p.tys.mk_ref(false, slice_t), iter, ref_t),
            (p.tys.mk_ref(true, slice_t), iter_mut, mut_t),
        ];
        for (self_pat, it, item) in entries {
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, it)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, self_pat, &[], g1.clone(), assoc, Synthetic::Lang, false, span);
        }
    }
    // `IntoIterator` for arrays and their references (fx-array-iter),
    // as core declares it since edition 2021: `[T; N]` by value is
    // `array::IntoIter` (item `T`, for every `T`), `&[T; N]` is
    // `slice::Iter`, `&mut [T; N]` is `slice::IterMut`. Selection and
    // Item/IntoIter only; `into_iter` and `for` stay builtin.
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        let t = p.tys.intern(TyKind::Param(ParamId(0)));
        let n = p.tys.intern_const(crate::ty::ConstKind::Param(1));
        let arr_t = p.tys.intern(TyKind::Array(t, n));
        let (ref_t, mut_t) = (p.tys.mk_ref(false, t), p.tys.mk_ref(true, t));
        let g = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("N"), kind: ParamKind::Const(USIZE), span },
            ],
            predicates: Vec::new(),
        };
        let entries = [
            (arr_t, mk_iter(&mut p.tys, K::ArrayIntoIter, &[t, arr_t]), t),
            (p.tys.mk_ref(false, arr_t), mk_iter(&mut p.tys, K::SliceIter, &[t]), ref_t),
            (p.tys.mk_ref(true, arr_t), mk_iter(&mut p.tys, K::SliceIterMut, &[t]), mut_t),
        ];
        for (self_pat, it, item) in entries {
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, it)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, self_pat, &[], g.clone(), assoc, Synthetic::Lang, false, span);
        }
    }
    // `IntoIterator` for `Option` and `Result` and their references
    // (fx-option-rest), as core declares it: by value the `IntoIter`
    // (item `T`), by `&` the `Iter` (item `&T`), by `&mut` the
    // `IterMut` (item `&mut T`). Selection and Item/IntoIter only;
    // `into_iter` and `for` stay builtin.
    {
        use crate::ty::iter::{IterKind as K, mk_iter};
        let t = p.tys.intern(TyKind::Param(ParamId(0)));
        let e = p.tys.intern(TyKind::Param(ParamId(1)));
        let (ref_t, mut_t) = (p.tys.mk_ref(false, t), p.tys.mk_ref(true, t));
        let g1 = Generics { parent: None, params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }], predicates: Vec::new() };
        let g2 = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("E"), kind: ParamKind::Type, span },
            ],
            predicates: Vec::new(),
        };
        let opt_t = p.tys.mk_option(t);
        let opts = [
            (opt_t, mk_iter(&mut p.tys, K::OptionIntoIter, &[t]), t),
            (p.tys.mk_ref(false, opt_t), mk_iter(&mut p.tys, K::OptionIter, &[t]), ref_t),
            (p.tys.mk_ref(true, opt_t), mk_iter(&mut p.tys, K::OptionIterMut, &[t]), mut_t),
        ];
        for (self_pat, it, item) in opts {
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, it)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, self_pat, &[], g1.clone(), assoc, Synthetic::Lang, false, span);
        }
        let res_t = p.tys.mk_result(t, e);
        let ress = [
            (res_t, mk_iter(&mut p.tys, K::ResultIntoIter, &[t]), t),
            (p.tys.mk_ref(false, res_t), mk_iter(&mut p.tys, K::ResultIter, &[t]), ref_t),
            (p.tys.mk_ref(true, res_t), mk_iter(&mut p.tys, K::ResultIterMut, &[t]), mut_t),
        ];
        for (self_pat, it, item) in ress {
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, it)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, self_pat, &[], g2.clone(), assoc, Synthetic::Lang, false, span);
        }
    }
    // `Cow<'_, B>` (W-STD-B): Clone for every B (the Owned value clones
    // through `ToOwned`), the rest through B, as std's impls deref.
    {
        let cow_p0 = p.tys.mk_adt(cow_def(), &[GenericArg::Ty(p0)]);
        insert_synthetic(p, &mut ordinal, lang.clone, cow_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        // `Default` when the Owned type has one: `Owned::default()`.
        {
            let a = p.tys.intern_args(&[GenericArg::Ty(p0)]);
            let owned_p0 = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_owned), a));
            let mut g = one.clone();
            g.predicates = vec![pred_on(p, lang.default, owned_p0)];
            insert_synthetic(p, &mut ordinal, lang.default, cow_p0, &[], g, Vec::new(), Synthetic::Lang, false, span);
        }
        // `Add` and `AddAssign` for `Cow<str>`, with a `&str` or a
        // Cow right side: selection only, the calls are the Cow
        // addition builtins (check/cow.rs).
        {
            let cow_str = p.tys.mk_adt(cow_def(), &[GenericArg::Ty(STR)]);
            let ref_str = p.tys.mk_ref(false, STR);
            if let Some(out) = lang.output_of(lang.add) {
                for rhs in [ref_str, cow_str] {
                    insert_synthetic(p, &mut ordinal, lang.add, cow_str, &[rhs], g0.clone(), vec![(out, cow_str)], Synthetic::Lang, false, span);
                    insert_synthetic(p, &mut ordinal, lang.add_assign, cow_str, &[rhs], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
                }
            }
        }
        // `Borrow<B>` (map lookups of `Cow<str>` keys by `&str`),
        // `AsRef<B>`, and `Deref` to `B`: selection only, the calls
        // are `Builtin::CowDeref` (check/cow.rs).
        insert_synthetic(p, &mut ordinal, lang.borrow, cow_p0, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.as_ref, cow_p0, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.deref, cow_p0, &[], one.clone(), vec![(lang.assoc_target, p0)], Synthetic::Lang, false, span);
        for tr in [lang.debug, lang.display, lang.eq, lang.hash, lang.partial_eq, lang.partial_ord, lang.ord] {
            let mut g1 = one.clone();
            g1.predicates = pred_on_p0(p, tr);
            insert_synthetic(p, &mut ordinal, tr, cow_p0, &rhs_of(tr, cow_p0), g1, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // The std hashers and hashed collections (ty/hash.rs, W-STD-B), as
    // the std impl blocks state them. Traits without a port here
    // (PartialEq on the tables, Debug on DefaultHasher) reject.
    {
        use crate::ty::hash::{HashTy as H, mk_hash};
        let rs = mk_hash(&mut p.tys, H::RandomState, &[]);
        let dh = mk_hash(&mut p.tys, H::DefaultHasher, &[]);
        let bhd = mk_hash(&mut p.tys, H::BuildHasherDefault, &[p0]);
        insert_synthetic(p, &mut ordinal, lang.hasher, dh, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(
            p,
            &mut ordinal,
            lang.build_hasher,
            rs,
            &[],
            g0.clone(),
            vec![(lang.assoc_hasher, dh)],
            Synthetic::Lang,
            false,
            span,
        );
        let mut g1 = one.clone();
        g1.predicates = vec![pred_on(p, lang.default, p0), pred_on(p, lang.hasher, p0)];
        insert_synthetic(p, &mut ordinal, lang.build_hasher, bhd, &[], g1, vec![(lang.assoc_hasher, p0)], Synthetic::Lang, false, span);
        for tr in [lang.clone, lang.default] {
            insert_synthetic(p, &mut ordinal, tr, rs, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
            insert_synthetic(p, &mut ordinal, tr, dh, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
            insert_synthetic(p, &mut ordinal, tr, bhd, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.debug, rs, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        // HashMap<K, V, S> and HashSet<T, S>: Clone through every
        // param, Default through S, Debug through the elements.
        let p2 = p.tys.intern(TyKind::Param(ParamId(2)));
        let names = |p: &mut Program, ns: &[&str]| -> Vec<ParamDef> {
            ns.iter().map(|n| ParamDef { name: p.interner.intern(n), kind: ParamKind::Type, span }).collect()
        };
        let map = mk_hash(&mut p.tys, H::HashMap, &[p0, p1, p2]);
        let set = mk_hash(&mut p.tys, H::HashSet, &[p0, p1]);
        for (self_pat, params, elems, s) in
            [(map, names(p, &["K", "V", "S"]), vec![p0, p1], p2), (set, names(p, &["T", "S"]), vec![p0], p1)]
        {
            let g = |p: &mut Program, tr: DefId, on: &[Ty]| Generics {
                parent: None,
                params: params.clone(),
                predicates: on.iter().map(|&t| pred_on(p, tr, t)).collect(),
            };
            let mut all = elems.clone();
            all.push(s);
            let gc = g(p, lang.clone, &all);
            insert_synthetic(p, &mut ordinal, lang.clone, self_pat, &[], gc, Vec::new(), Synthetic::Lang, false, span);
            let gd = g(p, lang.default, &[s]);
            insert_synthetic(p, &mut ordinal, lang.default, self_pat, &[], gd, Vec::new(), Synthetic::Lang, false, span);
            let gf = g(p, lang.debug, &elems);
            insert_synthetic(p, &mut ordinal, lang.debug, self_pat, &[], gf, Vec::new(), Synthetic::Lang, false, span);
            // PartialEq and Eq (Rhs = Self): the keys `Eq + Hash`, a
            // map's values PartialEq (Eq), `S: BuildHasher`.
            for tr in [lang.partial_eq, lang.eq] {
                let rhs = |p: &mut Program, tr: DefId, t: Ty| {
                    let mut a = vec![GenericArg::Ty(t)];
                    if tr == lang.partial_eq {
                        a.push(GenericArg::Ty(t));
                    }
                    let args = p.tys.intern_args(&a);
                    Predicate::Trait(Binder::plain(TraitRef { def: tr, args, bindings: EMPTY_BINDINGS }))
                };
                let mut preds = vec![pred_on(p, lang.eq, elems[0]), pred_on(p, lang.hash, elems[0]), pred_on(p, lang.build_hasher, s)];
                if let Some(&v) = elems.get(1) {
                    preds.push(rhs(p, tr, v));
                }
                let ge = Generics { parent: None, params: params.clone(), predicates: preds };
                let rest: Vec<Ty> = if tr == lang.partial_eq { vec![self_pat] } else { Vec::new() };
                insert_synthetic(p, &mut ordinal, tr, self_pat, &rest, ge, Vec::new(), Synthetic::Lang, false, span);
            }
        }
    }
    // The IntoIterator blanket: impl<I: Iterator> IntoIterator
    // for I, Item = I::Item, IntoIter = I.
    {
        let preds = pred_on_p0(p, lang.iterator);
        let mut g1 = one.clone();
        g1.predicates = preds;
        let item_args = p.tys.intern_args(&[GenericArg::Ty(p0)]);
        let item_proj = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_item), item_args));
        insert_synthetic(
            p,
            &mut ordinal,
            lang.into_iterator,
            p0,
            &[],
            g1,
            vec![(lang.assoc_into_item, item_proj), (lang.assoc_into_iter, p0)],
            Synthetic::Lang,
            false,
            span,
        );
    }
    // The std::sync and std::thread types (W-THREADS, check/sync.rs).
    crate::check::sync::add_sync_impls(p, &mut ordinal, span);
    crate::check::own::add_own_impls(p, &mut ordinal, span);
    // core's `impl<T: 'static + ?Sized> Any for T` (check/any.rs). The
    // `'static` bound is a region fact: selection ignores it, as rustc's
    // probe does, and the checker and the borrow checker prove it.
    {
        let mut g1 = one.clone();
        g1.predicates = vec![Predicate::TypeOutlives(p0, Region::Static)];
        insert_synthetic(p, &mut ordinal, lang.any, p0, &[], g1, Vec::new(), Synthetic::Lang, false, span);
    }
    // IntoIterator for the hash maps and sets with their references
    // (W-STD-B; Vec and slices are in the block above). Selection and
    // Item/IntoIter only; `into_iter` and `for` stay builtin.
    {
        use crate::ty::hash::{HashTy, mk_hash};
        use crate::ty::iter::{IterKind as K, mk_iter};
        let two = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("K"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("V"), kind: ParamKind::Type, span },
            ],
            predicates: Vec::new(),
        };
        let three = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("K"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("V"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("S"), kind: ParamKind::Type, span },
            ],
            predicates: Vec::new(),
        };
        let p2 = p.tys.intern(TyKind::Param(ParamId(2)));
        let ref_p0 = p.tys.mk_ref(false, p0);
        // HashMap<K, V, S> by value, `&`, `&mut`; HashSet<T, S> by value, `&`.
        let map = mk_hash(&mut p.tys, HashTy::HashMap, &[p0, p1, p2]);
        let ref_map = p.tys.mk_ref(false, map);
        let mut_map = p.tys.mk_ref(true, map);
        let ref_p1 = p.tys.mk_ref(false, p1);
        let mut_p1 = p.tys.mk_ref(true, p1);
        let tup = |p: &mut Program, a: Ty, b: Ty| {
            let ts = p.tys.intern_tys(&[a, b]);
            p.tys.intern(TyKind::Tuple(ts))
        };
        let maps = [
            (map, tup(p, p0, p1), K::MapIntoIter),
            (ref_map, tup(p, ref_p0, ref_p1), K::MapIter),
            (mut_map, tup(p, ref_p0, mut_p1), K::MapIterMut),
        ];
        for (s, item, k) in maps {
            let iter = mk_iter(&mut p.tys, k, &[p0, p1]);
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, iter)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, s, &[], three.clone(), assoc, Synthetic::Lang, false, span);
        }
        let set = mk_hash(&mut p.tys, HashTy::HashSet, &[p0, p1]);
        let ref_set = p.tys.mk_ref(false, set);
        for (s, item, k) in [(set, p0, K::SetIntoIter), (ref_set, ref_p0, K::SetIter)] {
            let iter = mk_iter(&mut p.tys, k, &[p0]);
            let assoc = vec![(lang.assoc_into_item, item), (lang.assoc_into_iter, iter)];
            insert_synthetic(p, &mut ordinal, lang.into_iterator, s, &[], two.clone(), assoc, Synthetic::Lang, false, span);
        }
        // std's `Extend` impls of the builtin collections, for bounds
        // (`M: Extend<<M as IntoIterator>::Item>` in ts-rust's
        // copy_map_into); a call on a concrete collection stays its
        // builtin (check/extend.rs, check/hashmap.rs).
        let bound = |p: &mut Program, tr: DefId, t: Ty| {
            let a = p.tys.intern_args(&[GenericArg::Ty(t)]);
            Predicate::Trait(Binder::plain(TraitRef { def: tr, args: a, bindings: EMPTY_BINDINGS }))
        };
        let with = |g: &Generics, preds: Vec<Predicate>| Generics { predicates: preds, ..g.clone() };
        let one_t = Generics { parent: None, params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }], predicates: Vec::new() };
        let vec_p0 = p.tys.mk_vec(p0);
        insert_synthetic(p, &mut ordinal, lang.extend, vec_p0, &[p0], one_t.clone(), Vec::new(), Synthetic::Lang, false, span);
        let copy_p0 = bound(p, lang.copy, p0);
        insert_synthetic(p, &mut ordinal, lang.extend, vec_p0, &[ref_p0], with(&one_t, vec![copy_p0]), Vec::new(), Synthetic::Lang, false, span);
        let ref_char = p.tys.mk_ref(false, CHAR);
        let box_str = p.tys.mk_boxed(STR);
        let mut string_items = vec![CHAR, ref_char, REF_STR, STRING, box_str];
        if let Some(cow) = p.tys.local_adt_of(cow_def()).map(|_| p.tys.mk_adt(cow_def(), &[GenericArg::Ty(STR)])) {
            string_items.push(cow);
        }
        for item in string_items {
            insert_synthetic(p, &mut ordinal, lang.extend, STRING, &[item], Generics::default(), Vec::new(), Synthetic::Lang, false, span);
        }
        let (eq0, hash0, copy1, bh2) = (bound(p, lang.eq, p0), bound(p, lang.hash, p0), bound(p, lang.copy, p1), bound(p, lang.build_hasher, p2));
        let kv = tup(p, p0, p1);
        let ref_p1 = p.tys.mk_ref(false, p1);
        let kv_ref = tup(p, ref_p0, ref_p1);
        insert_synthetic(p, &mut ordinal, lang.extend, map, &[kv], with(&three, vec![eq0, hash0, bh2]), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.extend, map, &[kv_ref], with(&three, vec![eq0, hash0, copy_p0, copy1, bh2]), Vec::new(), Synthetic::Lang, false, span);
        let bh1 = bound(p, lang.build_hasher, p1);
        insert_synthetic(p, &mut ordinal, lang.extend, set, &[p0], with(&two, vec![eq0, hash0, bh1]), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.extend, set, &[ref_p0], with(&two, vec![eq0, hash0, copy_p0, bh1]), Vec::new(), Synthetic::Lang, false, span);
    }
}

/// An owned snapshot of a type from any store (see `lift_ty`).
/// A body overlay borrows the global store, so a type cannot be
/// lifted by walking it while interning into the globals; the
/// snapshot breaks that borrow. It names defs by `DefId`, so it also
/// outlives the program: the driver's generic reuse cache keeps
/// discovery output in this form across requests (driver/gen_reuse.rs).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum OwnedTy {
    Leaf(TyKind),
    Ref(Region, Mut, Box<OwnedTy>),
    RawPtr(Mut, Box<OwnedTy>),
    Slice(Box<OwnedTy>),
    Array(Box<OwnedTy>, ConstKind),
    Tuple(Vec<OwnedTy>),
    Adt(DefId, Vec<OwnedArg>),
    FnDef(DefId, Vec<OwnedArg>),
    Closure(DefId, Vec<OwnedArg>),
    Opaque(DefId, Vec<OwnedArg>),
    Projection(AssocId, Vec<OwnedArg>),
    FnPtr(Binder<FnSig>, Vec<OwnedTy>, Box<OwnedTy>),
    /// The principal def, args, and bindings (only the `Output` of the
    /// Fn-family sugar; supertraits are always empty in a dyn type
    /// `resolve_dyn` forms), auto bits, region.
    Dyn(Option<(DefId, Vec<OwnedArg>, Vec<(DefId, OwnedArg)>)>, AutoTraits, Region),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum OwnedArg {
    Ty(OwnedTy),
    Lifetime(Region),
    Const(ConstKind),
}

/// Copies one body type out of its store, or None when it still
/// holds an inference variable or the error type (a variable the
/// zonk could not resolve): such a type names no instance, and the
/// body that made it has an error report of its own.
pub(crate) fn snapshot_ty(src: &dyn TyIntern, t: Ty) -> Option<OwnedTy> {
    // A type past rustc's type-length limit is never an instance arg
    // rustc builds (its post-mono error), and as an owned tree a type
    // that doubles its args per level is exponential: no snapshot.
    if over_type_length(src, t) {
        return None;
    }
    snapshot_ty_tree(src, t)
}

/// rustc's default `type_length_limit`: an instance whose args walk
/// more nodes than this is a build error.
pub(crate) const TYPE_LENGTH_LIMIT: u64 = 1_048_576;

/// True when `t` walks more than `TYPE_LENGTH_LIMIT` nodes as a tree.
/// Small types answer from a bounded walk; a large one is counted
/// once per distinct node.
pub(crate) fn over_type_length(src: &dyn TyIntern, t: Ty) -> bool {
    fn bounded(src: &dyn TyIntern, t: Ty, budget: &mut u32) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        ty_children(src, t).into_iter().all(|e| bounded(src, e, budget))
    }
    fn length(src: &dyn TyIntern, t: Ty, memo: &mut FxMap<Ty, u64>) -> u64 {
        if let Some(&n) = memo.get(&t) {
            return n;
        }
        let n = ty_children(src, t).into_iter().fold(1u64, |acc, e| acc.saturating_add(length(src, e, memo)));
        memo.insert(t, n);
        n
    }
    if bounded(src, t, &mut 4096) {
        return false;
    }
    length(src, t, &mut FxMap::default()) > TYPE_LENGTH_LIMIT
}

/// The type arguments and parts one level inside `t`.
fn ty_children(src: &dyn TyIntern, t: Ty) -> Vec<Ty> {
    match src.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => vec![e],
        TyKind::Tuple(ts) => src.tys_of(ts).to_vec(),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
            src.args(a).iter().filter_map(|g| g.as_ty()).collect()
        }
        TyKind::FnPtr(sig) => {
            let s = src.sig(sig).value;
            src.tys_of(s.inputs).iter().copied().chain([s.output]).collect()
        }
        _ => Vec::new(),
    }
}

/// `snapshot_ty` without the length check.
fn snapshot_ty_tree(src: &dyn TyIntern, t: Ty) -> Option<OwnedTy> {
    Some(match src.kind(t) {
        TyKind::Infer(_) | TyKind::Error => return None,
        TyKind::Ref(r, m, e) => OwnedTy::Ref(r, m, Box::new(snapshot_ty_tree(src, e)?)),
        TyKind::RawPtr(m, e) => OwnedTy::RawPtr(m, Box::new(snapshot_ty_tree(src, e)?)),
        TyKind::Slice(e) => OwnedTy::Slice(Box::new(snapshot_ty_tree(src, e)?)),
        TyKind::Array(e, n) => match src.const_kind(n) {
            ConstKind::Infer(_) => return None,
            k => OwnedTy::Array(Box::new(snapshot_ty_tree(src, e)?), k),
        },
        TyKind::Tuple(ts) => {
            let mut out = Vec::new();
            for e in src.tys_of(ts).to_vec() {
                out.push(snapshot_ty_tree(src, e)?);
            }
            OwnedTy::Tuple(out)
        }
        TyKind::Adt(d, a) => OwnedTy::Adt(d, snapshot_args(src, a)?),
        TyKind::FnDef(d, a) => OwnedTy::FnDef(d, snapshot_args(src, a)?),
        TyKind::Closure(d, a) => OwnedTy::Closure(d, snapshot_args(src, a)?),
        TyKind::Opaque(d, a) => OwnedTy::Opaque(d, snapshot_args(src, a)?),
        TyKind::Projection(d, a) => OwnedTy::Projection(d, snapshot_args(src, a)?),
        TyKind::FnPtr(sig) => {
            let b = src.sig(sig);
            let mut inputs = Vec::new();
            for e in src.tys_of(b.value.inputs).to_vec() {
                inputs.push(snapshot_ty_tree(src, e)?);
            }
            let output = Box::new(snapshot_ty_tree(src, b.value.output)?);
            // The ids of the sig's own inputs and output are the source
            // store's (a body overlay's are new at each check); the owned
            // trees hold them, and `build_owned_ty` reads only those.
            let b = Binder { count: b.count, value: FnSig { inputs: EMPTY_TYS, output: ERROR, ..b.value } };
            OwnedTy::FnPtr(b, inputs, output)
        }
        TyKind::Dyn(b, r) => {
            let bounds = src.dyn_bounds(b).clone();
            let principal = match bounds.principal {
                // Slot 0 is the erased Self (`DYN_SELF`, the error type by
                // design), kept as is: only the args after it must be known.
                Some(pr) => {
                    let mut args = vec![OwnedArg::Ty(OwnedTy::Leaf(TyKind::Error))];
                    for g in src.args(pr.value.args)[1..].to_vec() {
                        args.push(snapshot_arg(src, g)?);
                    }
                    let mut bindings = Vec::new();
                    for (d, g) in src.bindings(pr.value.bindings).to_vec() {
                        bindings.push((d, snapshot_arg(src, g)?));
                    }
                    Some((pr.value.def, args, bindings))
                }
                None => None,
            };
            OwnedTy::Dyn(principal, bounds.auto, r)
        }
        kind => OwnedTy::Leaf(kind),
    })
}

fn snapshot_args(src: &dyn TyIntern, a: ArgsId) -> Option<Vec<OwnedArg>> {
    src.args(a).to_vec().into_iter().map(|g| snapshot_arg(src, g)).collect()
}

fn snapshot_arg(src: &dyn TyIntern, g: GenericArg) -> Option<OwnedArg> {
    Some(match g {
        GenericArg::Ty(e) => OwnedArg::Ty(snapshot_ty(src, e)?),
        GenericArg::Const(c) => match src.const_kind(c) {
            ConstKind::Infer(_) => return None,
            k => OwnedArg::Const(k),
        },
        GenericArg::Lifetime(r) => OwnedArg::Lifetime(r),
    })
}

pub(crate) fn build_owned_ty(p: &mut Program, t: &OwnedTy) -> Ty {
    match t {
        OwnedTy::Leaf(kind) => p.tys.intern(*kind),
        OwnedTy::Ref(r, m, e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::Ref(*r, *m, e))
        }
        OwnedTy::RawPtr(m, e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::RawPtr(*m, e))
        }
        OwnedTy::Slice(e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::Slice(e))
        }
        OwnedTy::Array(e, k) => {
            let e = build_owned_ty(p, e);
            let n = p.tys.intern_const(*k);
            p.tys.intern(TyKind::Array(e, n))
        }
        OwnedTy::Tuple(elems) => {
            let out: Vec<Ty> = elems.iter().map(|e| build_owned_ty(p, e)).collect();
            let ts = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(ts))
        }
        OwnedTy::Adt(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Adt(*d, a))
        }
        OwnedTy::FnDef(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::FnDef(*d, a))
        }
        OwnedTy::Closure(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Closure(*d, a))
        }
        OwnedTy::Opaque(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Opaque(*d, a))
        }
        OwnedTy::Projection(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Projection(*d, a))
        }
        OwnedTy::FnPtr(b, inputs, output) => {
            let out: Vec<Ty> = inputs.iter().map(|e| build_owned_ty(p, e)).collect();
            let inputs_id = p.tys.intern_tys(&out);
            let output = build_owned_ty(p, output);
            let sig = p.tys.intern_sig(Binder { count: b.count, value: FnSig { inputs: inputs_id, output, ..b.value } });
            p.tys.intern(TyKind::FnPtr(sig))
        }
        OwnedTy::Dyn(principal, auto, r) => {
            let principal = principal.as_ref().map(|(def, args, bindings)| {
                let args = build_owned_args(p, args);
                let bindings: Vec<(DefId, GenericArg)> = bindings.iter().map(|(d, g)| (*d, build_owned_arg(p, g))).collect();
                let bindings = p.tys.intern_bindings(&bindings);
                Binder::plain(TraitRef { def: *def, args, bindings })
            });
            let b = p.tys.intern_dyn_bounds(DynBounds { principal, supertraits: Box::new([]), auto: *auto });
            p.tys.intern(TyKind::Dyn(b, *r))
        }
    }
}

fn build_owned_args(p: &mut Program, args: &[OwnedArg]) -> ArgsId {
    let out: Vec<GenericArg> = args.iter().map(|a| build_owned_arg(p, a)).collect();
    p.tys.intern_args(&out)
}

fn build_owned_arg(p: &mut Program, a: &OwnedArg) -> GenericArg {
    match a {
        OwnedArg::Ty(e) => GenericArg::Ty(build_owned_ty(p, e)),
        OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
        OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
    }
}

/// Lifts one type from a body-local store into the program's
/// global store (the owned type store lift of ARCH 2.1, in its
/// structural form). None when the type still contains an
/// inference variable (the request that named it is not
/// concrete yet).
// Used by ensure_adt_instances_in below; both are kept for the
// cross-store mono wiring that lands after this increment.
#[allow(dead_code)]
pub fn lift_ty(p: &mut Program, src: &dyn TyIntern, t: Ty) -> Option<Ty> {
    let owned = snapshot_ty(src, t)?;
    Some(build_owned_ty(p, &owned))
}

/// Finds the global type structurally equal to a body-local type.
fn find_global_ty(p: &Program, src: &dyn TyIntern, t: Ty) -> Option<Ty> {
    let g = &p.tys;
    Some(match src.kind(t) {
        TyKind::Ref(r, m, e) => g.get(TyKind::Ref(r, m, find_global_ty(p, src, e)?))?,
        TyKind::RawPtr(m, e) => g.get(TyKind::RawPtr(m, find_global_ty(p, src, e)?))?,
        TyKind::Slice(e) => g.get(TyKind::Slice(find_global_ty(p, src, e)?))?,
        TyKind::Array(e, n) => {
            let n = match src.const_kind(n) {
                ConstKind::Infer(_) => return None,
                k => g.consts_get(k)?,
            };
            g.get(TyKind::Array(find_global_ty(p, src, e)?, n))?
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = src.tys_of(ts).to_vec();
            let mut out = Vec::new();
            for e in elems {
                out.push(find_global_ty(p, src, e)?);
            }
            let ts = g.get_tys(&out)?;
            g.get(TyKind::Tuple(ts))?
        }
        TyKind::Adt(d, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            let mut out: Vec<GenericArg> = Vec::new();
            for gg in raw {
                out.push(match gg {
                    GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                    GenericArg::Const(c) => match src.const_kind(c) {
                        ConstKind::Infer(_) => return None,
                        k => GenericArg::Const(g.consts_get(k)?),
                    },
                    other => other,
                });
            }
            let aid = g.get_args(&out)?;
            g.get(TyKind::Adt(d, aid))?
        }
        TyKind::Projection(d, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            let mut out: Vec<GenericArg> = Vec::new();
            for gg in raw {
                out.push(match gg {
                    GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                    other => other,
                });
            }
            let aid = g.get_args(&out)?;
            g.get(TyKind::Projection(d, aid))?
        }
        TyKind::Dyn(b, r) => {
            let bounds = src.dyn_bounds(b).clone();
            let principal = match bounds.principal {
                Some(pr) => {
                    let raw: Vec<GenericArg> = src.args(pr.value.args).to_vec();
                    let mut out: Vec<GenericArg> = Vec::new();
                    for gg in raw {
                        out.push(match gg {
                            GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                            GenericArg::Const(c) => match src.const_kind(c) {
                                ConstKind::Infer(_) => return None,
                                k => GenericArg::Const(g.consts_get(k)?),
                            },
                            other => other,
                        });
                    }
                    let mut bs: Vec<(DefId, GenericArg)> = Vec::new();
                    for (d, gg) in src.bindings(pr.value.bindings).to_vec() {
                        bs.push((
                            d,
                            match gg {
                                GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                                other => other,
                            },
                        ));
                    }
                    let bindings = if bs.is_empty() { EMPTY_BINDINGS } else { g.bindings_get(&bs)? };
                    Some(Binder { count: pr.count, value: TraitRef { def: pr.value.def, args: g.get_args(&out)?, bindings } })
                }
                None => None,
            };
            let gb = g.dyn_bounds_get(&DynBounds { principal, supertraits: Box::new([]), auto: bounds.auto })?;
            g.get(TyKind::Dyn(gb, r))?
        }
        kind => g.get(kind)?,
    })
}

/// The vtable mono made for one unsizing coercion, from body-local
/// types: the concrete pointee and the target dyn type.
pub fn vtable_for(p: &Program, src: &dyn TyIntern, concrete: Ty, dyn_ty: Ty) -> Option<u32> {
    let concrete = find_global_ty(p, src, concrete)?;
    // The principal alone keys the vtable, so the dyn type itself need
    // not be in the global store: mono cannot check a body that uses a
    // static (`&X as &(dyn Tr + 'static)`), and then only the eager
    // vtable of a plain impl exists for it.
    let TyKind::Dyn(b, _) = src.kind(dyn_ty) else { return None };
    let Some(pr) = src.dyn_bounds(b).principal.map(|pr| pr.value) else {
        return p.gx.vtable_by_key.get(&(concrete, crate::check::object::auto_only_key(p))).copied();
    };
    let mut args: Vec<GenericArg> = Vec::new();
    for g in src.args(pr.args).to_vec() {
        args.push(match g {
            GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
            GenericArg::Const(c) => match src.const_kind(c) {
                ConstKind::Infer(_) => return None,
                k => GenericArg::Const(p.tys.consts_get(k)?),
            },
            other => other,
        });
    }
    let principal = TraitRef { def: pr.def, args: p.tys.get_args(&args)?, bindings: EMPTY_BINDINGS };
    p.gx.vtable_by_key.get(&(concrete, principal)).copied()
}

/// Selects the impl of one concrete trait ref over the global store,
/// with its args lifted into the global store. None unless exactly one
/// impl applies.
pub(crate) fn select_impl_global(p: &mut Program, tr: TraitRef) -> Option<(crate::traits::ImplId, Vec<GenericArg>)> {
    let (id, owned) = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        let Selection::Impl { id, args, .. } = solver.select(&mut cx, &p.gx.index, &[], tr) else { return None };
        let mut owned: Vec<OwnedArg> = Vec::new();
        for g in args {
            owned.push(match g {
                GenericArg::Ty(t) => OwnedArg::Ty(snapshot_ty(&cx.tys, t)?),
                GenericArg::Const(c) => match cx.tys.const_kind(c) {
                    ConstKind::Infer(_) => return None,
                    k => OwnedArg::Const(k),
                },
                GenericArg::Lifetime(r) => OwnedArg::Lifetime(r),
            });
        }
        (id, owned)
    };
    let args: Vec<GenericArg> = owned
        .iter()
        .map(|a| match a {
            OwnedArg::Ty(t) => GenericArg::Ty(build_owned_ty(p, t)),
            OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
            OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
        })
        .collect();
    Some((id, args))
}

/// The concrete fn for one callable template or plain fn at `args`:
/// the plain fn itself, or its instance (pushed on `made` when new).
pub(crate) fn instance_at(p: &mut Program, f: LocalDefId, args: &[GenericArg], made: &mut Vec<LocalDefId>) -> LocalDefId {
    if p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
        return f;
    }
    let before = p.fns.len();
    let inst = fn_instance(p, f, args);
    if inst.0 as usize >= before {
        made.push(inst);
    }
    inst
}

/// The mono instance for one template and body-local args, as
/// lowering needs it. Compares candidate instance args (global)
/// against the lifted body args structurally.
pub fn instance_for(p: &Program, src: &dyn TyIntern, template: LocalDefId, args: &[GenericArg]) -> Option<LocalDefId> {
    let template_def = p.def_id(template);
    // Lift each arg by structural find; tuple args fall back to a
    // direct comparison against every instance of this template.
    let mut lifted: Vec<GenericArg> = Vec::new();
    for &g in args {
        match g {
            GenericArg::Ty(e) => lifted.push(GenericArg::Ty(find_global_ty(p, src, e)?)),
            other => lifted.push(other),
        }
    }
    // The global store hash-conses arg lists, so equal args are one id:
    // a direct lookup finds what a scan of every instance would.
    let args_id = p.tys.get_args(&lifted)?;
    p.gx.instance_by_key.get(&(template_def, args_id)).copied()
}

/// One signature fn per method of each trait a template's env names,
/// for the calls a template check proves through its param env
/// (`t.m()` with `T: Tr` in the bounds, no impl to select). It is the callee that lowering and borrowck
/// see in template bodies, and the trait method that instance checks
/// replay as a pick. Its generics are the trait's (Self first), then
/// the method's own; its signature is the trait method's. Stubs are
/// never checked, instantiated, or generated.
fn add_trait_method_stubs(p: &mut Program) {
    // Only a trait some template's env names can prove a call there:
    // stubs of other traits would only take driver slots.
    let mut bound: Vec<DefId> = Vec::new();
    for (i, class) in p.gx.fn_class.iter().enumerate() {
        if *class == FnClass::Template {
            for pred in &p.gx.fn_scopes[i].env {
                if let Predicate::Trait(b) = pred
                    && !bound.contains(&b.value.def)
                {
                    bound.push(b.value.def);
                }
            }
        }
    }
    // The bounds of `impl Trait` returns prove calls in their callers'
    // opaque views (check/opaque.rs), supertraits included.
    let opaque_bounds: Vec<Predicate> = p.gx.opaques.values().flat_map(|o| o.bounds.iter().copied()).collect();
    for pred in crate::traits::solve::elaborate_in(&mut p.tys, &p.gx.index, &opaque_bounds) {
        if let Predicate::Trait(b) = pred
            && !bound.contains(&b.value.def)
        {
            bound.push(b.value.def);
        }
    }
    // A `for` loop over an `IntoIterator` bound also calls
    // `Iterator::next` on the `IntoIter` projection; no env
    // predicate names `Iterator` there (assoc-type bounds of a
    // trait definition are not elaborated), so stub it too.
    if bound.contains(&p.gx.lang.into_iterator) && !bound.contains(&p.gx.lang.iterator) {
        bound.push(p.gx.lang.iterator);
    }
    // `T: Display` gives `t.to_string()` through core's blanket ToString.
    if bound.contains(&p.gx.lang.display) && !bound.contains(&p.gx.lang.to_string) {
        bound.push(p.gx.lang.to_string);
    }
    let mut methods: Vec<(DefId, DefId, Sym)> = Vec::new();
    for traits in p.gx.traits_by_method.values() {
        for &t in traits {
            if !bound.contains(&t) {
                continue;
            }
            if let Some(rec) = p.gx.index.trait_record(t) {
                for &(m, name) in &rec.methods {
                    if !methods.iter().any(|x| x.1 == m) {
                        methods.push((t, m, name));
                    }
                }
            }
        }
    }
    methods.sort_by_key(|x| x.1.hash.0);
    for (trait_def, method_def, name) in methods {
        let (def, self_kind, params, ret, ret_borrows_from, generics) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => (t.loc, t.self_kind, t.params.clone(), t.ret, t.ret_borrows_from, t.generics.clone()),
            None => {
                // A lang trait method: its signature comes from the
                // table built out of the lang trait records.
                let Some(sig) = p.gx.lang_method_sigs.get(&method_def).cloned() else { continue };
                let (self_kind, params, ret, rb) = (sig.self_kind, sig.params, sig.ret, sig.ret_borrows_from);
                let Some(rec) = p.gx.index.trait_record(trait_def) else { continue };
                let generics = Generics { parent: None, params: rec.generics.params.clone(), predicates: Vec::new() };
                // Lang methods have no AST def; stubs are never
                // checked, so any def stands in for the FnInfo slot.
                let Some(any_def) = p.fns.first().map(|f| f.loc) else { return };
                (any_def, self_kind, params, ret, rb, generics)
            }
        };
        let id = LocalDefId(p.fns.len() as u32);
        let def_id = DefId {
            krate: p.krate,
            hash: crate::def::item_hash(p.stable_crate, &["<stub>"], crate::def::DefKind::Method, &format!("{}", method_def.hash.0), 0),
        };
        p.fn_defs.push(def_id);
        p.def_by_hash.entry(def_id.hash).or_insert(id);
        p.fns.push(crate::check::collect::FnInfo {
            name,
            loc: def,
            owner: None,
            self_kind,
            params,
            ret,
            ret_borrows_from,
            is_const: false,
        });
        p.gx.fn_templates.push(Some(FnTemplate { generics, env: Vec::new() }));
        p.gx.fn_scopes.push(FnScope::default());
        p.gx.fn_class.push(FnClass::Stub);
        p.gx.trait_method_stubs.insert(method_def, id);
    }
}

/// The template check (ARCH 4.1): every generic fn, method, and
/// trait default body is checked once as written, against its param
/// env. Its `Param` and projection types are rigid: they have exactly
/// the traits the bounds give them (`Tys::env`), they have no layout,
/// and const params stay symbolic. Each body is borrow-checked too: a
/// second move of a non-Copy param, or a call through an `FnMut`
/// bound on an immutable binding, is the template error this pass
/// exists to catch. A call the env proves resolves to the trait
/// method's stub, and its pick is recorded for the instances.
/// Closure templates are checked in place by their enclosing body.
fn template_check(p: &mut Program) -> Vec<Diag> {
    let mut templates: Vec<LocalDefId> =
        (0..p.fns.len() as u32).map(LocalDefId).filter(|&f| p.gx.fn_class.get(f.0 as usize) == Some(&FnClass::Template)).collect();
    // A generic fn with its own `impl Trait` return checks first: a body
    // that uses the opaque value asks for its hidden type's auto traits
    // (`Send` leakage), wherever the definer sits in the source.
    templates.sort_by_key(|&f| !p.gx.opaques.contains_key(&opaque_def(p.def_id(f))));
    for &t in &templates {
        p.gx.template_checks.insert(t, t);
    }
    let mut errs: Vec<Diag> = Vec::new();
    let mut reuse = std::mem::take(&mut p.gx.reuse);
    // The lang enum methods (checked when the library was built) check
    // only when mono makes their first instance (`materialize`): a
    // compile splices all of them and instantiates a few. A std platform
    // template in `lust check` (`Program::check_skips`) does not check,
    // unless callers need the hidden type of its `impl Trait`.
    templates.retain(|&t| !p.is_lang_method(t) && (!p.check_skips(t) || p.gx.opaques.contains_key(&opaque_def(p.def_id(t)))));
    // A template whose check only reads the program (no closures to
    // register, no hidden type of its own) checks ahead in a window, as
    // discovery bodies do (`Ahead`); its writes go in at its turn.
    let mut ahead: Ahead<TemplateBody> = Ahead::new(!p.record_reads && !reuse.on, false);
    ahead.start(templates.len());
    for (k, &t) in templates.iter().enumerate() {
        crate::driver::graph::FpMemo::sync(p);
        let reads_only = |p: &Program, t: LocalDefId| !fn_has_closures(p, t) && !p.gx.opaques.contains_key(&opaque_def(p.def_id(t)));
        ahead.fill(&templates, k, |i| reads_only(p, templates[i]), |&t| template_body(p, t, &[]));
        match ahead.take(&p.gx.anon_wants, k) {
            Some(body) => errs.extend(finish_template(p, t, &mut reuse, body, &[], &Vec::new())),
            None => errs.extend(check_template(p, t, &mut reuse)),
        }
    }
    ahead.end();
    ahead.report("templates");
    p.gx.reuse = reuse;
    errs
}

/// Checks every lang enum method template now (std load's validation
/// of library/core; a compile checks them lazily, see `template_check`).
pub fn check_lang_templates(p: &mut Program) -> Vec<Diag> {
    let mut reuse = std::mem::take(&mut p.gx.reuse);
    let mut errs = Vec::new();
    for f in (0..p.fns.len() as u32).map(LocalDefId) {
        if p.gx.fn_class.get(f.0 as usize) == Some(&FnClass::Template) && p.is_lang_method(f) {
            errs.extend(check_template(p, f, &mut reuse));
        }
    }
    p.gx.reuse = reuse;
    errs
}

/// One template's check against its param env (see `template_check`):
/// its picks, closure call kinds, and closure bodies are recorded for
/// its instances. Returns the check's errors.
pub(crate) fn check_template(p: &mut Program, t: LocalDefId, reuse: &mut crate::driver::gen_reuse::GenReuse) -> Vec<Diag> {
    // A template whose stored check still holds (driver session
    // reuse) contributes its picks and closure call kinds without
    // a recheck; one with closure expressions also makes its closure
    // body fns again from the stored records (below). An opaque
    // definer always rechecks: its check sets the hidden types.
    crate::driver::graph::FpMemo::sync(p);
    let defines_opaque = p.gx.opaques.contains_key(&opaque_def(p.def_id(t)));
    if !defines_opaque && let Some((picks, calls)) = reuse.template(p, t) {
        reuse.note_template_out(p, t, &picks, &calls, &[]);
        p.gx.trait_picks.extend(picks);
        record_template_closures(p, t, Vec::new(), calls);
        return Vec::new();
    }
    let has_closures = fn_has_closures(p, t);
    // A body with closures whose stored check holds replays it as well:
    // its closures' records make their body fns again, as the check does.
    if !defines_opaque
        && has_closures
        && let Some((picks, calls, shapes, owned)) = reuse.closure_template(p, t)
    {
        reuse.note_template_out(p, t, &picks, &calls, &shapes);
        record_template_closures(p, t, shapes, calls);
        register_closures(p, t, owned, FnClass::TemplateClosure);
        p.gx.trait_picks.extend(picks);
        return Vec::new();
    }
    // Closures first: their body fns must exist before the body
    // lowers (its closure calls name them), and the capture
    // analysis is recorded for the instances. Only bodies with
    // closure expressions pay this extra check.
    let mut closure_fns: Vec<LocalDefId> = Vec::new();
    let mut template_shapes: ClosureShapes = Vec::new();
    let mut closure_records: Vec<OwnedClosure> = Vec::new();
    // The closure pass reads derive lists too (capture modes): its notes
    // join the reads the derive delta compares for this template.
    let ((), closure_noted) = crate::check::derive_delta::scoped(p.record_reads && has_closures, || {
        if has_closures {
            let (owned, shapes) = {
                let (c, _) = crate::check::check_fn(p, t);
                (snapshot_closures(&c), closure_shapes(&c))
            };
            template_shapes.clone_from(&shapes);
            record_template_closures(p, t, shapes, Vec::new());
            if let Some(owned) = owned {
                closure_records.clone_from(&owned);
                closure_fns = register_closures(p, t, owned, FnClass::TemplateClosure);
            }
        }
    });
    let mut body = template_body(p, t, &closure_fns);
    if has_closures {
        crate::check::derive_delta::record(p, &mut body.reads, &closure_noted);
        reuse.store_closure_template(p, t, body.errs.is_empty().then_some(&body.reads));
    }
    // What a replay of this clean check needs (`GenReuse::closure_template`).
    let replay = (has_closures && !defines_opaque && body.errs.is_empty()).then(|| (body.picks.clone(), body.calls.clone()));
    let errs = finish_template(p, t, reuse, body, &closure_fns, &template_shapes);
    if let Some((picks, calls)) = replay {
        reuse.store_closure_template_out(p, t, &picks, &calls, &template_shapes, &closure_records);
    }
    errs
}

/// The part of a template check that only reads the program: the body
/// check, its lowering and borrowck, and those of its closure bodies
/// `closure_fns`. The derive delta runs several at once
/// (driver/kept_derive.rs); `finish_template` writes the result.
pub(crate) struct TemplateBody {
    errs: Vec<Diag>,
    picks: Vec<(ast::ExprId, crate::check::picks::TraitPick)>,
    calls: Vec<(ast::ExprId, crate::check::closure::ClosureKind)>,
    reads: crate::driver::graph::Reads,
    hidden: Vec<(DefId, OwnedTy)>,
}

impl TemplateBody {
    /// True when the body check reported an error (no write done yet).
    pub(crate) fn failed(&self) -> bool {
        !self.errs.is_empty()
    }
}

/// `check_template`'s body check of template `t` (see `TemplateBody`).
pub(crate) fn template_body(p: &Program, t: LocalDefId, closure_fns: &[LocalDefId]) -> TemplateBody {
    // Lowering, borrowck and check_fn's tail passes read derive lists too
    // (Copy operands, moves): their notes join the stored reads, as in the
    // compile tail, so a derive toggle checks the template again.
    let ((errs, picks, calls, mut reads, hidden), noted) = crate::check::derive_delta::scoped(p.record_reads, || {
        let (c, mut e) = crate::check::check_fn(p, t);
        let picks = c.trait_picks.clone();
        let hidden: Vec<(DefId, OwnedTy)> =
            c.opaque_hidden.iter().filter_map(|&(od, h)| snapshot_ty(&c.tys, h).map(|o| (od, o))).collect();
        let calls = c.closure_calls.clone();
        let mut reads = c.reads.clone();
        if e.is_empty() {
            let body = crate::lower::lower(p, t, c);
            e.extend(crate::borrowck::borrowck(p, &body));
            for &cf in closure_fns {
                let (cc, _) = crate::check::check_fn(p, cf);
                cc.reads.iter(crate::driver::graph::ReadKeys::none()).for_each(|(k, r)| reads.record(*k, r.fingerprint, r.failed));
                let cbody = crate::lower::lower(p, cf, cc);
                e.extend(crate::borrowck::borrowck(p, &cbody));
            }
        }
        (e, picks, calls, reads, hidden)
    });
    crate::check::derive_delta::record(p, &mut reads, &noted);
    TemplateBody { errs, picks, calls, reads, hidden }
}

/// Writes one template body check into the program and the reuse cache
/// (hidden types, picks, closure call kinds, the stored check). Returns
/// the check's errors.
pub(crate) fn finish_template(
    p: &mut Program,
    t: LocalDefId,
    reuse: &mut crate::driver::gen_reuse::GenReuse,
    body: TemplateBody,
    closure_fns: &[LocalDefId],
    template_shapes: &ClosureShapes,
) -> Vec<Diag> {
    let TemplateBody { errs: body_errs, picks, calls, reads, hidden } = body;
    for (od, owned) in hidden {
        let h = build_owned_ty(p, &owned);
        p.gx.opaque_hidden.insert(od, h);
    }
    reuse.templates_checked += 1;
    reuse.template_errors += body_errs.len();
    reuse.note_template_out(p, t, &picks, &calls, template_shapes);
    if body_errs.is_empty() && closure_fns.is_empty() && !fn_has_closures(p, t) {
        reuse.store_template(p, t, &reads, &picks, &calls);
    }
    record_template_closures(p, t, Vec::new(), calls);
    for (call, pick) in picks {
        p.gx.trait_picks.insert(call, pick);
    }
    p.gx.mono_counts.0 += 1;
    body_errs
}

/// The `written_projections` key of the const and static item types.
pub(crate) fn item_types_key(p: &Program) -> DefId {
    DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &["<written item types>"], crate::def::DefKind::Const, "", 0) }
}

/// Normalizes one global type through the solver, lifting the
/// result back into the global store when normalization rewrote
/// it in the solver's overlay.
pub fn normalize_global(p: &mut Program, t: Ty) -> Ty {
    normalize_global_in(p, &[], t)
}

/// `normalize_global` under one item's param env: a template's
/// rigid `<T as Tr>::Out` stays, and one its bounds bind
/// (`T: Tr<Out = u8>`) rewrites.
pub fn normalize_global_in(p: &mut Program, env: &[Predicate], t: Ty) -> Ty {
    if !p.tys.flags(t).contains_projection() {
        return t;
    }
    let owned = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        let out = crate::traits::solve::normalize(&mut solver, &mut cx, &p.gx.index, env, t);
        snapshot_ty(&cx.tys, out)
    };
    let t = match owned {
        Some(owned) => build_owned_ty(p, &owned),
        None => t,
    };
    // `<[T] as ToOwned>::Owned` and `<str as ToOwned>::Owned` (the
    // `Cow` Owned field, W-STD-B): a pure solver cannot refute the
    // blanket `impl<T: Clone> ToOwned for T` at an unsized head (its
    // `Clone` and `Sized` clauses are answered by structure in a body),
    // so the lang facts' answers are read off here.
    if let TyKind::Projection(assoc, a) = p.tys.kind(t)
        && assoc.0 == p.gx.lang.assoc_owned
        && let Some(b) = p.tys.args(a).first().and_then(|g| g.as_ty())
    {
        return match p.tys.kind(b) {
            TyKind::Str => STRING,
            TyKind::Slice(e) => p.tys.mk_vec(e),
            _ => t,
        };
    }
    t
}

/// A const or static item's type with its projections normalized
/// (`const C: <A as Tr>::Out`): collect evaluates these items before
/// `normalize_signatures` runs. A projection normalizes only when its
/// trait ref is proved, where clauses included; otherwise the type
/// stays as written and the value's type check rejects it.
pub fn normalize_item_ty(p: &mut Program, t: Ty) -> Ty {
    fn goals(p: &Program, t: Ty, out: &mut Vec<TraitRef>) {
        match p.tys.kind(t) {
            TyKind::Projection(assoc, a) => {
                if let Some(def) = p.gx.index.trait_of_assoc(assoc.0) {
                    out.push(TraitRef { def, args: a, bindings: EMPTY_BINDINGS });
                }
                p.tys.args(a).iter().filter_map(|g| g.as_ty()).for_each(|e| goals(p, e, out));
            }
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => goals(p, e, out),
            TyKind::Tuple(ts) => p.tys.tys_of(ts).iter().for_each(|&e| goals(p, e, out)),
            TyKind::Adt(_, a) => p.tys.args(a).iter().filter_map(|g| g.as_ty()).for_each(|e| goals(p, e, out)),
            _ => {}
        }
    }
    if !p.tys.flags(t).contains_projection() {
        return t;
    }
    let mut needed = Vec::new();
    goals(p, t, &mut needed);
    if needed.iter().all(|&g| prove_goal(p, &[], g)) { normalize_global(p, t) } else { t }
}

/// Normalizes the projections in every fn signature and Adt field
/// type once the impl index is complete (ARCH 2.5), before any body,
/// caller, or C signature reads them: a plain `fn f() -> <A as
/// Tr>::Out` returns the impl's type. Each item normalizes under its
/// own env (`normalize_global_in`); instances normalize again after
/// substitution (`fn_instance`, `adt_instance`), and bodies normalize
/// what they instantiate (check/project.rs).
fn normalize_signatures(p: &mut Program) {
    for i in 0..p.fns.len() {
        normalize_fn_sig(p, i);
    }
    for a in 0..p.adts.len() {
        let has_projection = p.adts[a].variants.iter().flat_map(|v| &v.fields).any(|f| p.tys.flags(f.ty).contains_projection());
        if !has_projection {
            continue;
        }
        if let Some(def) = p.defs.def_of_adt(AdtId(a as u32)) {
            let written = p.adts[a].variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
            p.gx.written_projections.insert(def, written);
        }
        let env = p.gx.adt_envs.get(a).cloned().unwrap_or_default();
        for v in 0..p.adts[a].variants.len() {
            for f in 0..p.adts[a].variants[v].fields.len() {
                let t = p.adts[a].variants[v].fields[f].ty;
                p.adts[a].variants[v].fields[f].ty = normalize_global_in(p, &env, t);
            }
        }
    }
}

/// Normalizes the projections in fn `i`'s signature under its env, in
/// `FnInfo` and the def table (`normalize_signatures`, or a signature
/// delta for the fn it edited).
pub(crate) fn normalize_fn_sig(p: &mut Program, i: usize) {
    crate::borrowck::normalize_self_projections(p, LocalDefId(i as u32));
    let (params, ret) = (p.fns[i].params.clone(), p.fns[i].ret);
    if !params.iter().chain([&ret]).any(|&t| p.tys.flags(t).contains_projection()) {
        return;
    }
    p.gx.written_projections.insert(p.fn_defs[i], params.iter().copied().chain([ret]).collect());
    let env = p.gx.fn_scopes.get(i).map(|s| s.env.clone()).unwrap_or_default();
    let params: Vec<Ty> = params.into_iter().map(|t| normalize_global_in(p, &env, t)).collect();
    let ret = normalize_global_in(p, &env, ret);
    if let Some(data) = p.defs.get_mut(p.fn_defs[i]) {
        data.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret };
    }
    p.fns[i].params = params;
    p.fns[i].ret = ret;
}

/// Substitutes and normalizes a list of signature types.
fn subst_norm_all(p: &mut Program, tys_in: &[Ty], args: &[GenericArg]) -> Vec<Ty> {
    let substed: Vec<Ty> = tys_in.iter().map(|&t| subst(&mut p.tys, t, args)).collect();
    substed.into_iter().map(|t| normalize_global(p, t)).collect()
}

/// Creates (or finds) the Adt instance for one application.
fn adt_instance(p: &mut Program, template: AdtId, args: &[GenericArg]) -> AdtId {
    let (def, _) = p.gx.adt_info[template.0 as usize];
    let args_id = p.tys.intern_args(args);
    if let Some(inst) = p.tys.local_adt_instance(def, args_id) {
        return inst;
    }
    let src_variants: Vec<(Sym, crate::check::collect::VariantShape, i128, bool, Vec<(Sym, Ty, Span)>)> =
        p.adt(template)
            .variants
            .iter()
            .map(|v| (v.name, v.shape, v.disc, v.non_exhaustive, v.fields.iter().map(|f| (f.name, f.ty, f.span)).collect()))
            .collect();
    let mut variants: Vec<crate::check::collect::Variant> = Vec::with_capacity(src_variants.len());
    for (vname, shape, disc, variant_ne, fields) in src_variants {
        let mut out_fields = Vec::with_capacity(fields.len());
        for (name, ty, span) in fields {
            let ty = subst(&mut p.tys, ty, args);
            let ty = normalize_global(p, ty);
            out_fields.push(crate::check::collect::Field { name, ty, span, derive_bounds: Vec::new() });
        }
        variants.push(crate::check::collect::Variant { name: vname, shape, fields: out_fields, disc, non_exhaustive: variant_ne });
    }
    let id = instance_adt_id(p, def, args_id);
    let at = id.0 as usize;
    let (name, is_enum, derives, span, adt_ne) = {
        let src = p.adt(template);
        (src.name, src.is_enum, p.derives_of(template), src.span, src.non_exhaustive)
    };
    p.adts[at] =
        crate::check::collect::AdtDef::new(name, is_enum, variants, derives, span, p.adt(template).repr, adt_ne);
    p.tys.register_adt_instance(def, args_id, id);
    // A generic unsized newtype's instance field, for its C form.
    if p.tys.unsized_field(def).is_some()
        && let Some(f) = p.adts[at].variants.first().and_then(|v| v.fields.first()).map(|f| f.ty)
    {
        p.tys.register_unsized_inst(def, args_id, f);
    }
    p.defs.insert_adt_instance(def, id);
    p.gx.adt_info[at] = (def, args.len());
    let full = p.tys.full_adt_ty(id).unwrap();
    p.gx.adt_scopes[at] = Scope { self_ty: Some(full), ..Scope::default() };
    p.gx.adt_instance_of[at] = Some((def, args_id));
    p.gx.adt_created.push(id);
    p.gx.mono_counts.1 += 1;
    // The Adt instances this one's fields name (`In<u8>` inside
    // `Out<u8>`): a body that only builds `Out<u8>` by `Default` glue and
    // prints it names no `In<u8>`, and codegen then lowered the field
    // through the template (`In(())`). After the registration above, so
    // a recursive type finds itself; the depth guard stops a type that
    // grows its args at each level.
    thread_local!(static FIELD_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) });
    if FIELD_DEPTH.get() < 8 {
        FIELD_DEPTH.set(FIELD_DEPTH.get() + 1);
        let tys: Vec<Ty> = p.adts[at].variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        for t in tys {
            ensure_global_adt_instances(p, t, 0);
        }
        FIELD_DEPTH.set(FIELD_DEPTH.get() - 1);
    }
    id
}

/// The id of a new Adt instance: the session's stable place for its
/// instance key (`collect::InstOrder`), with inert placeholder rows up to
/// it. A key whose place another instance of this program holds (two
/// instances that differ only in lifetimes) takes the next free key.
fn instance_adt_id(p: &mut Program, def: DefId, args: ArgsId) -> AdtId {
    if p.gx.template_rows.is_none() {
        p.gx.template_rows = Some(p.adts.len() as u32);
        p.gx.inst_order.fit(p.adts.len());
    }
    let mut key = p.instance_key_hash(&crate::driver::graph::InstanceKey { def, args }).0;
    let at = loop {
        let at = (p.gx.inst_order.base + p.gx.inst_order.place_of(key)) as usize;
        if p.gx.adt_instance_of.get(at).is_none_or(|i| i.is_none()) {
            break at;
        }
        key = key.rotate_left(17) ^ 0x9e37_79b9_7f4a_7c15;
    };
    while p.adts.len() <= at {
        let name = p.interner.intern("");
        p.adts.push(crate::check::collect::AdtDef::new(name, false, Vec::new(), Default::default(), Span::default(), Default::default(), false));
        p.gx.adt_info.push((DefId::PLACEHOLDER, 0));
        p.gx.adt_generics.push(Generics::default());
        p.gx.adt_envs.push(Vec::new());
        p.gx.adt_scopes.push(Scope::default());
        p.gx.adt_instance_of.push(None);
    }
    AdtId(at as u32)
}

/// The owner Adt instance of one instantiated method, from its
/// substituted receiver parameter type.
fn instance_owner(p: &mut Program, params: &[Ty], self_kind: Option<ast::SelfKind>) -> Option<AdtId> {
    if self_kind.is_none() {
        return None;
    }
    let mut t = *params.first()?;
    // Peel reference forms and smart-pointer-shaped typed
    // receivers down to the Adt application.
    for _ in 0..4 {
        match p.tys.kind(t) {
            TyKind::Ref(_, _, inner) => t = inner,
            TyKind::Adt(def, args) => {
                if let Some(template) = p.defs.local_adt(def) {
                    let args_vec: Vec<GenericArg> = p.tys.args(args).to_vec();
                    if args_vec.is_empty() {
                        return Some(template);
                    }
                    return Some(adt_instance(p, template, &args_vec));
                }
                // A smart-pointer Adt (Box/Rc when they exist):
                // look through one type argument.
                match p.tys.args(args).first().and_then(|g| g.as_ty()) {
                    Some(inner) => t = inner,
                    None => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// One closure of a checked body, snapshotted out of its store so
/// the program can grow while it registers (see `register_closures`).
#[derive(Clone, PartialEq)]
pub(crate) struct OwnedClosure {
    pub(crate) def: DefId,
    pub(crate) kind: crate::check::closure::ClosureKind,
    pub(crate) env: OwnedTy,
    pub(crate) inputs: Vec<OwnedTy>,
    pub(crate) output: OwnedTy,
    pub(crate) free_args: Option<Vec<bool>>,
    pub(crate) scope_body: bool,
    pub(crate) input_regions: Vec<Option<OwnedTy>>,
    pub(crate) output_region: Option<OwnedTy>,
    pub(crate) bound_output: Option<OwnedTy>,
    pub(crate) bound_inputs: Vec<OwnedTy>,
    pub(crate) call_out: bool,
    pub(crate) free_sig: bool,
}

/// Snapshots the closures of one checked body. None when a closure
/// type still holds an inference variable (the body failed to check).
fn snapshot_closures(c: &crate::check::Checked) -> Option<Vec<OwnedClosure>> {
    let mut out = Vec::with_capacity(c.closures.len());
    for cl in &c.closures {
        out.push(OwnedClosure {
            def: cl.def,
            kind: cl.kind,
            env: snapshot_ty(&c.tys, cl.ty)?,
            inputs: cl.inputs.iter().map(|&t| snapshot_ty(&c.tys, t)).collect::<Option<Vec<_>>>()?,
            output: snapshot_ty(&c.tys, cl.output)?,
            free_args: cl.free_args.clone(),
            scope_body: cl.scope_body,
            input_regions: cl.input_regions.iter().map(|o| o.and_then(|t| snapshot_ty(&c.tys, t))).collect(),
            output_region: cl.output_region.and_then(|t| snapshot_ty(&c.tys, t)),
            bound_output: cl.bound_output.and_then(|t| snapshot_ty(&c.tys, t)),
            bound_inputs: cl.bound_inputs.iter().map(|&t| snapshot_ty(&c.tys, t)).collect::<Option<Vec<_>>>().unwrap_or_default(),
            call_out: cl.call_out,
            free_sig: cl.free_sig,
        });
    }
    Some(out)
}

/// The closure analysis of one checked body without types.
pub(crate) type ClosureShapes = Vec<(ast::ExprId, crate::check::closure::ClosureKind, Vec<CaptureShape>)>;

fn closure_shapes(c: &crate::check::Checked) -> ClosureShapes {
    c.closures
        .iter()
        .map(|cl| (cl.expr, cl.kind, cl.captures.iter().map(|cap| (cap.root, cap.projs.clone(), cap.mode)).collect()))
        .collect()
}

/// True when a fn body holds a closure expression.
/// The method names std source defines on the lang enums (`impl<T>
/// Option<T>` in library/core), as this program interns them.
fn lang_enum_method_names(p: &Program) -> Vec<Sym> {
    let b = p.tys.builtins();
    let mut names: Vec<Sym> = p.gx.inherent_methods.keys().filter(|(d, _)| *d == b.option || *d == b.result).map(|&(_, n)| n).collect();
    names.sort_unstable();
    names.dedup();
    names
}

/// True if the body of `fid` calls one of `names` as a method or
/// names it as a path's last segment (`Option::map`).
fn names_lang_enum_method(p: &Program, fid: LocalDefId, names: &[Sym]) -> bool {
    let (lo, hi) = p.fn_def(fid).exprs;
    (lo..hi).any(|x| match p.ast.expr(ast::ExprId(x)) {
        ast::Expr::MethodCall { name, .. } => names.binary_search(name).is_ok(),
        ast::Expr::Path(segs) => segs.last().is_some_and(|s| names.binary_search(&s.name).is_ok()),
        _ => false,
    })
}

pub(crate) fn fn_has_closures(p: &Program, fid: LocalDefId) -> bool {
    let (lo, hi) = p.fn_def(fid).exprs;
    (lo..hi).any(|x| matches!(p.ast.expr(ast::ExprId(x)), ast::Expr::Closure { .. }))
}

/// Records one template check's closure analysis and closure call
/// modes, for the template's concrete instances.
fn record_template_closures(
    p: &mut Program,
    template: LocalDefId,
    shapes: ClosureShapes,
    calls: Vec<(ast::ExprId, crate::check::closure::ClosureKind)>,
) {
    for (e, k, sh) in shapes {
        p.gx.template_closures.insert((template, e), (k, sh));
    }
    for (e, k) in calls {
        p.gx.template_calls.insert((template, e), k);
    }
}

/// Registers the closures of one checked body (ARCH 2.9): each gets
/// a body fn appended to `p.fns` under the closure's own def (so its
/// slot keys on the parent's identity plus the closure ordinal),
/// taking the env first (`&C`, `&mut C`, or `C` by kind) and then the
/// closure's parameters. `class` is `Closure` for concrete parents
/// and `TemplateClosure` for template checks (borrowck only).
/// Returns the new body fns.
fn register_closures(p: &mut Program, parent: LocalDefId, owned: Vec<OwnedClosure>, class: FnClass) -> Vec<LocalDefId> {
    use crate::check::closure::ClosureKind;
    let mut out = Vec::new();
    for oc in owned {
        if let Some(e) = p.gx.closures.get(&oc.def) {
            let id = e.body_fn;
            // Registered from a check that still named a generic
            // definer's template closures (`Checked::closure_map_pending`):
            // the recheck's types replace them, or the closure's body
            // and its callers' instances would disagree on them.
            let stale = |p: &Program, t: Ty| crate::check::opaque::mentions_template_closure(p, &p.tys, t);
            if p.fn_info(id).params.iter().chain([&p.fn_info(id).ret]).any(|&t| stale(p, t)) {
                let env = build_owned_ty(p, &oc.env);
                let inputs: Vec<Ty> = oc.inputs.iter().map(|t| build_owned_ty(p, t)).collect();
                let output = build_owned_ty(p, &oc.output);
                let env_param = match oc.kind {
                    ClosureKind::Fn => p.tys.mk_ref(false, env),
                    ClosureKind::FnMut => p.tys.mk_ref(true, env),
                    ClosureKind::FnOnce => env,
                };
                let mut params = vec![env_param];
                params.extend(inputs.iter().copied());
                if let Some(d) = p.defs.get_mut(oc.def) {
                    d.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret: output };
                }
                let f = &mut p.fns[id.0 as usize];
                f.params = params;
                f.ret = output;
                if let Some(e) = p.gx.closures.get_mut(&oc.def) {
                    e.inputs = inputs;
                    e.output = output;
                }
            }
            out.push(id);
            continue;
        }
        let env = build_owned_ty(p, &oc.env);
        let inputs: Vec<Ty> = oc.inputs.iter().map(|t| build_owned_ty(p, t)).collect();
        let output = build_owned_ty(p, &oc.output);
        let input_regions: Vec<Option<Ty>> = oc.input_regions.iter().map(|o| o.as_ref().map(|t| build_owned_ty(p, t))).collect();
        let output_region: Option<Ty> = oc.output_region.as_ref().map(|t| build_owned_ty(p, t));
        let bound_output: Option<Ty> = oc.bound_output.as_ref().map(|t| build_owned_ty(p, t));
        let bound_inputs: Vec<Ty> = oc.bound_inputs.iter().map(|t| build_owned_ty(p, t)).collect();
        let env_param = match oc.kind {
            ClosureKind::Fn => p.tys.mk_ref(false, env),
            ClosureKind::FnMut => p.tys.mk_ref(true, env),
            ClosureKind::FnOnce => env,
        };
        let mut params = vec![env_param];
        params.extend(inputs.iter().copied());
        let (loc, owner) = {
            let f = p.fn_info(parent);
            (f.loc, f.owner)
        };
        let name = p.interner.intern("{closure}");
        let id = LocalDefId(p.fns.len() as u32);
        p.fn_defs.push(oc.def);
        p.def_by_hash.entry(oc.def.hash).or_insert(id);
        let name_span = loc.def(&p.ast).name_span;
        let mut data =
            crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Closure, None, name, crate::ty::defs::Vis::Priv, name_span);
        data.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret: output };
        p.defs.insert(oc.def, data);
        p.fns.push(crate::check::collect::FnInfo {
            name,
            loc,
            owner,
            self_kind: None,
            params,
            ret: output,
            ret_borrows_from: None,
            is_const: false,
        });
        p.gx.fn_templates.push(None);
        let scope = p.gx.fn_scopes.get(parent.0 as usize).cloned().unwrap_or_default();
        p.gx.fn_scopes.push(scope);
        p.gx.fn_class.push(class);
        p.gx.closures.insert(oc.def, ClosureEntry { parent, body_fn: id, kind: oc.kind, inputs, output, free_args: oc.free_args.clone(), scope_body: oc.scope_body, input_regions, output_region, bound_output, bound_inputs, call_out: oc.call_out, free_sig: oc.free_sig });
        p.gx.closure_fns.insert(id, oc.def);
        out.push(id);
    }
    out
}

/// True when template `t`'s closures, checked again now (its body was
/// edited under a kept program, driver/patch.rs `reuse_kept`), are the
/// ones registered: as many, and each one's kind, signature, and borrow
/// facts equal its entry and body fn. `check_template` then reuses every
/// body fn as a fresh collect would make it (`register_closures` finds
/// each by its def), so the program stands. Also true for no closure.
pub(crate) fn template_closures_stand(p: &mut Program, t: LocalDefId) -> bool {
    use crate::check::closure::ClosureKind;
    let old = p.gx.closures.values().filter(|e| e.parent == t).count();
    if old == 0 && !fn_has_closures(p, t) {
        return true;
    }
    // As `check_template`'s closure pass: its errors are the template
    // check's to report (that check runs next).
    let owned = {
        let (c, _) = crate::check::check_fn(p, t);
        snapshot_closures(&c)
    };
    let Some(owned) = owned else { return false };
    if owned.len() != old {
        return false;
    }
    for oc in owned {
        let Some(e) = p.gx.closures.get(&oc.def).cloned() else { return false };
        let env = build_owned_ty(p, &oc.env);
        let env = match oc.kind {
            ClosureKind::Fn => p.tys.mk_ref(false, env),
            ClosureKind::FnMut => p.tys.mk_ref(true, env),
            ClosureKind::FnOnce => env,
        };
        let inputs: Vec<Ty> = oc.inputs.iter().map(|x| build_owned_ty(p, x)).collect();
        let output = build_owned_ty(p, &oc.output);
        let input_regions: Vec<Option<Ty>> = oc.input_regions.iter().map(|o| o.as_ref().map(|x| build_owned_ty(p, x))).collect();
        let output_region = oc.output_region.as_ref().map(|x| build_owned_ty(p, x));
        let bound_output = oc.bound_output.as_ref().map(|x| build_owned_ty(p, x));
        let bound_inputs: Vec<Ty> = oc.bound_inputs.iter().map(|x| build_owned_ty(p, x)).collect();
        let f = p.fn_info(e.body_fn);
        let same = e.parent == t
            && e.kind == oc.kind
            && e.inputs == inputs
            && e.output == output
            && e.free_args == oc.free_args
            && e.scope_body == oc.scope_body
            && e.input_regions == input_regions
            && e.output_region == output_region
            && e.bound_output == bound_output
            && e.bound_inputs == bound_inputs
            && e.call_out == oc.call_out
            && e.free_sig == oc.free_sig
            && f.params.first() == Some(&env)
            && f.params[1..] == inputs[..]
            && f.ret == output;
        if !same {
            return false;
        }
    }
    true
}

/// The signature of the instance of `template` at `args` whose def is
/// `def_id`: what `fn_instance` writes for it, and what `refresh_instance`
/// writes again after a header delta of its template.
pub(crate) struct InstanceSig {
    params: Vec<Ty>,
    ret: Ty,
    opaque_ret: Option<Ty>,
    owner: Option<AdtId>,
    ret_borrows_from: Option<usize>,
    scope: Scope,
}

pub(crate) fn instance_sig(p: &mut Program, template: LocalDefId, args: &[GenericArg], def_id: DefId) -> InstanceSig {
    let self_kind = p.fn_info(template).self_kind;
    let raw_params: Vec<Ty> = p.fn_info(template).params.clone();
    let raw_ret = p.fn_info(template).ret;
    let ret_borrows_from = p.fn_info(template).ret_borrows_from;
    let params = subst_norm_all(p, &raw_params, args);
    let raw_ret = subst(&mut p.tys, raw_ret, args);
    let ret = normalize_global(p, raw_ret);
    // A generic fn's own `impl Trait` return: the instance generates its
    // hidden type, and callers keep the opaque (check/opaque.rs).
    let opaque_ret = crate::check::opaque::mentions_opaque(&p.tys, ret, None).then_some(ret);
    let ret = match opaque_ret {
        Some(o) => {
            let hidden = std::mem::take(&mut p.gx.opaque_hidden);
            // A hidden type can name a projection of the params
            // (`I::IntoIter`), which the args now decide (normalized).
            let r = crate::check::opaque::reveal_global(p, hidden.as_map(), o);
            p.gx.opaque_hidden = hidden;
            r
        }
        None => ret,
    };
    let owner = instance_owner(p, &params, self_kind);
    // The hidden type's closures are this instance's own.
    let ret = match opaque_ret {
        Some(_) => {
            let map = crate::check::opaque::instance_closure_map(p, &p.tys, ret, template, def_id);
            if map.is_empty() { ret } else { crate::check::opaque::map_closure_defs(&mut p.tys, ret, &map) }
        }
        None => ret,
    };
    // The body scope of an instance: no parameters, the concrete
    // Self type, and the template's assoc sources substituted. Self
    // comes from the template's scope (a trait default assoc fn has
    // no receiver to name an owner), else from the owner.
    let scope = {
        let mut sc = Scope::default();
        let tmpl_self = p.gx.fn_scopes.get(template.0 as usize).and_then(|ts| ts.scope.self_ty);
        sc.self_ty = match tmpl_self {
            Some(t) => {
                let t = subst(&mut p.tys, t, args);
                Some(normalize_global(p, t))
            }
            None => owner.map(|a| p.tys.adt_ty(a)),
        };
        if let Some(ts) = p.gx.fn_scopes.get(template.0 as usize) {
            for src in &ts.scope.assoc_srcs {
                let self_ty = subst(&mut p.tys, src.self_ty, args);
                let sargs = crate::traits::index::subst_args_pub(&mut p.tys, src.args, args);
                sc.assoc_srcs.push(AssocSrc { self_ty, trait_def: src.trait_def, args: sargs, assocs: src.assocs.clone() });
            }
            for (name, t) in &ts.scope.param_tys {
                let t2 = subst(&mut p.tys, *t, args);
                sc.param_tys.push((*name, t2));
            }
            for &(name, i, _) in &ts.scope.const_params {
                if let Some(GenericArg::Const(c)) = args.get(i as usize) {
                    sc.const_values.push((name, *c));
                }
            }
            // The template's named lifetimes, so a body annotation that
            // names one (`let x: &'a T`) resolves in the instance too.
            sc.lifetimes = ts.scope.lifetimes.clone();
            sc.region_facts = ts.scope.region_facts.clone();
        }
        sc
    };
    InstanceSig { params, ret, opaque_ret, owner, ret_borrows_from, scope }
}

/// Writes instance `inst`'s signature again from its template's (a header
/// delta of the template, driver/kept_delta.rs), as `fn_instance` would
/// make it now. Err when its owner or its `impl Trait` return moves: the
/// method tables and the opaque type callers keep would then differ (the
/// template's own check proved its hidden type stands).
pub(crate) fn refresh_instance(p: &mut Program, inst: LocalDefId) -> Result<InstanceUndo, &'static str> {
    let Some(info) = p.gx.instances.get(&inst) else { return Err("instance") };
    let Some(template) = info.template_local else { return Err("instance") };
    let args: Vec<GenericArg> = p.tys.args(info.args).to_vec();
    let def_id = p.def_id(inst);
    let s = instance_sig(p, template, &args, def_id);
    let i = inst.0 as usize;
    if s.owner != p.fns[i].owner || s.opaque_ret != p.gx.opaque_ret_of.get(&inst).copied() {
        return Err("instance owner");
    }
    let sig = p.defs.get_mut(def_id).map(|d| std::mem::replace(&mut d.sig, crate::ty::defs::SigData::Fn { params: s.params.clone(), ret: s.ret }));
    let f = &mut p.fns[i];
    let old = (std::mem::replace(&mut f.params, s.params), std::mem::replace(&mut f.ret, s.ret), std::mem::replace(&mut f.ret_borrows_from, s.ret_borrows_from));
    let scope = std::mem::replace(&mut p.gx.fn_scopes[i], FnScope { env: Vec::new(), scope: s.scope });
    Ok(InstanceUndo { inst, params: old.0, ret: old.1, ret_borrows_from: old.2, scope, sig })
}

/// What `refresh_instance` wrote over, for `undo_instance`.
pub(crate) struct InstanceUndo {
    inst: LocalDefId,
    params: Vec<Ty>,
    ret: Ty,
    ret_borrows_from: Option<usize>,
    scope: FnScope,
    sig: Option<crate::ty::defs::SigData>,
}

/// Puts back what `refresh_instance` wrote (a refused header delta keeps
/// the program, driver/kept_delta.rs `fail`).
pub(crate) fn undo_instance(p: &mut Program, u: InstanceUndo) {
    let i = u.inst.0 as usize;
    let def_id = p.def_id(u.inst);
    if let (Some(d), Some(sig)) = (p.defs.get_mut(def_id), u.sig) {
        d.sig = sig;
    }
    let f = &mut p.fns[i];
    (f.params, f.ret, f.ret_borrows_from) = (u.params, u.ret, u.ret_borrows_from);
    p.gx.fn_scopes[i] = u.scope;
}

/// Creates (or finds) the concrete instance of one template.
fn fn_instance(p: &mut Program, template: LocalDefId, args: &[GenericArg]) -> LocalDefId {
    let template_def = p.def_id(template);
    let args_id = p.tys.intern_args(args);
    if let Some(&existing) = p.gx.instance_by_key.get(&(template_def, args_id)) {
        return existing;
    }
    let (loc, name, self_kind) = {
        let f = p.fn_info(template);
        (f.loc, f.name, f.self_kind)
    };
    // Instance identity: template disk identity plus the args
    // fingerprint (the InstanceKeyHash of section 4.2).
    let key = crate::driver::graph::InstanceKey { def: template_def, args: args_id };
    let kh = p.instance_key_hash(&key);
    // The instance def lives under an "<instance>" module with
    // the key hash in its name, so it can never collide with a
    // user def's path hash in the slot registry.
    let def_id = DefId {
        krate: p.krate,
        hash: crate::def::item_hash(p.stable_crate, &["<instance>"], crate::def::DefKind::Fn, &format!("{}#{}", p.name(name), kh.0), 0),
    };
    let InstanceSig { params, ret, opaque_ret, owner, ret_borrows_from, scope } = instance_sig(p, template, args, def_id);
    let id = LocalDefId(p.fns.len() as u32);
    p.fn_defs.push(def_id);
    p.def_by_hash.entry(def_id.hash).or_insert(id);
    let (name_span, is_const) = {
        let def = loc.def(&p.ast);
        (def.name_span, def.qual.is_const)
    };
    let mut data = crate::ty::defs::DefData::skeleton(
        if owner.is_some() { crate::ty::defs::DefKind::Method } else { crate::ty::defs::DefKind::Fn },
        None,
        name,
        crate::ty::defs::Vis::Priv,
        name_span,
    );
    data.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret };
    p.defs.insert(def_id, data);
    p.fns.push(crate::check::collect::FnInfo { name, loc, owner, self_kind, params, ret, ret_borrows_from, is_const });
    if let Some(o) = opaque_ret {
        p.gx.opaque_ret_of.insert(id, o);
    }
    p.gx.fn_templates.push(None);
    p.gx.fn_scopes.push(FnScope { env: Vec::new(), scope });
    p.gx.fn_class.push(FnClass::Instance);
    p.gx.instances.insert(id, InstanceInfo { template_def, template_local: Some(template), args: args_id });
    p.gx.instance_by_key.insert((template_def, args_id), id);
    p.gx.mono_counts.1 += 1;
    // Inherent instances join the compat method table.
    if let Some(owner) = owner
        && is_inherent_template(p, template)
    {
        let cands = p.methods.entry((owner, name)).or_default();
        if !cands.contains(&id) {
            cands.push(id);
        }
    }
    id
}

/// True when fn `t` is in some `GenTables::inherent_methods` list.
fn is_inherent_template(p: &Program, t: LocalDefId) -> bool {
    p.gx.inherent_tmpls.get_or_init(|| p.gx.inherent_methods.values().flatten().map(|&f| (f, ())).collect()).contains_key(&t)
}

/// Walks one checked type for generic Adt applications mono has
/// not made yet, creating them (their own fields may name more).
// Not wired yet; see the note on lift_ty above.
#[allow(dead_code)]
fn ensure_adt_instances_in(p: &mut Program, src: &dyn TyIntern, t: Ty, depth: u32) {
    if depth > 32 {
        return;
    }
    match src.kind(t) {
        TyKind::Adt(def, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_adt_instances_in(p, src, e, depth + 1);
                }
            }
            if !raw.is_empty()
                && let Some(template) = p.defs.local_adt(def)
                && !p.gx.adt_generics[template.0 as usize].params.is_empty()
            {
                let mut lifted: Vec<GenericArg> = Vec::new();
                let mut ok = true;
                for g in &raw {
                    match g {
                        GenericArg::Ty(e) => match lift_ty(p, src, *e) {
                            Some(gt) => lifted.push(GenericArg::Ty(gt)),
                            None => {
                                ok = false;
                                break;
                            }
                        },
                        GenericArg::Const(c) => match src.const_kind(*c) {
                            ConstKind::Infer(_) => {
                                ok = false;
                                break;
                            }
                            k => lifted.push(GenericArg::Const(p.tys.intern_const(k))),
                        },
                        other => lifted.push(*other),
                    }
                }
                if ok {
                    adt_instance(p, template, &lifted);
                }
            }
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => {
            ensure_adt_instances_in(p, src, e, depth + 1)
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = src.tys_of(ts).to_vec();
            for e in elems {
                ensure_adt_instances_in(p, src, e, depth + 1);
            }
        }
        TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_adt_instances_in(p, src, e, depth + 1);
                }
            }
        }
        _ => {}
    }
}

/// Finds the Drop method instance for one concrete Adt instance,
/// creating it when a `Drop` impl applies. Records it for cgen.
fn ensure_drop_method(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    if p.gx.drop_methods.contains_key(&adt) {
        return;
    }
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    let args_id = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
    let tr = TraitRef { def: p.gx.lang.drop, args: args_id, bindings: EMPTY_BINDINGS };
    let sel = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        solver.select(&mut cx, &p.gx.index, &[], tr)
    };
    let Selection::Impl { id, args: impl_args, .. } = sel else { return };
    let record = p.gx.index.get(id).clone();
    let Some(local) = record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "drop"))
    else {
        return;
    };
    // An Adt whose args still hold a type param (a field type of a generic
    // Adt's template, `W<T>` in `struct G<T: Write> { w: W<T> }`) records
    // the template fn: cgen never sees it, `needs_drop` only asks whether
    // it has one, and an instance would check the body with no bounds on
    // the param (a false L0612).
    let drop_fn = if p.tys.flags(self_ty).contains_param() {
        local
    } else if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
        let raw: Vec<GenericArg> = impl_args;
        let before = p.fns.len();
        let inst = fn_instance(p, local, &raw);
        if inst.0 as usize >= before {
            queue.push(inst);
        }
        inst
    } else {
        local
    };
    p.gx.drop_methods.insert(adt, drop_fn);
}

/// The user `Hasher` and `BuildHasher` method instances of one concrete
/// Adt (`gx.hasher_methods`, `gx.build_hashers`; W-STD-B): selection on
/// the Adt's full type, then every method of the written impl.
fn ensure_hash_methods(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    use crate::traits::index::Synthetic;
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    if p.tys.flags(self_ty).contains_param() {
        return;
    }
    for trait_def in [p.gx.lang.hasher, p.gx.lang.build_hasher] {
        let args_id = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
        let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
        let sel = {
            let mut cx = crate::traits::solve::PureCx::new(&p.tys);
            let mut solver = Solver::new();
            solver.select(&mut cx, &p.gx.index, &[], tr)
        };
        let Selection::Impl { id, args: impl_args, .. } = sel else { continue };
        let record = p.gx.index.get(id).clone();
        if record.synthetic != Synthetic::None || !prove_goal(p, &[], tr) {
            continue;
        }
        for d in record.items.clone() {
            let Some(local) = p.local_def(d.hash) else { continue };
            let name = p.name(p.fn_info(local).name).to_string();
            let f = if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
                let before = p.fns.len();
                let inst = fn_instance(p, local, &impl_args);
                if inst.0 as usize >= before {
                    queue.push(inst);
                }
                inst
            } else {
                local
            };
            if trait_def == p.gx.lang.hasher {
                if let Some(i) = crate::check::hashmap::HASHER_METHODS.iter().position(|m| *m == name) {
                    p.gx.hasher_methods.insert((adt, i as u8), f);
                }
            } else if name == "build_hasher"
                && let Some(h) = record.assoc_ty(p.gx.lang.assoc_hasher)
            {
                let h = subst(&mut p.tys, h, &impl_args);
                let h = normalize_global(p, h);
                ensure_global_adt_instances(p, h, 0);
                p.gx.build_hashers.insert(adt, (f, h));
            }
        }
    }
}

/// The user `fmt` method instances of one concrete Adt, for cgen's
/// Display and Debug glue (`gx.fmt_methods`, W-STD-B): for each of the
/// two traits, selection on the Adt's full type, and the selected
/// written impl's `fmt` (instantiated when the impl is generic). A
/// derived or absent impl records nothing; glue then uses the derive.
fn ensure_fmt_methods(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    use crate::traits::index::Synthetic;
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    if p.tys.flags(self_ty).contains_param() {
        return;
    }
    for (trait_def, kind) in [(p.gx.lang.display, ast::FmtKind::Display), (p.gx.lang.debug, ast::FmtKind::Debug)] {
        if p.gx.fmt_methods.contains_key(&(adt, kind as u8)) {
            continue;
        }
        let args_id = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
        let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
        let sel = {
            let mut cx = crate::traits::solve::PureCx::new(&p.tys);
            let mut solver = Solver::new();
            solver.select(&mut cx, &p.gx.index, &[], tr)
        };
        let Selection::Impl { id, args: impl_args, .. } = sel else { continue };
        let record = p.gx.index.get(id).clone();
        // An impl whose where clauses fail has no instance: a type that
        // is never formatted (`VecDeque<D>` with `D: !Debug`) must not
        // instantiate its `T: Debug` impl. `prove_goal` is weaker than
        // the format site's proof for args holding references or
        // closures (`W<&str>: Debug` fails it), and a skip there printed
        // a structural Debug for a type with no derive (wrong output):
        // for those, the selected written impl is called (W-STD-C).
        if record.synthetic != Synthetic::None || !fmt_impl_bounds_hold(p, &record, &impl_args, tr, self_ty) {
            continue;
        }
        let Some(local) = record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "fmt"))
        else {
            continue;
        };
        let f = if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
            let before = p.fns.len();
            let inst = fn_instance(p, local, &impl_args);
            if inst.0 as usize >= before {
                queue.push(inst);
            }
            inst
        } else {
            local
        };
        p.gx.fmt_methods.insert((adt, kind as u8), f);
    }
}

/// The written `Clone`, `Default`, `PartialEq`, and `PartialOrd`
/// method instances of one concrete Adt, for the derive glue
/// (`gx.glue_methods`, `gx.pcmp_methods`): selection on the Adt's
/// full type, as in `ensure_fmt_methods`. `compute_glue_methods`
/// records the non-generic impls in finish_collect; this adds the
/// generic ones (an `impl<S, S2> PartialEq<M<S2>> for M<S>`, std's
/// `impl<T: Clone> Clone for OnceCell<T>`), instantiated here where
/// the concrete Adt is known. An entry is recorded only when the
/// glue walk also accepts the type (`written_glue_impl` on the
/// check side, same `ne`/`lt` and Copy guards), so check and cgen
/// agree on which types compare, clone, and default by glue.
fn ensure_glue_methods(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    use crate::traits::index::Synthetic;
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    if p.tys.flags(self_ty).contains_param() {
        return;
    }
    let lang = p.gx.lang;
    for (trait_def, method) in
        [(lang.clone, "clone"), (lang.default, "default"), (lang.partial_eq, "eq"), (lang.partial_ord, "partial_cmp")]
    {
        if p.gx.glue_methods.contains_key(&(adt, trait_def)) && (trait_def != lang.partial_ord || p.gx.pcmp_methods.contains_key(&(adt, trait_def))) {
            continue;
        }
        let mut a = vec![GenericArg::Ty(self_ty)];
        if trait_def == lang.partial_eq || trait_def == lang.partial_ord {
            a.push(GenericArg::Ty(self_ty));
        }
        let args_id = p.tys.intern_args(&a);
        let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
        let sel = {
            let mut cx = crate::traits::solve::PureCx::new(&p.tys);
            let mut solver = Solver::new();
            solver.select(&mut cx, &p.gx.index, &[], tr)
        };
        let Selection::Impl { id, args: impl_args, .. } = sel else { continue };
        let record = p.gx.index.get(id).clone();
        if record.synthetic != Synthetic::None {
            continue;
        }
        let has = |p: &Program, n: &str| record.items.iter().any(|&m| p.local_def(m.hash).is_some_and(|l| p.name(p.fn_info(l).name) == n));
        let Some(local) =
            record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == method))
        else {
            continue;
        };
        let (has_ne, has_rel) = (has(p, "ne"), ["lt", "le", "gt", "ge"].iter().any(|&n| has(p, n)));
        let has_lt = has(p, "lt");
        // Which glue maps take this method, on `compute_glue_methods`'
        // terms, gated on the walk that answers for the same glue.
        let mut to_glue = false;
        let mut to_pcmp = false;
        if trait_def == lang.clone {
            let copy_args = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
            to_glue = crate::check::collect::has_clone(p, &p.tys, self_ty)
                && !prove_goal(p, &[], TraitRef { def: lang.copy, args: copy_args, bindings: EMPTY_BINDINGS });
        } else if trait_def == lang.default {
            to_glue = crate::check::collect::has_default(p, &p.tys, self_ty);
        } else if trait_def == lang.partial_eq {
            to_glue = !has_ne && crate::check::collect::has_eq(p, &p.tys, self_ty);
        } else {
            to_pcmp = !has_lt && crate::check::collect::has_partial_cmp(p, &p.tys, self_ty);
            let ord_args = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
            to_glue = !has_rel
                && !prove_goal(p, &[], TraitRef { def: lang.ord, args: ord_args, bindings: EMPTY_BINDINGS })
                && crate::check::collect::has_ord(p, &p.tys, self_ty);
        }
        if !to_glue && !to_pcmp {
            continue;
        }
        let f = iter_fn_instance(p, local, &impl_args, queue);
        if to_glue {
            p.gx.glue_methods.entry((adt, trait_def)).or_insert(f);
            // The same impl's written `clone_from`, at this instance.
            if trait_def == lang.clone
                && let Some(cf) =
                    record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "clone_from"))
            {
                let cf = iter_fn_instance(p, cf, &impl_args, queue);
                p.gx.clone_from_methods.entry(adt).or_insert(cf);
            }
        }
        if to_pcmp {
            p.gx.pcmp_methods.entry((adt, trait_def)).or_insert(f);
        }
    }
}

/// One impl method at its concrete instance, for `ensure_iter_methods`:
/// the plain fn when the impl is not a template, else its instance
/// (queued for checking when new), as in `ensure_fmt_methods`.
fn iter_fn_instance(p: &mut Program, local: LocalDefId, impl_args: &[GenericArg], queue: &mut Vec<LocalDefId>) -> LocalDefId {
    if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
        let before = p.fns.len();
        let inst = fn_instance(p, local, impl_args);
        if inst.0 as usize >= before {
            queue.push(inst);
        }
        inst
    } else {
        local
    }
}

/// The user `Iterator` method instances of one concrete Adt
/// (`gx.iter_methods`): selection on the Adt's full type, then the
/// written impl's `next` and `size_hint`, plus `next_back` from its
/// `DoubleEndedIterator` impl. Only the shape the `ByNext` expansion
/// can call records anything (check/iter.rs `by_next_fns`): a written
/// impl that defines no provided method besides `size_hint`. Std
/// source Adts keep their builtin iterator kinds and are skipped, except
/// the `core::iter` sources (library/core/src/iter.rs) and
/// `core::char::DecodeUtf16`, which step by their own `next` as a user
/// iterator does.
fn ensure_iter_methods(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    use crate::traits::index::Synthetic;
    let own_next = |path: String| path.starts_with("core::iter::") || path == "core::char::DecodeUtf16";
    if p.gx.iter_methods.contains_key(&adt) || (p.is_std_adt(adt) && !own_next(p.display_path(p.adt(adt).name))) {
        return;
    }
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    if p.tys.flags(self_ty).contains_param() {
        return;
    }
    let lang = p.gx.lang;
    let self_args = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
    let select = |p: &mut Program, trait_def: DefId| {
        let tr = TraitRef { def: trait_def, args: self_args, bindings: EMPTY_BINDINGS };
        let sel = {
            let mut cx = crate::traits::solve::PureCx::new(&p.tys);
            let mut solver = Solver::new();
            solver.select(&mut cx, &p.gx.index, &[], tr)
        };
        match sel {
            Selection::Impl { id, args, .. } if prove_goal(p, &[], tr) => Some((id, args)),
            // The pure solver cannot prove an Fn-family bound on a
            // closure (check proved it with the closure's signature).
            Selection::Impl { id, .. } => {
                let rec = p.gx.index.get(id).clone();
                fn_bound_impl_args(p, &rec, self_ty).map(|args| (id, args))
            }
            _ => None,
        }
    };
    let Some((id, impl_args)) = select(p, lang.iterator) else { return };
    let record = p.gx.index.get(id).clone();
    if record.synthetic != Synthetic::None {
        return;
    }
    let (mut next, mut size_hint) = (None, None);
    for d in record.items.clone() {
        let Some(local) = p.local_def(d.hash) else { return };
        match p.name(p.fn_info(local).name) {
            "next" => next = Some(local),
            "size_hint" => size_hint = Some(local),
            _ => return,
        }
    }
    let Some(next) = next else { return };
    let next = iter_fn_instance(p, next, &impl_args, queue);
    let size_hint = size_hint.map(|l| iter_fn_instance(p, l, &impl_args, queue));
    let item = record.assoc_ty(lang.assoc_item).map(|t| {
        let t = subst(&mut p.tys, t, &impl_args);
        normalize_global(p, t)
    });
    let next_back = select(p, lang.double_ended_iterator).and_then(|(id, args)| {
        let rec = p.gx.index.get(id).clone();
        if rec.synthetic != Synthetic::None {
            return None;
        }
        let local = rec.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "next_back"))?;
        Some(iter_fn_instance(p, local, &args, queue))
    });
    // An `ExactSizeIterator` impl with no `len` override, like
    // `by_next_fns` reads it: `len()` runs the trait default.
    let exact = size_hint.is_some()
        && select(p, lang.exact_size_iterator).is_some_and(|(id, _)| {
            let rec = p.gx.index.get(id);
            rec.synthetic == Synthetic::None
                && !rec.items.iter().any(|d| p.local_def(d.hash).is_some_and(|l| p.name(p.fn_info(l).name) == "len"))
        });
    p.gx.iter_methods.insert(adt, (next, size_hint, next_back, item, exact));
}

/// Impl args for `rec` at the concrete `self_ty` when the pure solver
/// cannot prove the impl's Fn-family bounds (`impl<T, F: FnMut() ->
/// Option<T>> Iterator for FromFn<F>`): Self binds what it can, each
/// Fn-family bound on a closure or fn pointer binds the rest from that
/// callable's signature (a closure's kind must fit the bound), and every
/// other trait bound must prove at the bound args. None when a step
/// fails or a parameter stays unbound.
fn fn_bound_impl_args(p: &mut Program, rec: &crate::traits::index::ImplRecord, self_ty: Ty) -> Option<Vec<GenericArg>> {
    use crate::check::closure::ClosureKind;
    let lang = p.gx.lang;
    let output = lang.output_of(lang.fn_once)?;
    let mut binds: Vec<Option<GenericArg>> = vec![None; rec.generics.params.len()];
    if !crate::check::iter::match_self_pat(p, &p.tys, rec.self_ty(&p.tys), self_ty, &mut binds) {
        return None;
    }
    // A callable's (inputs, output), when its kind fits `trait_def`.
    let callable = |p: &Program, t: Ty, trait_def: DefId| -> Option<(Vec<Ty>, Ty)> {
        let (inputs, out) = match p.tys.kind(t) {
            TyKind::Closure(def, _) => {
                let e = p.gx.closures.get(&def)?;
                let need = if trait_def == lang.fn_ { ClosureKind::Fn } else if trait_def == lang.fn_mut { ClosureKind::FnMut } else { ClosureKind::FnOnce };
                let fits = matches!((e.kind, need), (ClosureKind::Fn, _) | (ClosureKind::FnMut, ClosureKind::FnMut | ClosureKind::FnOnce) | (ClosureKind::FnOnce, ClosureKind::FnOnce));
                if !fits {
                    return None;
                }
                (e.inputs.clone(), e.output)
            }
            TyKind::FnPtr(sig) => {
                let s = p.tys.sig(sig).value;
                (p.tys.tys_of(s.inputs).to_vec(), s.output)
            }
            _ => return None,
        };
        let concrete = inputs.iter().chain([&out]).all(|&x| !p.tys.flags(x).contains_param());
        concrete.then_some((inputs, out))
    };
    // The bound's callee once Self or an earlier bound bound it.
    let bound_ty = |pat: Ty, binds: &[Option<GenericArg>]| match p.tys.kind(pat) {
        TyKind::Param(i) => binds.get(i.0 as usize).copied().flatten().and_then(|g| g.as_ty()),
        _ if !p.tys.flags(pat).contains_param() => Some(pat),
        _ => None,
    };
    let preds = rec.generics.predicates.clone();
    let mut fn_pred = vec![false; preds.len()];
    for _ in 0..=preds.len() {
        let mut progress = false;
        for (k, pred) in preds.iter().enumerate() {
            let Predicate::Trait(b) = *pred else { continue };
            if fn_pred[k] || !lang.is_fn_family(b.value.def) {
                continue;
            }
            let args = p.tys.args(b.value.args).to_vec();
            let (Some(callee_pat), Some(inputs_pat)) = (args.first().and_then(|g| g.as_ty()), args.get(1).and_then(|g| g.as_ty())) else {
                return None;
            };
            let Some(callee) = bound_ty(callee_pat, &binds) else { continue };
            let (inputs, out) = callable(p, callee, b.value.def)?;
            let TyKind::Tuple(ts) = p.tys.kind(inputs_pat) else { return None };
            let pats = p.tys.tys_of(ts).to_vec();
            if pats.len() != inputs.len() || !pats.iter().zip(&inputs).all(|(&x, &y)| crate::check::iter::match_self_pat(p, &p.tys, x, y, &mut binds)) {
                return None;
            }
            for &(assoc, g) in p.tys.bindings(b.value.bindings).to_vec().iter() {
                if assoc != output {
                    return None;
                }
                let Some(pat) = g.as_ty() else { return None };
                if !crate::check::iter::match_self_pat(p, &p.tys, pat, out, &mut binds) {
                    return None;
                }
            }
            fn_pred[k] = true;
            progress = true;
        }
        if !progress {
            break;
        }
    }
    let args: Vec<GenericArg> = binds.into_iter().collect::<Option<Vec<_>>>()?;
    for (k, &pred) in preds.iter().enumerate() {
        match crate::traits::index::subst_predicate(&mut p.tys, pred, &args) {
            _ if fn_pred[k] => {}
            Predicate::Trait(b) if b.count == 0 && prove_goal(p, &[], b.value) => {}
            // Regions are erased in mono; an equality or a bound this
            // fallback cannot read keeps the old answer.
            Predicate::Outlives(..) | Predicate::TypeOutlives(..) => {}
            _ => return None,
        }
    }
    Some(args)
}

/// True when a written fmt impl's where clauses hold for its selected
/// args (`ensure_fmt_methods`). A `Debug`/`Display` bound holds when the
/// format site's structural question (`has_debug`, `has_display`) or
/// `prove_goal` (written impls) says so, or the arg holds references
/// or closures; `prove_goal` alone gives false negatives for tuples and
/// references. Other bounds take `prove_goal`, with the same escape.
fn fmt_impl_bounds_hold(p: &mut Program, record: &crate::traits::index::ImplRecord, impl_args: &[GenericArg], tr: TraitRef, self_ty: Ty) -> bool {
    let lang = p.gx.lang;
    // Bounds that are not `Debug`/`Display` are proven one by one at
    // the end, each at its normal form: proving the whole `tr` again
    // re-asks the fmt bounds as projections (`A::Item: Debug`),
    // which the pure solver cannot select on, and a written impl
    // was then skipped for a structural answer (wrong output).
    let mut others: Vec<TraitRef> = Vec::new();
    for pr in &record.generics.predicates {
        // Non-trait predicates and higher-ranked bounds are not
        // goals here, as in `prove_trait_ref`.
        let Predicate::Trait(b) = pr else { continue };
        if b.count != 0 {
            continue;
        }
        let d = b.value.def;
        if d == lang.sized {
            continue;
        }
        if d != lang.debug && d != lang.display {
            let raw: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            let mut args: Vec<GenericArg> = Vec::with_capacity(raw.len());
            for g in raw {
                args.push(match g.as_ty() {
                    Some(t) => {
                        let t = crate::ty::subst(&mut p.tys, t, impl_args);
                        GenericArg::Ty(normalize_global(p, t))
                    }
                    None => g,
                });
            }
            let args = p.tys.intern_args(&args);
            // The bindings name impl parameters too (`B: Bounds<Primitive
            // = P>`): they take the selected args, normalized as above.
            let raw_b: Vec<(DefId, GenericArg)> = p.tys.bindings(b.value.bindings).to_vec();
            let mut new_b: Vec<(DefId, GenericArg)> = Vec::with_capacity(raw_b.len());
            for (assoc, g) in raw_b {
                new_b.push((
                    assoc,
                    match g.as_ty() {
                        Some(t) => {
                            let t = crate::ty::subst(&mut p.tys, t, impl_args);
                            GenericArg::Ty(normalize_global(p, t))
                        }
                        None => g,
                    },
                ));
            }
            let bindings = p.tys.intern_bindings(&new_b);
            others.push(TraitRef { def: d, args, bindings });
            continue;
        }
        let Some(arg) = p.tys.args(b.value.args).first().and_then(|g| g.as_ty()) else { return false };
        // A bound on a projection (`A::Item: Debug`) names its normal
        // form here: the structural check and `prove_goal` do not
        // normalize projections in a trait ref's Self type.
        let t = crate::ty::subst(&mut p.tys, arg, impl_args);
        let mut t = normalize_global(p, t);
        // `&T: Debug` (and Display) holds exactly when `T: Debug` does
        // (std's impls for `&T` and `&mut T`): ask about `T`, so
        // `OnceCell<&No>` with `No: !Debug` makes no instance (its body
        // check failed the build). A closure is never Debug or Display.
        while let TyKind::Ref(_, _, u) = p.tys.kind(t) {
            t = u;
        }
        if matches!(p.tys.kind(t), TyKind::Closure(..)) {
            return false;
        }
        // The structural answer (builtin types, tuples, derives), else a
        // written impl (`prove_goal`), else an arg the proof cannot see.
        let structural = if d == lang.debug { crate::check::collect::has_debug(p, &p.tys, t) } else { crate::check::collect::has_display(p, &p.tys, t) };
        let ok = structural || {
            let args = p.tys.intern_args(&[GenericArg::Ty(t)]);
            prove_goal(p, &[], TraitRef { def: d, args, bindings: EMPTY_BINDINGS })
                || (args_hold_refs(&p.tys, t) && !ref_pointee_lacks(p, t, d, 0))
        };
        if !ok {
            return false;
        }
    }
    let _ = tr;
    others.iter().all(|&o| prove_goal(p, &[], o)) || args_hold_refs(&p.tys, self_ty)
}

/// True when a reference inside `t`'s type arguments (at any depth)
/// points at a type that surely lacks the fmt trait `d` (Debug or
/// Display): a closure, or a type with no structural answer, no
/// written impl, and no references of its own (`G<&No>` with `No:
/// !Debug`). `fmt_impl_bounds_hold` trusts other reference args.
fn ref_pointee_lacks(p: &mut Program, t: Ty, d: DefId, depth: u32) -> bool {
    if depth > 16 {
        return false;
    }
    let inner: Vec<Ty> = match p.tys.kind(t) {
        TyKind::Tuple(ts) => p.tys.tys_of(ts).to_vec(),
        TyKind::Array(e, _) | TyKind::Slice(e) => vec![e],
        TyKind::Adt(_, a) => p.tys.args(a).iter().filter_map(|g| g.as_ty()).collect(),
        TyKind::Ref(..) => vec![t],
        _ => return false,
    };
    for mut e in inner {
        if !matches!(p.tys.kind(e), TyKind::Ref(..)) {
            if ref_pointee_lacks(p, e, d, depth + 1) {
                return true;
            }
            continue;
        }
        while let TyKind::Ref(_, _, u) = p.tys.kind(e) {
            e = u;
        }
        if matches!(p.tys.kind(e), TyKind::Closure(..)) {
            return true;
        }
        let lang = p.gx.lang;
        let structural =
            if d == lang.debug { crate::check::collect::has_debug(p, &p.tys, e) } else { crate::check::collect::has_display(p, &p.tys, e) };
        let args = p.tys.intern_args(&[GenericArg::Ty(e)]);
        if !structural && !prove_goal(p, &[], TraitRef { def: d, args, bindings: EMPTY_BINDINGS }) && !args_hold_refs(&p.tys, e) {
            return true;
        }
        if ref_pointee_lacks(p, e, d, depth + 1) {
            return true;
        }
    }
    false
}

/// True when some type argument of `t` (at any depth) is a reference,
/// raw pointer, or closure (`ensure_fmt_methods`).
fn args_hold_refs(tys: &GlobalTys, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::Closure(..) => true,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| args_hold_refs(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => args_hold_refs(tys, e),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| args_hold_refs(tys, e))),
        _ => false,
    }
}

/// Records the written generic `Hash` impl of one concrete Adt
/// instance (`gx.generic_hash`), on the terms of `compute_written_hash`
/// (no own `hash_slice`), when the check side's glue walk also hashes
/// the type through it (`has_hash`), so check and cgen agree.
fn ensure_generic_hash(p: &mut Program, adt: AdtId) {
    use crate::traits::index::Synthetic;
    if p.gx.written_hash.contains_key(&adt) || p.gx.generic_hash.contains_key(&adt) {
        return;
    }
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    if p.tys.flags(self_ty).contains_param() {
        return;
    }
    let args_id = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
    let tr = TraitRef { def: p.gx.lang.hash, args: args_id, bindings: EMPTY_BINDINGS };
    let sel = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        solver.select(&mut cx, &p.gx.index, &[], tr)
    };
    let Selection::Impl { id, args: impl_args, .. } = sel else { return };
    let record = p.gx.index.get(id);
    if record.synthetic != Synthetic::None || record.generics.params.is_empty() {
        return;
    }
    let named = |n: &str| record.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == n));
    let (Some(f), None) = (named("hash"), named("hash_slice")) else { return };
    if crate::check::collect::has_hash(p, &p.tys, self_ty) {
        p.gx.generic_hash.insert(adt, (f, impl_args.to_vec()));
    }
}

/// The `hash::<H>` instances of the written Hash impls
/// (`written_hash`) for every hasher type the hash glue may feed them
/// (W-STD-B): DefaultHasher and each concrete Adt with a written
/// `Hasher` impl. Pairs made in an earlier pass stay.
/// The sizes of `ensure_written_hash`'s inputs. During materialize they
/// only grow (inserts of new keys; `written_hash` and `dyn_keys` are set
/// before it), so an unchanged stamp means a pass would find nothing new.
fn hash_stamp(p: &Program) -> Option<(usize, usize, usize, usize)> {
    Some((p.gx.hasher_methods.len(), p.gx.written_hash.len(), p.gx.generic_hash.len(), p.gx.dyn_keys.len()))
}

fn ensure_written_hash(p: &mut Program, queue: &mut Vec<LocalDefId>) {
    use crate::ty::hash::{HashTy, mk_hash};
    if p.gx.written_hash.is_empty() && p.gx.generic_hash.is_empty() && p.gx.dyn_keys.is_empty() {
        return;
    }
    let mut user: Vec<AdtId> = p.gx.hasher_methods.keys().map(|&(a, _)| a).collect();
    user.sort_by_key(|a| a.0);
    user.dedup();
    let mut hashers = vec![mk_hash(&mut p.tys, HashTy::DefaultHasher, &[])];
    hashers.extend(user.into_iter().filter_map(|a| p.tys.full_adt_ty(a)).filter(|&t| !p.tys.flags(t).contains_param()));
    let mut adts: Vec<(AdtId, LocalDefId, Vec<GenericArg>)> = p.gx.written_hash.iter().map(|(&a, &f)| (a, f, Vec::new())).collect();
    adts.extend(p.gx.generic_hash.iter().map(|(&a, (f, args))| (a, *f, args.clone())));
    adts.sort_by_key(|(a, _, _)| a.0);
    for (a, f, impl_args) in adts {
        for &h in &hashers {
            if p.gx.hash_impls.get(&a).is_some_and(|v| v.iter().any(|&(t, _)| t == h)) {
                continue;
            }
            let before = p.fns.len();
            let mut args = impl_args.clone();
            args.push(GenericArg::Ty(h));
            let inst = fn_instance(p, f, &args);
            if inst.0 as usize >= before {
                queue.push(inst);
            }
            p.gx.hash_impls.entry(a).or_default().push((h, inst));
        }
    }
    // The dyn lookups' `hash::<H>` (`dyn_keys`): lifetimes erased, H the
    // template's one type param.
    let mut keys: Vec<AdtId> = p.gx.dyn_keys.keys().copied().collect();
    keys.sort_by_key(|a| a.0);
    for a in keys {
        let f = p.gx.dyn_keys[&a].hash;
        let params: Vec<ParamKind> =
            p.gx.fn_templates.get(f.0 as usize).cloned().flatten().map_or(Vec::new(), |t| t.generics.params.iter().map(|x| x.kind.clone()).collect());
        for &h in &hashers {
            if p.gx.dyn_keys[&a].hash_insts.iter().any(|&(t, _)| t == h) {
                continue;
            }
            let args: Vec<GenericArg> =
                params.iter().map(|k| if matches!(k, ParamKind::Lifetime) { GenericArg::Lifetime(Region::Erased) } else { GenericArg::Ty(h) }).collect();
            if args.iter().filter(|g| g.as_ty().is_some()).count() != 1 {
                continue;
            }
            let before = p.fns.len();
            let inst = fn_instance(p, f, &args);
            if inst.0 as usize >= before {
                queue.push(inst);
            }
            if let Some(k) = p.gx.dyn_keys.get_mut(&a) {
                k.hash_insts.push((h, inst));
            }
        }
    }
}

/// Path segment names that mark a use of a generic synthetic std Adt:
/// `Bound` (its variants and `RangeBounds`), `NonZero` (and its
/// aliases), `TrySendError` (and `try_send`), `TryLockError`, and `MaybeUninit` (and alloc's
/// uninit constructors). A synthetic std Adt
/// that needs the generic flags adds its names here, not a new scan.
const GENERIC_STD_NAMES: &[&str] = &[
    "Bound", "Included", "Excluded", "Unbounded", "RangeBounds",
    "NonZero", "NonZeroU8", "NonZeroU16", "NonZeroU32", "NonZeroU64", "NonZeroU128", "NonZeroUsize",
    "NonZeroI8", "NonZeroI16", "NonZeroI32", "NonZeroI64", "NonZeroI128", "NonZeroIsize",
    "TrySendError", "try_send", "MaybeUninit", "TryLockError",
    // alloc's uninit constructors make a `MaybeUninit<T>` with no
    // `MaybeUninit` in the text (`Box::write(Box::new_uninit(), v)`).
    "new_uninit", "new_zeroed", "new_uninit_slice", "new_zeroed_slice",
];

/// Method names that mark the same uses: the `RangeBounds` bound
/// methods, `NonZero::get` and `available_parallelism`, `try_send`,
/// `MaybeUninit`'s `uninit` and `write`, and the lock `try_*` calls
/// (their `Err` is a `TryLockError<G>`).
const GENERIC_STD_METHODS: &[&str] =
    &["start_bound", "end_bound", "get", "available_parallelism", "try_send", "uninit", "write", "try_lock", "try_read", "try_write"];

/// The name collect's `uses_cow` looks for.
pub const COW: &str = "Cow";
/// Names `materialize`'s scan looks for: `std::thread::Result<T>` (its
/// `thread` segment) and `panic_any` name a `dyn Any` with no `dyn` in
/// the text.
const THREAD: &str = "thread";
const PANIC_ANY: &str = "panic_any";

/// True for a name one of the whole-Ast scans that turn the generic
/// flags on looks for: `COW`, the two lists above, `THREAD`, and
/// `PANIC_ANY`. A warm body patch (driver/patch.rs `plain_body`) sends a
/// body that holds one to a full collect while the program is not yet
/// generic, so a new scanned name goes in one of these lists, never in a
/// list of its own (w-daemon-sound: the patch missed NonZero,
/// TrySendError, MaybeUninit, thread::Result, and panic_any).
pub fn flag_scan_name(name: &str) -> bool {
    [COW, THREAD, PANIC_ANY].contains(&name) || GENERIC_STD_NAMES.contains(&name) || GENERIC_STD_METHODS.contains(&name)
}

/// True when the program uses a generic synthetic std Adt (`Bound<T>`,
/// `NonZero<T>`, `TrySendError<T>`, `MaybeUninit<T>`) by one of the names above. These
/// Adts are registered for every program; their instances need the
/// generic machinery, but only in programs that use them (the perf
/// gate measures plain programs too). One pass over the Ast: collect
/// calls it once.
pub fn ast_uses_generic_std(ast: &Ast, interner: &Interner) -> bool {
    // Compare Syms, not strings: a name nobody interned is in no Ast node.
    let syms = |names: &[&str]| -> Vec<Sym> { names.iter().filter_map(|n| interner.find(n)).collect() };
    let (names, methods) = (syms(GENERIC_STD_NAMES), syms(GENERIC_STD_METHODS));
    let named = |segs: &[ast::PathSeg]| !names.is_empty() && segs.iter().any(|s| names.contains(&s.name));
    ast.exprs.iter().any(|e| match e {
        ast::Expr::MethodCall { name, .. } => methods.contains(name),
        ast::Expr::Path(segs) => named(segs),
        ast::Expr::QPath { trait_path, segs, .. } => named(trait_path) || named(segs),
        _ => false,
    }) || ast.tys.iter().any(|t| match t {
        TyExpr::Path(segs) => named(segs),
        TyExpr::QPath { trait_path, segs, .. } => named(trait_path) || named(segs),
        _ => false,
    }) || ast.pats.iter().any(|p| match p {
        ast::Pat::Path(segs) | ast::Pat::TupleStruct { path: segs, .. } | ast::Pat::Struct { path: segs, .. } => named(segs),
        _ => false,
    })
}

/// Materializes every reachable instance (section 4.1's mono
/// half for wave A): check plain fns for requests, create the
/// instances they name, check those, to a fixpoint. Discovery
/// check errors are discarded; the driver's own check reports
/// them against the finished tables. Returns mono's own errors
/// (instantiation depth and count caps, section 4.2).
pub fn materialize(p: &mut Program) -> Vec<Diag> {
    // Body checks here record reads whose deep Adt fingerprints walk the
    // whole type graph each time; the memo follows the changing program
    // so each walk runs once per program state (driver/graph.rs).
    p.fp_memo.follow_begin();
    let errs = materialize_all(p);
    p.fp_memo.follow_end();
    errs
}

fn materialize_all(p: &mut Program) -> Vec<Diag> {
    // Closures need the instance machinery too: each closure body is
    // its own fn with a slot, made here (ARCH 2.9, 4.1); and so do
    // `dyn Fn` values made from fn items, whose vtables only body
    // checks ask for. A `panic_any` call asks the same way: lowering
    // boxes its payload as `dyn Any + Send`, a dyn type no source
    // text names, so the eager vtable pass cannot see it.
    if !p.gx.user_generics {
        let user = |sp: &Span| !p.in_lang_methods(*sp);
        let closures = p.ast.exprs.iter().zip(&p.ast.expr_spans).any(|(e, sp)| matches!(e, ast::Expr::Closure { .. }) && user(sp));
        // `std::thread::Result<T>` names `Box<dyn Any + Send>` with no
        // `dyn` in the text (R26).
        let (thread, result) = (p.interner.intern(THREAD), p.interner.intern("Result"));
        let thread_result = |t: &TyExpr| match t {
            TyExpr::Path(segs) => segs.len() >= 2 && segs[segs.len() - 1].name == result && segs[segs.len() - 2].name == thread,
            _ => false,
        };
        let dyns = p.ast.tys.iter().zip(&p.ast.ty_spans).any(|(t, sp)| (matches!(t, TyExpr::Dyn { .. }) || thread_result(t)) && user(sp));
        let panic_any = p.interner.intern(PANIC_ANY);
        let panic_anys = p
            .ast
            .exprs
            .iter()
            .zip(&p.ast.expr_spans)
            .any(|(e, sp)| matches!(e, ast::Expr::Path(segs) if segs.last().is_some_and(|s| s.name == panic_any)) && user(sp));
        if closures || dyns || panic_anys || !p.gx.opaques.is_empty() {
            p.gx.has_generics = true;
            p.gx.user_generics = true;
        }
    }
    if !p.gx.has_generics {
        return Vec::new();
    }
    if p.gx.reuse.on {
        prefill_value_fps(p);
    }
    // Templates check once against their param env first; a
    // template error rejects the program before any instance is made.
    add_trait_method_stubs(p);
    let template_errs = template_check(p);
    if !template_errs.is_empty() {
        return template_errs;
    }
    crate::check::opaque::reveal_plain_rets(p);
    let mut errs: Vec<Diag> = Vec::new();
    // Adt instances named by plain signatures and fields first.
    for a in 0..p.gx.adt_info.len() {
        let fields: Vec<Ty> = p.adts[a].variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        for t in fields {
            ensure_global_adt_instances(p, t, 0);
        }
    }
    let first_instance = p.fns.len();
    let mut queue: Vec<LocalDefId> =
        (0..p.fns.len() as u32).map(LocalDefId).filter(|&f| p.gx.fn_class.get(f.0 as usize) == Some(&FnClass::Plain)).collect();
    // Generics from std's lang enum methods only: a plain body asks for
    // an instance only by naming one of the methods, and `lust check`
    // walks no instances, so the discovery pass (a second check of
    // every body) runs only for bodies that name one, and only in a
    // build. No user closures, dyn values, or generic Adts exist then.
    if !p.gx.user_generics {
        if p.gx.walk_instances {
            let names = lang_enum_method_names(p);
            queue.retain(|&f| names_lang_enum_method(p, f, &names));
        } else {
            queue.clear();
        }
    }
    // Std platform bodies are no roots in `lust check` (`check_skips`).
    queue.retain(|&f| !p.check_skips(f));
    let eager_from = queue.len();
    crate::mono::vtable::eager_vtables(p, &mut queue);
    // Method instances only the eager vtables made: no body has called
    // them or coerced their self type to `dyn` yet (`live_writers`).
    let mut eager_only: Vec<LocalDefId> = queue[eager_from..].to_vec();
    let mut live_writers: Vec<Ty> = Vec::new();
    // Eager vtable method instances of std impls (every `Error` impl
    // once std source names `dyn Error`, F3) are std bodies too: no
    // discovery roots in `lust check`, as above.
    queue.retain(|&f| !p.check_skips(f));
    let mut depths: FxMap<LocalDefId, usize> = FxMap::default();
    let mut rounds = 0usize;
    // The input sizes of the last `ensure_written_hash` pass (`hash_stamp`).
    let mut hash_done: Option<(usize, usize, usize, usize)> = None;
    p.gx.turn_marks.clear();
    let mut drop_done = 0u32;
    let mut drop_created = 0usize;
    let mut reuse = std::mem::take(&mut p.gx.reuse);
    let mut lang_checked: Vec<LocalDefId> = Vec::new();
    // Bodies checked again (`Checked::closure_map_pending`), with their
    // count. Each `impl Trait` fn a definer's opaque passes through can
    // take one more round before the definer's instance is made and
    // checked; `lust check` makes no instances, so it checks again once.
    let mut rechecked: FxMap<LocalDefId, u32> = FxMap::default();
    // Vtable requests of replayed discovery outputs that name a closure no
    // body has registered yet, with the requester's depth: a body that
    // boxes a generic definer's `impl Fn` return names the closure of the
    // definer's instance, which a request of the same body makes in a
    // later round (a fresh check waits for it, `closure_map_pending`).
    // Each is built once its closures exist (`replay_vtable`).
    let mut deferred_vts: Vec<(OwnedTy, OwnedTy, usize)> = Vec::new();
    // The Adt types of replayed discovery outputs already built here, by address: replays hand
    // out the types their entries share (`GenReuse::shared`: ~525k on tsgo, ~50k distinct), and
    // a type built once is in the store with its instances made. The map keeps each type alive,
    // so no other one takes its address. A fresh check's types stay out: kept to the end, they
    // spread the heap (90 MB more image pages on tsgo).
    let mut built: FxMap<*const OwnedTy, std::sync::Arc<OwnedTy>> = FxMap::default();
    let recheck_limit = if p.gx.walk_instances { 8 } else { 1 };
    // The body lints after a clean check add only errors. A discovery
    // check's errors matter only for its instance requests (a failed
    // body's stub picks are dropped, `discovery_out`) and for the reuse
    // store a one-shot compile has not (`GenReuse::on`). So a one-shot
    // compile skips them, and runs them only for a clean body whose
    // requests name a stub (`lint_tail`, below).
    let lints = reuse.on || !reuse.one_shot;
    // Window checks run only where a check records no reads: a read's
    // fingerprint can come from the deep memo, which logs no table read.
    // A build runs windows on one thread too: its early interning
    // (below) decides the global type numbering, which the emitted C
    // reads, so it must not depend on the thread count.
    let mut ahead: Ahead<Found> = Ahead::new(!p.record_reads && !reuse.on, p.gx.walk_instances);
    let compare = std::env::var_os("LUST_CHECK_PARDISC");
    while !queue.is_empty() {
        rounds += 1;
        if rounds > 4096 || p.fns.len() > 200_000 {
            errs.push(Diag::new(
                "L0611",
                Span::default(),
                "too many monomorphized instances",
                "Reduce the generic instantiations in this program.",
            ));
            break;
        }
        let mut next_queue: Vec<LocalDefId> = Vec::new();
        let mut recheck: Vec<LocalDefId> = Vec::new();
        let round = order_fuzz(std::mem::take(&mut queue), rounds);
        ahead.start(round.len());
        // The round's stored discovery entries, judged on the pool before
        // their turns (`GenReuse::prejudge`; the same verdicts).
        crate::driver::graph::FpMemo::sync(p);
        let mut prejudged = reuse.prejudge(p, &round);
        for (k, &fid) in round.iter().enumerate() {
            crate::driver::graph::FpMemo::sync(p);
            if ahead.fill(&round, k, |_| true, |&f| discover_one(p, f, lints)) && p.gx.walk_instances {
                // Early interning: every type the window's bodies name goes
                // into the global store now, in turn order, rather than at
                // each body's turn (its apply step below interns them
                // anyway). A window result that checked such a type as a
                // body type would go stale at the first earlier turn that
                // interned it; the stale ones check again now, in parallel.
                for found in ahead.window(k) {
                    let (adt_tys, reqs, closures, vts) = &found.out;
                    let args = reqs.iter().flat_map(|(_, a)| a.iter()).filter_map(|a| match a {
                        OwnedArg::Ty(t) => Some(t),
                        _ => None,
                    });
                    let closure_tys = closures.iter().flat_map(|c| [&c.env, &c.output].into_iter().chain(&c.inputs));
                    for owned in adt_tys.iter().map(|t| &**t).chain(args).chain(closure_tys).chain(vts.iter().flat_map(|(a, b)| [a, b])) {
                        build_owned_ty(p, owned);
                    }
                    // Each request's instance key, as its apply step makes it
                    // (`lift_request`): a caller's `instance_for` asks for it.
                    for (_, owned_args) in reqs {
                        let lifted = lift_request(p, owned_args);
                        p.tys.intern_args(&lifted);
                    }
                }
                ahead.recheck(&round, k, |&f| discover_one(p, f, lints));
            }
            let adts_before = p.adts.len();
            if rounds == 1 && p.gx.fn_class.get(fid.0 as usize) == Some(&FnClass::Plain) {
                p.gx.turn_marks.push((fid, p.gx.adt_created.len() as u32));
            }
            let depth = depths.get(&fid).copied().unwrap_or(0);
            // Snapshot everything the instance requests name,
            // then drop the checked body: it borrows the program
            // this loop is about to extend. A body whose stored
            // discovery still holds (driver session reuse) replays it.
            let pre = prejudged.get_mut(k).and_then(Option::take);
            let replayed = reuse.discovered_prejudged(p, fid, pre);
            let from_store = replayed.is_some();
            let (adt_tys_owned, requests_owned, closures_owned, vtables_owned) = if let Some(stored) = replayed {
                stored
            } else {
                reuse.discovery_checked += 1;
                let checked = match ahead.take(&p.gx.anon_wants, k) {
                    Some(found) => {
                        if let Some(path) = &compare {
                            compare_found(p, fid, lints, &found, path);
                        }
                        found
                    }
                    None => discover_one(p, fid, lints),
                };
                let clean = checked.clean;
                let (adt_tys, reqs, closures_owned, vts) = checked.out;
                // A body whose types still name a generic definer's
                // template closures (its instance is made from this very
                // body's requests) checks again next round; its requests
                // that name them would make instances over template
                // closures, which have no code.
                // A body still pending after its recheck (in `lust check`,
                // which makes no instances, or when the definer's instance
                // came from an earlier collect and was not walked again)
                // is not stored: its requests miss the ones that name
                // the definer's closures, and a replay in a later build
                // would never make those instances (daemon warm builds).
                let n = rechecked.get(&fid).copied().unwrap_or(0);
                let pending = checked.closure_map_pending || checked.closure_kind_pending;
                if pending && n < recheck_limit {
                    rechecked.insert(fid, n + 1);
                    recheck.push(fid);
                    // A call of a closure no check registered yet gave this
                    // body's closures provisional kinds and types: none of
                    // them (or the requests and types that name them) stand;
                    // the recheck after the definer makes them.
                    if checked.closure_kind_pending {
                        (Vec::new(), Vec::new(), Vec::new(), Vec::new())
                    } else {
                        (adt_tys, reqs, closures_owned, vts)
                    }
                } else {
                    if clean && !pending {
                        reuse.store_discovered(p, fid, &checked.reads, &adt_tys, &reqs, &closures_owned, &vts);
                    } else {
                        // A pending check of `lust check` (no instances) stays
                        // pending: its reads let a derive delta skip it.
                        let keep = !p.gx.walk_instances && clean && !checked.closure_kind_pending;
                        reuse.note_unstored(p, fid, &adt_tys, &reqs, &closures_owned, &vts, keep.then_some(&checked.reads));
                    }
                    (adt_tys, reqs, closures_owned, vts)
                }
            };
            reuse.note_closures(&closures_owned);
            register_closures(p, fid, closures_owned, FnClass::Closure);
            for owned in &adt_tys_owned {
                if from_store && built.insert(std::sync::Arc::as_ptr(owned), owned.clone()).is_some() {
                    continue;
                }
                let gt = build_owned_ty(p, owned);
                ensure_global_adt_instances(p, gt, 0);
            }
            // Vtables for this body's unsizing coercions, with the
            // method instances they point at (ARCH 2.8, 4.2).
            for (src, dyn_ty) in &vtables_owned {
                if from_store && names_unregistered_closure(p, src) {
                    deferred_vts.push((src.clone(), dyn_ty.clone(), depth));
                    continue;
                }
                replay_vtable(p, src, dyn_ty, depth, &mut live_writers, &mut depths, &mut next_queue);
            }
            for (template, owned_args) in requests_owned {
                // `lust check` stops at the template checks (ARCH 4.1):
                // a generic fn instance only replays its template's
                // checked resolutions, and its post-mono errors (the
                // recursion limit) are a build's, as in rustc. Closure
                // body fns are not requests: `register_closures` makes
                // them in both modes, so every closure body is checked.
                // A program with generic associated consts is the
                // exception: their per-instance values are evaluated only
                // in instance checks (`assoc_eval`), and an instance whose
                // value overflows is an error (rustc E0080) that `lust
                // check` must report as `lust build` does, so check walks
                // the instances then.
                if !p.gx.walk_instances && p.gx.assoc_const_tmpls.is_empty() {
                    continue;
                }
                if depth + 1 > crate::mono::MAX_INSTANCE_DEPTH {
                    errs.push(Diag::new(
                        "L0611",
                        p.fn_def(template).name_span,
                        "instantiation depth limit reached",
                        "Reduce the recursive generic instantiation.",
                    ));
                    continue;
                }
                let lifted = lift_request(p, &owned_args);
                let template_def = p.def_id(template);
                let args_id = p.tys.intern_args(&lifted);
                if let Some(&had) = p.gx.instance_by_key.get(&(template_def, args_id)) {
                    eager_only.retain(|&f| f != had);
                    continue;
                }
                // A lang enum method checks as a template before its
                // first instance (see `template_check`).
                if p.is_lang_method(template) && !lang_checked.contains(&template) {
                    lang_checked.push(template);
                    errs.extend(check_template(p, template, &mut reuse));
                }
                let inst = fn_instance(p, template, &lifted);
                depths.insert(inst, depth + 1);
                next_queue.push(inst);
            }
            // Drop glue for Adts made since the last pass: the template
            // rows first, then instances in creation order (their ids
            // are session places, not creation order). An Adt's Drop
            // selection cannot change while materialize runs (the impl
            // index is fixed), so each Adt is asked once, in the same
            // order as asking all of them after every body.
            let templates = p.gx.template_rows.unwrap_or(p.adts.len() as u32);
            let mut adt_ids: Vec<AdtId> = (drop_done..templates).map(AdtId).collect();
            drop_done = templates;
            adt_ids.extend_from_slice(&p.gx.adt_created[drop_created..]);
            drop_created = p.gx.adt_created.len();
            for a in adt_ids {
                ensure_drop_method(p, a, &mut next_queue);
                ensure_fmt_methods(p, a, &mut next_queue);
                ensure_glue_methods(p, a, &mut next_queue);
                ensure_hash_methods(p, a, &mut next_queue);
                ensure_generic_hash(p, a);
                ensure_iter_methods(p, a, &mut next_queue);
            }
            // A pass makes every (hashed Adt, hasher) instance it can, so
            // a pass when none of its input tables grew makes none.
            let stamp = hash_stamp(p);
            if stamp != hash_done {
                ensure_written_hash(p, &mut next_queue);
                hash_done = hash_stamp(p);
            }
            // A scan of every Adt row (check/sync.rs) reads the row count.
            if p.adts.len() != adts_before {
                crate::check::spec::wrote_all(crate::check::spec::tab::ADTS);
            }
        }
        ahead.end();
        // Deferred vtables whose closures this round registered; when no
        // work is left, the rest as they are (a closure that never came).
        let flush = next_queue.is_empty() && recheck.is_empty();
        for (src, dyn_ty, depth) in std::mem::take(&mut deferred_vts) {
            if !flush && names_unregistered_closure(p, &src) {
                deferred_vts.push((src, dyn_ty, depth));
            } else {
                replay_vtable(p, &src, &dyn_ty, depth, &mut live_writers, &mut depths, &mut next_queue);
            }
        }
        next_queue.extend(recheck);
        // Std bodies an ensured vtable or glue method named are no
        // discovery roots in `lust check` either (`check_skips`).
        next_queue.retain(|&f| !p.check_skips(f));
        queue = next_queue;
    }
    p.gx.reuse = reuse;
    ahead.report("discovery");
    crate::check::opaque::finish_opaque_rets(p);
    p.gx.mono_done = true;
    // W-SHIM: instances whose behavior lust cannot make exact. A
    // `write_fmt` slot of an eager vtable runs only through a `dyn`
    // made from its writer, so it counts only when some body coerces
    // that writer (a `Box<dyn Write>` of stdout next to a user writer
    // that is never `dyn` is fine).
    for i in first_instance..p.fns.len() {
        let f = LocalDefId(i as u32);
        if eager_only.contains(&f) && !crate::check::platform::writer_of(p, f).is_some_and(|w| live_writers.contains(&w)) {
            continue;
        }
        errs.extend(crate::check::platform::user_write_fmt_instance(p, f));
        errs.extend(crate::check::platform::io_copy_instance(p, f));
    }
    errs
}

/// `LUST_ORDER_FUZZ=<seed>` (a test knob, scripts/determinism_check.py
/// `--order-fuzz`): each materialize round takes its bodies in a shuffled
/// order, fixed by the seed and the round. Fn instances, Adt rows and types
/// are then made in another order, while the program means the same: an
/// output that changes is one that reads creation order (the order audit
/// for parallel apply). Off when unset.
fn order_fuzz(mut round: Vec<LocalDefId>, n: usize) -> Vec<LocalDefId> {
    static SEED: std::sync::OnceLock<Option<u64>> = std::sync::OnceLock::new();
    let Some(seed) = *SEED.get_or_init(|| std::env::var("LUST_ORDER_FUZZ").ok().and_then(|v| v.parse().ok())) else { return round };
    // A splitmix64 stream: no dependency, the same on every platform.
    let mut x = seed ^ (n as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    let mut next = || {
        x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for i in (1..round.len()).rev() {
        round.swap(i, (next() % (i as u64 + 1)) as usize);
    }
    round
}

/// The global args of one discovery request: each type built and
/// normalized, each const interned (`materialize`).
fn lift_request(p: &mut Program, owned_args: &[OwnedArg]) -> Vec<GenericArg> {
    owned_args
        .iter()
        .map(|a| match a {
            OwnedArg::Ty(e) => {
                let gt = build_owned_ty(p, e);
                GenericArg::Ty(normalize_global(p, gt))
            }
            OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
            OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
        })
        .collect()
}

/// Makes the value fingerprint of every const and static on the pool
/// (`graph::value_fp`) before a warm build's reuse checks ask for them one
/// by one (a const's `Sig` read folds it; tsgo's large tables made it a
/// quarter second of serial work per build). Each is a function of the
/// item's evaluated value only, made once per item, so the order it is
/// made in does not matter.
fn prefill_value_fps(p: &Program) {
    let consts: Vec<usize> = (0..p.consts.len()).collect();
    crate::pool::par_map(&consts, |&i| {
        let c = &p.consts[i];
        crate::driver::graph::value_fp(p, &c.value, &c.value_fp);
    });
    let statics: Vec<usize> = (0..p.statics.len()).collect();
    crate::pool::par_map(&statics, |&i| {
        let s = &p.statics[i];
        crate::driver::graph::value_fp(p, &s.value, &s.value_fp);
    });
}

/// Builds the vtable of one discovery output's unsizing coercion
/// (`materialize`) and queues the method instances it makes.
fn replay_vtable(
    p: &mut Program,
    src: &OwnedTy,
    dyn_ty: &OwnedTy,
    depth: usize,
    live_writers: &mut Vec<Ty>,
    depths: &mut FxMap<LocalDefId, usize>,
    next_queue: &mut Vec<LocalDefId>,
) {
    let src = build_owned_ty(p, src);
    let src = normalize_global(p, src);
    let dyn_ty = build_owned_ty(p, dyn_ty);
    let Some(principal) = crate::check::object::vtable_key(p, &p.tys, dyn_ty) else { return };
    if !live_writers.contains(&src) {
        live_writers.push(src);
    }
    let mut made: Vec<LocalDefId> = Vec::new();
    crate::mono::vtable::ensure_vtable(p, src, principal, &mut made);
    for inst in made {
        depths.insert(inst, depth + 1);
        next_queue.push(inst);
    }
}

/// True when type `t` names a closure that no body registered yet
/// (`Program::gx.closures`).
fn names_unregistered_closure(p: &Program, t: &OwnedTy) -> bool {
    let args = |a: &[OwnedArg]| a.iter().any(|g| matches!(g, OwnedArg::Ty(t) if names_unregistered_closure(p, t)));
    match t {
        OwnedTy::Leaf(_) => false,
        OwnedTy::Ref(_, _, e) | OwnedTy::RawPtr(_, e) | OwnedTy::Slice(e) | OwnedTy::Array(e, _) => names_unregistered_closure(p, e),
        OwnedTy::Tuple(es) => es.iter().any(|e| names_unregistered_closure(p, e)),
        OwnedTy::Closure(d, a) => !p.gx.closures.contains_key(d) || args(a),
        OwnedTy::Adt(_, a) | OwnedTy::FnDef(_, a) | OwnedTy::Opaque(_, a) | OwnedTy::Projection(_, a) => args(a),
        OwnedTy::FnPtr(_, inputs, output) => inputs.iter().any(|e| names_unregistered_closure(p, e)) || names_unregistered_closure(p, output),
        OwnedTy::Dyn(principal, _, _) => principal.as_ref().is_some_and(|(_, a, bs)| args(a) || bs.iter().any(|(_, g)| args(std::slice::from_ref(g)))),
    }
}

/// One fresh discovery check of a body (`discover_one`), owned: its
/// discovery output and what the walk reads of the check besides.
struct Found {
    out: crate::driver::gen_reuse::Discovered,
    closure_map_pending: bool,
    closure_kind_pending: bool,
    /// The check (with the lints a one-shot compile asks for) found no
    /// error.
    clean: bool,
    reads: crate::driver::graph::Reads,
}

impl Found {
    /// Field by field: the outputs as `build_owned_ty` reads them (a fn
    /// pointer's own input and output ids are body-local numbering, which
    /// it replaces; `stable`), the read sets by their `Debug` text.
    fn same(&self, o: &Found) -> bool {
        let tys = |v: &[OwnedTy]| v.iter().map(stable).collect::<Vec<_>>();
        let closures = |v: &[OwnedClosure]| {
            v.iter()
                .map(|c| {
                    let mut c = c.clone();
                    c.env = stable(&c.env);
                    c.output = stable(&c.output);
                    c.inputs = tys(&c.inputs);
                    c.bound_inputs = tys(&c.bound_inputs);
                    c.input_regions = c.input_regions.iter().map(|t| t.as_ref().map(stable)).collect();
                    c.output_region = c.output_region.as_ref().map(stable);
                    c.bound_output = c.bound_output.as_ref().map(stable);
                    c
                })
                .collect::<Vec<_>>()
        };
        let shared = |v: &[std::sync::Arc<OwnedTy>]| v.iter().map(|t| stable(t)).collect::<Vec<_>>();
        let reqs = |v: &[(LocalDefId, std::sync::Arc<[OwnedArg]>)]| {
            v.iter().map(|(t, a)| (*t, a.iter().map(stable_arg).collect::<Vec<_>>())).collect::<Vec<_>>()
        };
        let vts = |v: &[(OwnedTy, OwnedTy)]| v.iter().map(|(a, b)| (stable(a), stable(b))).collect::<Vec<_>>();
        let ((a0, a1, a2, a3), (b0, b1, b2, b3)) = (&self.out, &o.out);
        shared(a0) == shared(b0)
            && reqs(a1) == reqs(b1)
            && closures(a2) == closures(b2)
            && vts(a3) == vts(b3)
            && self.closure_map_pending == o.closure_map_pending
            && self.closure_kind_pending == o.closure_kind_pending
            && self.clean == o.clean
            && format!("{:?}", self.reads) == format!("{:?}", o.reads)
    }
}

/// `t` with each fn pointer's own input and output ids cleared: a
/// snapshot keeps them in its `FnSig`, but they are body-local numbering,
/// and `build_owned_ty` rebuilds both from the snapshot's parts.
fn stable(t: &OwnedTy) -> OwnedTy {
    let b = |e: &OwnedTy| Box::new(stable(e));
    let args = |a: &[OwnedArg]| a.iter().map(stable_arg).collect();
    match t {
        OwnedTy::Leaf(k) => OwnedTy::Leaf(*k),
        OwnedTy::Ref(r, m, e) => OwnedTy::Ref(*r, *m, b(e)),
        OwnedTy::RawPtr(m, e) => OwnedTy::RawPtr(*m, b(e)),
        OwnedTy::Slice(e) => OwnedTy::Slice(b(e)),
        OwnedTy::Array(e, n) => OwnedTy::Array(b(e), *n),
        OwnedTy::Tuple(ts) => OwnedTy::Tuple(ts.iter().map(stable).collect()),
        OwnedTy::Adt(d, a) => OwnedTy::Adt(*d, args(a)),
        OwnedTy::FnDef(d, a) => OwnedTy::FnDef(*d, args(a)),
        OwnedTy::Closure(d, a) => OwnedTy::Closure(*d, args(a)),
        OwnedTy::Opaque(d, a) => OwnedTy::Opaque(*d, args(a)),
        OwnedTy::Projection(d, a) => OwnedTy::Projection(*d, args(a)),
        OwnedTy::FnPtr(sig, ins, out) => {
            let sig = Binder { count: sig.count, value: FnSig { inputs: EMPTY_TYS, output: UNIT, ..sig.value } };
            OwnedTy::FnPtr(sig, ins.iter().map(stable).collect(), b(out))
        }
        OwnedTy::Dyn(pr, auto, r) => {
            let pr = pr.as_ref().map(|(d, a, bs)| (*d, args(a), bs.iter().map(|(bd, g)| (*bd, stable_arg(g))).collect()));
            OwnedTy::Dyn(pr, *auto, *r)
        }
    }
}

fn stable_arg(a: &OwnedArg) -> OwnedArg {
    match a {
        OwnedArg::Ty(t) => OwnedArg::Ty(stable(t)),
        other => other.clone(),
    }
}

/// Checks body `fid` for discovery against the program as it is now.
fn discover_one(p: &Program, fid: LocalDefId, lints: bool) -> Found {
    let (mut checked, mut discarded) = crate::check::check_fn_with(p, fid, lints);
    if !lints
        && discarded.is_empty()
        && checked.inst_requests.iter().any(|(t, _)| p.gx.fn_class.get(t.0 as usize) == Some(&FnClass::Stub))
        && let Some(d) = crate::check::lint_tail(p, fid, &mut checked)
    {
        discarded.push(d);
    }
    let out = discovery_out(p, &checked, &discarded);
    let (closure_map_pending, closure_kind_pending) = (checked.closure_map_pending, checked.closure_kind_pending);
    Found { out, closure_map_pending, closure_kind_pending, clean: discarded.is_empty(), reads: checked.reads }
}

/// Checks of one round run ahead in windows (check/spec.rs): at the turn
/// of item `k`, `fill` checks the next items of the round in parallel
/// against the program as it is then, and each item's turn takes its
/// result (`take`) only when nothing it read was written since; else
/// the item checks in its turn as before. Materialize's discovery bodies
/// and the template checks use it.
struct Ahead<R> {
    on: bool,
    /// Each window result: the check, what it read of the logged tables,
    /// its `anon_wants` notes, the steps it took, and the write stamp of
    /// the program state it read.
    found: Vec<Option<AheadResult<R>>>,
    /// The end of the last window.
    filled: usize,
    /// Windows, results taken, results stale, checks that stopped early,
    /// results checked again after early interning (`recheck`).
    counts: [usize; 5],
    window_ms: f64,
    max_steps: u64,
    /// Stale results by the table of the read that made them stale.
    stale_by: [usize; 64],
}

type AheadResult<R> = (R, crate::check::spec::Log, Vec<(u32, Option<ConstScalar>)>, u64, u32);

/// Steps (trait selections and new body types) a window check may take
/// before it stops; the item then checks in its turn.
const AHEAD_FUEL: u64 = 2_000_000;

/// Items per window.
const AHEAD_WIDTH: usize = 64;

impl<R: Send> Ahead<R> {
    /// Windows run when `on` (a one-shot compile: no read is recorded and
    /// no reuse store kept) with more than one thread or when `always`,
    /// and not under `LUST_NO_PARDISC=1`.
    fn new(on: bool, always: bool) -> Ahead<R> {
        let on = on && (always || crate::pool::threads() > 1) && std::env::var_os("LUST_NO_PARDISC").is_none();
        if on {
            crate::check::spec::quiet_hook();
        }
        Ahead { on, found: Vec::new(), filled: 0, counts: [0; 5], window_ms: 0.0, max_steps: 0, stale_by: [0; 64] }
    }

    /// A round of `n` items starts: the main thread logs its writes.
    fn start(&mut self, n: usize) {
        self.found.clear();
        self.found.resize_with(n, || None);
        self.filled = 0;
        if self.on {
            crate::check::spec::begin_round();
        }
    }

    /// The round's last turn ended.
    fn end(&mut self) {
        if self.on {
            crate::check::spec::end_round();
        }
        self.found.clear();
    }

    /// Before item `k`'s check: when the last window ends at `k`, checks
    /// the next window's items that `ahead` admits, and returns true.
    fn fill<T: Sync>(&mut self, round: &[T], k: usize, ahead: impl Fn(usize) -> bool, check: impl Fn(&T) -> R + Sync) -> bool {
        if !self.on {
            return false;
        }
        let stamp = crate::check::spec::new_stamp();
        if k < self.filled || round.len() - k < 2 {
            return false;
        }
        let end = (k + AHEAD_WIDTH).min(round.len());
        let at: Vec<usize> = (k..end).filter(|&i| ahead(i)).collect();
        self.filled = end;
        if at.len() < 2 {
            return false;
        }
        self.counts[0] += 1;
        self.check_at(round, &at, stamp, &check);
        true
    }

    /// Checks items `at` of `round` in parallel against the program as of
    /// write stamp `stamp` (now).
    fn check_at<T: Sync>(&mut self, round: &[T], at: &[usize], stamp: u32, check: &(impl Fn(&T) -> R + Sync)) {
        let t0 = std::time::Instant::now();
        let results = crate::pool::par_map(at, |&i| crate::check::spec::speculate(AHEAD_FUEL, || check(&round[i])));
        self.window_ms += t0.elapsed().as_secs_f64() * 1e3;
        for (&i, r) in at.iter().zip(results) {
            match r {
                Some((found, log, anon, steps)) => self.found[i] = Some((found, log, anon, steps, stamp)),
                None => {
                    self.found[i] = None;
                    self.counts[3] += 1;
                }
            }
        }
    }

    /// The results of the window that opened at `k`, in turn order.
    fn window(&self, k: usize) -> impl Iterator<Item = &R> {
        self.found[k..self.filled].iter().filter_map(|r| r.as_ref().map(|r| &r.0))
    }

    /// After the main thread wrote to logged tables between turns (early
    /// interning, `materialize`): checks again, in parallel, each result
    /// of the window that opened at `k` that those writes made stale.
    fn recheck<T: Sync>(&mut self, round: &[T], k: usize, check: impl Fn(&T) -> R + Sync) {
        let at: Vec<usize> = (k..self.filled)
            .filter(|&i| self.found[i].as_ref().is_some_and(|r| crate::check::spec::stale_since(&r.1, r.4).is_some()))
            .collect();
        let stamp = crate::check::spec::new_stamp();
        self.counts[4] += at.len();
        self.check_at(round, &at, stamp, &check);
    }

    /// Item `k`'s window result, when nothing it read was written since.
    /// Its `anon_wants` notes go in now, in turn order.
    fn take(&mut self, anon_wants: &AnonWants, k: usize) -> Option<R> {
        let (found, log, anon, steps, turn) = self.found.get_mut(k)?.take()?;
        if let Some(t) = crate::check::spec::stale_since(&log, turn) {
            self.counts[2] += 1;
            self.stale_by[t as usize] += 1;
            return None;
        }
        self.counts[1] += 1;
        self.max_steps = self.max_steps.max(steps);
        for (e, want) in anon {
            put_anon_want(anon_wants, e, want);
        }
        Some(found)
    }

    /// `LUST_PARDISC_STATS`: one line of counts, to stderr (`1`) or
    /// appended to the file the value names.
    fn report(&self, what: &str) {
        let Some(to) = std::env::var_os("LUST_PARDISC_STATS").filter(|_| self.on) else { return };
        let [w, taken, stale, out, again] = self.counts;
        let by: Vec<String> = self.stale_by.iter().enumerate().filter(|(_, n)| **n > 0).map(|(t, n)| format!("{t}:{n}")).collect();
        let line = format!(
            "pardisc-stats: {what}: windows {w} taken {taken} stale {stale} stopped {out} rechecked {again} window-ms {:.1} max-steps {} stale-by-table {}\n",
            self.window_ms,
            self.max_steps,
            by.join(",")
        );
        if to == "1" {
            eprint!("{line}");
        } else if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(to) {
            use std::io::Write;
            let _ = f.write_all(line.as_bytes());
        }
    }
}

/// A round cut short (an error, a cancelled background compile) still
/// stops the main thread's write log.
impl<R> Drop for Ahead<R> {
    fn drop(&mut self) {
        if self.on {
            crate::check::spec::end_round();
        }
    }
}

/// `LUST_CHECK_PARDISC=<log>`: checks discovery body `fid` again in order
/// and logs a difference from its window result `found`.
fn compare_found(p: &Program, fid: LocalDefId, lints: bool, found: &Found, path: &std::ffi::OsStr) {
    let fresh = discover_one(p, fid, lints);
    if fresh.same(found) {
        return;
    }
    let (a, b) = (&found.out, &fresh.out);
    let line = format!(
        "pardisc: {} {} differs: adt_tys {} reqs {} closures {} vtables {} map_pending {} kind_pending {} clean {} reads {}\n",
        std::env::args().skip(2).find(|a| a.ends_with(".rs")).unwrap_or_default(),
        p.interner.get(p.fn_info(fid).name),
        a.0 != b.0,
        a.1 != b.1,
        a.2 != b.2,
        a.3 != b.3,
        found.closure_map_pending != fresh.closure_map_pending,
        found.closure_kind_pending != fresh.closure_kind_pending,
        found.clean != fresh.clean,
        format!("{:?}", found.reads) != format!("{:?}", fresh.reads),
    );
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = f.write_all(line.as_bytes());
    }
}

/// The output of one fresh discovery check of a body (see
/// `materialize`): the Adt types it names, each once in first-seen
/// order; its instance requests; its closures; and its vtable requests
/// (concrete type, dyn type). The daemon's kept program compares an
/// edited body's output with its stored one (driver/patch.rs).
pub(crate) fn discovery_out(p: &Program, checked: &crate::check::Checked<'_>, discarded: &[Diag]) -> crate::driver::gen_reuse::Discovered {
    let closures_owned = snapshot_closures(checked).unwrap_or_default();
    // Each type once, in first-seen order: a body names the
    // same Adt type at many expressions, and every stored
    // copy is rebuilt on each discovery replay (driver
    // session reuse), while `ensure_global_adt_instances`
    // makes an instance only the first time. Every type enters
    // the global store (lowering and codegen read body types
    // there); only some can name an instance (`may_make_instances`).
    let mut adt_tys: Vec<std::sync::Arc<OwnedTy>> = Vec::new();
    let mut seen: crate::intern::FxMap<Ty, ()> = crate::intern::FxMap::default();
    for t in checked.expr_ty.iter().copied().chain(checked.locals.iter().map(|l| l.ty)) {
        if seen.insert(t, ()).is_none()
            && let Some(o) = snapshot_ty(&checked.tys, t)
        {
            adt_tys.push(std::sync::Arc::new(o));
        }
    }
    let mut vts: Vec<(OwnedTy, OwnedTy)> = Vec::new();
    for &(src, dyn_ty) in &checked.vtable_requests {
        if let (Some(a), Some(b)) = (snapshot_ty(&checked.tys, src), snapshot_ty(&checked.tys, dyn_ty)) {
            vts.push((a, b));
        }
    }
    let mut reqs: Vec<(LocalDefId, std::sync::Arc<[OwnedArg]>)> = Vec::new();
    for (template, raw_args) in &checked.inst_requests {
        if checked.closure_map_pending
            && raw_args.iter().any(|g| matches!(g, GenericArg::Ty(t) if crate::check::opaque::mentions_template_closure(p, &checked.tys, *t)))
        {
            continue;
        }
        let mut owned: Vec<OwnedArg> = Vec::new();
        let mut ok = true;
        for g in raw_args {
            match g {
                GenericArg::Ty(e) => match snapshot_ty(&checked.tys, *e) {
                    Some(o) => owned.push(OwnedArg::Ty(o)),
                    None => {
                        ok = false;
                        break;
                    }
                },
                GenericArg::Const(c) => match checked.tys.const_kind(*c) {
                    ConstKind::Infer(_) => {
                        ok = false;
                        break;
                    }
                    k => owned.push(OwnedArg::Const(k)),
                },
                GenericArg::Lifetime(r) => owned.push(OwnedArg::Lifetime(*r)),
            }
        }
        if ok {
            reqs.push((*template, owned.into()));
        }
    }
    // A body with errors fails the build (the driver's check reports
    // them), and its picks may name a trait method stub, which has no
    // instance (an opaque view's picks on an `impl Trait` value). Its
    // other requests stand.
    if discarded.iter().any(|d| d.severity == "error") {
        reqs.retain(|(t, _)| p.gx.fn_class.get(t.0 as usize) != Some(&FnClass::Stub));
    }
    (adt_tys, reqs, closures_owned, vts)
}

/// True when `ensure_global_adt_instances` can make an instance from
/// `t`: it holds an Adt application with arguments where that walk
/// looks (under references, pointers, slices, arrays, tuples, and Adt
/// arguments). For any other type the walk does nothing.
pub(crate) fn may_make_instances(t: &OwnedTy) -> bool {
    match t {
        OwnedTy::Adt(_, args) => !args.is_empty(),
        OwnedTy::Ref(_, _, e) | OwnedTy::RawPtr(_, e) | OwnedTy::Slice(e) | OwnedTy::Array(e, _) => may_make_instances(e),
        OwnedTy::Tuple(ts) => ts.iter().any(may_make_instances),
        _ => false,
    }
}

/// True when every Adt instance `ensure_global_adt_instances` makes from
/// `t` exists and was made before plain fn `x`'s turn in materialize's
/// first round (`GenTables::turn_marks`): that turn then makes nothing
/// from `t`. False when `x` had no turn there.
pub(crate) fn made_before_turn(p: &Program, t: Ty, x: LocalDefId) -> bool {
    let marks = &p.gx.turn_marks;
    let Ok(i) = marks.binary_search_by_key(&x.0, |m| m.0.0) else { return false };
    let before = &p.gx.adt_created[..(marks[i].1 as usize).min(p.gx.adt_created.len())];
    made_among(p, t, before, 0)
}

/// `made_before_turn` over the instances `before`, as deep as
/// `ensure_global_adt_instances` walks.
fn made_among(p: &Program, t: Ty, before: &[AdtId], depth: u32) -> bool {
    if depth > 32 {
        return true;
    }
    match p.tys.kind(t) {
        TyKind::Adt(def, a) => {
            let raw = p.tys.args(a);
            let generic = p.defs.local_adt(def).is_some_and(|template| !p.gx.adt_generics[template.0 as usize].params.is_empty());
            raw.iter().all(|g| g.as_ty().is_none_or(|e| made_among(p, e, before, depth + 1)))
                && (raw.is_empty() || !generic || p.tys.local_adt_instance(def, a).is_some_and(|inst| before.contains(&inst)))
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => made_among(p, e, before, depth + 1),
        TyKind::Tuple(ts) => p.tys.tys_of(ts).iter().all(|&e| made_among(p, e, before, depth + 1)),
        _ => true,
    }
}

/// `ensure_adt_instances_in` for types already in the global
/// store (signatures and fields at collect time).
fn ensure_global_adt_instances(p: &mut Program, t: Ty, depth: u32) {
    if depth > 32 {
        return;
    }
    match p.tys.kind(t) {
        TyKind::Adt(def, a) => {
            let raw: Vec<GenericArg> = p.tys.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_global_adt_instances(p, e, depth + 1);
                }
            }
            if !raw.is_empty()
                && let Some(template) = p.defs.local_adt(def)
                && !p.gx.adt_generics[template.0 as usize].params.is_empty()
            {
                adt_instance(p, template, &raw);
            }
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => {
            ensure_global_adt_instances(p, e, depth + 1)
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            for e in elems {
                ensure_global_adt_instances(p, e, depth + 1);
            }
        }
        _ => {}
    }
}

/// Appends trait default method bodies as template fns. Runs
/// after collect's fn pass: `Program::fns` must keep the AST fns
/// first, in AST order, because the driver maps slots by that
/// order (section 1.7). Mono materializes these templates per
/// impl instance on demand.
pub fn append_trait_default_templates(p: &mut Program) {
    let defaults: Vec<(DefId, TraitMethodTemplate)> =
        p.gx.trait_methods.iter().filter(|(_, t)| t.def(&p.ast).body.is_some()).map(|(&d, t)| (d, t.clone())).collect();
    for (method_def, tmpl) in defaults {
        let local = LocalDefId(p.fns.len() as u32);
        p.fn_defs.push(method_def);
        p.def_by_hash.entry(method_def.hash).or_insert(local);
        let trait_def = p.gx.index.trait_of_assoc(method_def);
        let mut data = crate::ty::defs::DefData::skeleton(
            crate::ty::defs::DefKind::Method,
            trait_def,
            tmpl.name,
            crate::ty::defs::Vis::Priv,
            tmpl.def(&p.ast).name_span,
        );
        data.generics = tmpl.generics.clone();
        data.sig = crate::ty::defs::SigData::Fn { params: tmpl.params.clone(), ret: tmpl.ret };
        p.defs.insert(method_def, data);
        p.fns.push(crate::check::collect::FnInfo {
            name: tmpl.name,
            loc: tmpl.loc,
            owner: None,
            self_kind: tmpl.self_kind,
            params: tmpl.params.clone(),
            ret: tmpl.ret,
            ret_borrows_from: tmpl.ret_borrows_from,
            is_const: tmpl.def(&p.ast).qual.is_const,
        });
        // The body may call the trait's own methods on Self: its env
        // has `Self: Trait<..>` over the trait's params, as in rustc.
        let mut env = tmpl.env.clone();
        if let Some(own) = own_trait_pred(p, method_def, &tmpl.generics) {
            env.push(own);
            env = body_env(&mut p.tys, &p.gx.index, &env);
        }
        p.gx.fn_templates.push(Some(FnTemplate { generics: tmpl.generics.clone(), env: env.clone() }));
        p.gx.fn_scopes.push(FnScope { env, scope: tmpl.scope.clone() });
        p.gx.fn_class.push(FnClass::Template);
    }
}

/// Proves one trait goal in pattern space (collect time): the
/// param env speaks first, then impls, with a confirmed impl's
/// own clauses proved the same way. `Sized` and the auto traits
/// hold by construction here (sizedness is checked where types
/// are used). A goal the solver can only defer counts as not
/// proved: at collect the bound must be in the env or in an impl.
/// `seen` holds the derived-Adt goals on the current walk: a
/// repeat is a recursive type (`Option<Box<S>>` in `S`), which
/// rustc proves from the derive impl itself, so it counts as
/// proved. Only derived-Adt steps push to `seen`; a cycle through
/// written impls alone still fails by depth, as rustc rejects it.
fn prove_trait_ref(
    p: &Program,
    solver: &mut crate::traits::solve::Solver,
    cx: &mut crate::traits::solve::PureCx,
    env: &[Predicate],
    tr: TraitRef,
    depth: u32,
    seen: &mut Vec<(DefId, Ty)>,
) -> bool {
    use crate::traits::solve::Selection;
    let (index, lang) = (&p.gx.index, &p.gx.lang);
    if depth > 24 {
        return false;
    }
    // A confirmed impl's nested goal names its Self by the probe
    // variable the header bound (`S: Send` with `S = ?3`), so the
    // structural answers below read Self deep-resolved; an unbound
    // variable proves nothing.
    let self_resolved = cx.tys.args(tr.args).first().and_then(|g| g.as_ty()).map(|t| crate::traits::solve::SolveCx::deep_resolve(cx, t));
    if tr.def == lang.sized {
        // Sized by structure (check::sized): a parameter is when the
        // env says so (an implicit `T: Sized` is in every env that has one).
        let Some(t) = self_resolved else { return false };
        if cx.tys.flags(t).contains_infer() {
            return false;
        }
        let sized_params = crate::check::sized::env_sized_params(&cx.tys, env, lang.sized);
        return crate::check::sized::is_sized(p, &mut cx.tys, t, &|q| sized_params.contains(&q));
    }
    // The builtin object impl: `dyn P` implements `P` and every
    // supertrait of `P` (the fmt traits included), with no impl record.
    if index.dyn_object_impl_holds(&mut cx.tys, tr) {
        return true;
    }
    // Auto traits by structure (ARCH 2.7); an open answer is not a proof.
    if lang.is_auto(tr.def) {
        let Some(t) = self_resolved else { return false };
        return crate::check::collect::auto_structural(p, &mut cx.tys, env, tr.def, t, &mut crate::check::collect::AutoSeen::default()) == Some(true);
    }
    // rustc's object candidate: `dyn Tr` implements its principal and
    // the principal's supertraits (`Box<dyn Write>: Write` through
    // `impl<W: Write + ?Sized> Write for Box<W>`, w-unsized).
    if let Some(t) = cx.tys.args(tr.args).first().and_then(|g| g.as_ty())
        && let t = crate::traits::solve::SolveCx::deep_resolve(cx, t)
        && let Some(principal) = crate::check::object::principal_of(&cx.tys, t)
    {
        let mut args: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
        for g in args.iter_mut() {
            if let GenericArg::Ty(x) = g {
                *x = crate::traits::solve::SolveCx::deep_resolve(cx, *x);
            }
        }
        args[0] = GenericArg::Ty(DYN_SELF);
        let to = TraitRef { def: tr.def, args: cx.tys.intern_args(&args), bindings: principal.bindings };
        if crate::check::object::upcast_path(p, &mut cx.tys, principal, to).is_some() {
            return true;
        }
    }
    // The derive family's container impls have no solver records
    // (`Vec<X>: Debug` from `X: Debug` in an impl's obligations,
    // where X is a projection the env bounds): decompose derive
    // family goals over the containers std forwards them through.
    // Self must read deep-resolved here: a confirmed impl's nested
    // goal names its Self by the probe variable the header bound
    // (`K: Debug` with `K = &T` from `W<&T>`), and the kind of the
    // variable itself is `Infer`, not `Ref` (fx-bench4-gaps).
    let fam_parts: Option<(Ty, bool)> = {
        let fam = [
            lang.debug,
            lang.clone,
            lang.copy,
            lang.hash,
            lang.eq,
            lang.partial_eq,
            lang.partial_ord,
            lang.ord,
            lang.default,
        ]
        .contains(&tr.def);
        let argv: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
        let t0 = argv.first().and_then(|g| g.as_ty());
        match (fam, t0) {
            (true, Some(t0)) => {
                let t = crate::traits::solve::SolveCx::deep_resolve(cx, t0);
                // `PartialEq` and `PartialOrd` goals carry `Rhs` as a
                // second arg; the component-wise impls need `Rhs = Self`.
                let arity_ok = match argv.len() {
                    1 => true,
                    2 if tr.def == lang.partial_eq || tr.def == lang.partial_ord => {
                        argv[1].as_ty().is_some_and(|r| crate::traits::solve::SolveCx::deep_resolve(cx, r) == t)
                    }
                    _ => false,
                };
                arity_ok.then_some((t, argv.len() == 2))
            }
            _ => None,
        }
    };
    if let Some((t, two_args)) = fam_parts {
        // `Copy` forwards through fewer containers than the
        // others: `Vec`, `Box`, `Rc`, and `Arc` are never Copy,
        // and a slice is not a sized value at all.
        let is_copy = tr.def == lang.copy;
        let is_default = tr.def == lang.default;
        // The container and derived-Adt forwards below are written
        // for Debug, Clone, Copy, and Hash; the other family traits
        // decompose only the record-less shapes (tuple, array,
        // slice, reference) and otherwise keep the solver's answer.
        let containers = tr.def == lang.debug || tr.def == lang.clone || tr.def == lang.copy || tr.def == lang.hash;
        // Set when `parts` are a derived Adt's fields: that is the
        // only step that can cycle (`S` derives `Hash`, a field is
        // `Option<Box<S>>`), and rustc proves such a cycle from the
        // derive impl itself, so a goal already in `seen` holds.
        let mut derived_adt = false;
        let parts: Option<Vec<Ty>> = match cx.tys.kind(t) {
            // A shared reference is always `Copy` and `Clone`
            // (`impl<T: ?Sized> Copy for &T` in core), with no
            // element goal: forwarding to `T` would ask `str: Copy`
            // for `&str: Copy` and fail a goal the solver's record
            // answered before Self read deep-resolved here.
            TyKind::Ref(_, m, _) if !m.is_mut() && (is_copy || tr.def == lang.clone) => Some(Vec::new()),
            // `&mut T` is never `Copy` or `Clone` (it does not forward to `T`).
            TyKind::Ref(_, m, _) if m.is_mut() && (is_copy || tr.def == lang.clone) => return false,
            // A reference defaults only as `&str` or `&[T]`, with no
            // element goal; the other family traits forward to `T`.
            TyKind::Ref(_, m, e) if is_default => matches!(cx.tys.kind(e), TyKind::Str | TyKind::Slice(_)).then_some(Vec::new()),
            TyKind::Ref(_, m, e) if !is_copy || !m.is_mut() => Some(vec![e]),
            // core's array `Default` stops at 32 elements (any
            // element type at length 0), as in `prove_field_trait`.
            TyKind::Array(e, n) if is_default => match cx.tys.const_kind(n) {
                ConstKind::Int(0) => Some(Vec::new()),
                ConstKind::Int(k) if k <= 32 => Some(vec![e]),
                _ => None,
            },
            TyKind::Array(e, _) => Some(vec![e]),
            TyKind::Slice(e) if !is_copy && !is_default => Some(vec![e]),
            // core's tuple impls of the derive family stop at 12
            // elements (`Clone` and `Copy` hold at every arity).
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = cx.tys.tys_of(ts).to_vec();
                let limited = tr.def != lang.clone && tr.def != lang.copy;
                (!limited || elems.len() <= 12).then_some(elems)
            }
            // Core implements the family traits for every raw
            // pointer, and all but `Default` for every fn pointer,
            // with no goal on the signature or pointee (they compare
            // and hash by address; a raw pointer defaults to null).
            // The solver has no records for these heads.
            TyKind::FnPtr(_) if !is_default => Some(Vec::new()),
            TyKind::RawPtr(..) => Some(Vec::new()),
            // `PhantomData<T>: Debug` is glue, for a `T` lust can name
            // (`collect::phantom_debug_text`); never through a record.
            _ if tr.def == lang.debug && cx.tys.local_adt(t).is_some_and(|a| p.is_phantom_adt(a)) => {
                if crate::check::collect::phantom_debug_text(p, &cx.tys, t).is_none() {
                    return false;
                }
                Some(Vec::new())
            }
            // std's owning iterators (vec, option, result `IntoIter`):
            // `Debug` and `Clone` from `T`'s; `vec::IntoIter` is `Default`
            // for every `T`; no `Copy` or `Hash` (no records).
            _ if let Some(e) = crate::check::collect::owning_iter_elem(&cx.tys, t) => {
                if is_default {
                    crate::check::collect::vec_into_iter_elem(&cx.tys, t).map(|_| Vec::new())
                } else if tr.def == lang.debug || tr.def == lang.clone {
                    Some(vec![e])
                } else {
                    None
                }
            }
            _ if !containers => None,
            _ => {
                let elem = if is_copy {
                    cx.tys.option_elem(t)
                } else {
                    cx.tys.vec_elem(t).or_else(|| cx.tys.option_elem(t)).or_else(|| cx.tys.smart_elem(t))
                };
                if let Some(e) = elem {
                    // std's `Clone` for `Rc<T>` and `Arc<T>` has no goal on
                    // `T`, `Box<str>` none on `str`, and `Box<[T]>` asks `T`.
                    let clone = tr.def == lang.clone;
                    match cx.tys.kind(e) {
                        _ if clone && cx.tys.rc_elem(t).is_some() => Some(Vec::new()),
                        TyKind::Str if clone => Some(Vec::new()),
                        TyKind::Slice(x) if clone => Some(vec![x]),
                        _ => Some(vec![e]),
                    }
                } else if cx.tys.result_args(t).is_some() {
                    cx.tys.result_args(t).map(|(a, b)| vec![a, b])
                } else if let Some(a) = cx.tys.local_adt(t) {
                    // A derived Adt: every field must hold, with
                    // this application's args substituted.
                    // The one trait this goal asks (the others go unread).
                    use crate::check::derive_delta::bit;
                    let asked = if tr.def == lang.copy {
                        bit::COPY
                    } else if tr.def == lang.clone {
                        bit::CLONE
                    } else if tr.def == lang.debug {
                        bit::DEBUG
                    } else {
                        bit::HASH
                    };
                    let derived = p.derive_has(a, asked);
                    if derived {
                        derived_adt = true;
                        let args: Vec<GenericArg> = cx.tys.adt_parts(t).map(|(_, a)| cx.tys.args(a).to_vec()).unwrap_or_default();
                        let raw: Vec<Ty> = p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
                        let mut fields: Vec<Ty> =
                            raw.into_iter().map(|f| if args.is_empty() { f } else { subst(&mut cx.tys, f, &args) }).collect();
                        // The derive bounds every type param by the trait
                        // (`impl<T: Debug> Debug for G<T>`), so each type arg
                        // must hold too, even one only a `fn() -> T` or
                        // `PhantomData<T>` field names. std's PhantomData
                        // impls have no bounds.
                        if !p.is_phantom_adt(a) {
                            fields.extend(args.iter().filter_map(|g| g.as_ty()));
                        }
                        Some(fields)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        };
        if let Some(parts) = parts {
            if derived_adt {
                if seen.contains(&(tr.def, t)) {
                    return true;
                }
                seen.push((tr.def, t));
            }
            let all = parts.into_iter().all(|e| {
                // A derived Adt's field whose type did not resolve: that
                // error is reported already (as in `prove_field_trait`).
                if derived_adt && cx.tys.kind(e) == TyKind::Error {
                    return true;
                }
                let args = if two_args {
                    cx.tys.intern_args(&[GenericArg::Ty(e), GenericArg::Ty(e)])
                } else {
                    cx.tys.intern_args(&[GenericArg::Ty(e)])
                };
                prove_trait_ref(p, solver, cx, env, TraitRef { def: tr.def, args, bindings: EMPTY_BINDINGS }, depth + 1, seen)
            });
            if derived_adt {
                seen.pop();
            }
            return all;
        }
    }
    match solver.select(cx, index, env, tr) {
        Selection::Impl { nested, .. } => nested.iter().all(|pred| match pred {
            Predicate::Trait(b) if b.count == 0 => {
                // A nested goal on a projection (`<Y as Bounds>::Primitive:
                // Prim`, from an associated type's bound) asks its normal
                // form: the solver does not select on a projection Self.
                let mut goal = b.value;
                let argv: Vec<GenericArg> = cx.tys.args(goal.args).to_vec();
                if argv.iter().any(|g| g.as_ty().is_some_and(|t| cx.tys.flags(t).contains_projection())) {
                    let normed: Vec<GenericArg> = argv
                        .iter()
                        .map(|&g| match g.as_ty() {
                            Some(t) => GenericArg::Ty(crate::traits::solve::normalize(solver, cx, index, env, t)),
                            None => g,
                        })
                        .collect();
                    goal.args = cx.tys.intern_args(&normed);
                }
                prove_trait_ref(p, solver, cx, env, goal, depth + 1, seen)
            }
            _ => true,
        }),
        Selection::ParamEvidence(_) => true,
        _ => false,
    }
}

/// Proves `ty: trait` for a field-type check, decomposing the
/// structural forms core implements component-wise (tuples,
/// arrays, references) since those have no impl records here.
fn prove_field_trait(p: &mut Program, env: &[Predicate], trait_def: DefId, ty: Ty) -> bool {
    let lang = p.gx.lang;
    let default = trait_def == lang.default;
    match p.tys.kind(ty) {
        // A field whose type did not resolve: that error is reported
        // already, and a derive error on top would name the wrong cause.
        TyKind::Error => true,
        // std's `PhantomData<T>` has every derivable trait at every `T`.
        // Lust lacks its Debug and Hash records (marker.rs), so a generic
        // field's proof at the definition answers here; a use of the
        // derived impl asks the glue at the instance, which rejects those.
        TyKind::Adt(..) if p.tys.flags(ty).contains_param() && p.tys.local_adt(ty).is_some_and(|a| p.is_phantom_adt(a)) => true,
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            // core's tuple impls of the derive family stop at 12
            // elements (`Clone` and `Copy` hold at every arity).
            let limited = [lang.debug, lang.partial_eq, lang.eq, lang.partial_ord, lang.ord, lang.hash, lang.default].contains(&trait_def);
            (!limited || elems.len() <= 12) && elems.iter().all(|&e| prove_field_trait(p, env, trait_def, e))
        }
        // core's `Default` impls: arrays of up to 32 elements (any
        // element type at length 0), `&str` and `&[T]`; no others.
        TyKind::Array(e, n) if default => match p.tys.const_kind(n) {
            ConstKind::Int(0) => true,
            ConstKind::Int(k) if k <= 32 => prove_field_trait(p, env, trait_def, e),
            _ => false,
        },
        TyKind::Ref(..) if default => crate::check::collect::ref_default(p, &p.tys, ty),
        // `Cow<B>` defaults through its Owned type, which the pure
        // solver cannot normalize at the unsized heads (str, [T]);
        // the structural glue answer decides, plus the derive's own
        // `B: Default` bound in the env for a parameter `B`.
        TyKind::Adt(..) if default && crate::check::collect::cow_arg(&p.tys, ty).is_some() => {
            crate::check::collect::has_default(p, &p.tys, ty)
                || env.iter().any(|pr| {
                    matches!(pr, Predicate::Trait(b) if b.value.def == trait_def
                        && p.tys.args(b.value.args).first().and_then(|g| g.as_ty())
                            == crate::check::collect::cow_arg(&p.tys, ty))
                })
        }
        // core: `&T` is `Clone` and `Copy` for every `T`; `&mut T` is neither.
        TyKind::Ref(_, m, _) if trait_def == lang.copy || trait_def == lang.clone => !m.is_mut(),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::Ref(_, _, e) => prove_field_trait(p, env, trait_def, e),
        // `Box`, `Rc`, and `Arc` are never `Copy` (`Box<[T]>`: the arm
        // below must not reach `T: Copy`).
        TyKind::Adt(..) if trait_def == lang.copy && crate::check::own::own_parts(&p.tys, ty).is_some() => false,
        // `Box`, `Rc`, and `Arc` of `str` or `[T]` follow the pointee for
        // the comparison and hash traits, as std's `T: ?Sized` impls do
        // (the pure solver has no `[T]` records; check/own.rs).
        TyKind::Adt(..)
            if !default
                && trait_def != lang.clone
                && let Some((_, e)) = crate::check::own::own_parts(&p.tys, ty)
                && matches!(p.tys.kind(e), TyKind::Str | TyKind::Slice(_)) =>
        {
            prove_field_trait(p, env, trait_def, e)
        }
        _ => {
            let mut a = vec![GenericArg::Ty(ty)];
            if trait_def == lang.partial_eq || trait_def == lang.partial_ord {
                a.push(GenericArg::Ty(ty));
            }
            let a = p.tys.intern_args(&a);
            prove_goal(p, env, TraitRef { def: trait_def, args: a, bindings: EMPTY_BINDINGS })
        }
    }
}

/// One where clause of an impl, instantiated with `args` (global
/// types), proven by the full solver. The derive glue's written-impl
/// check (`collect::glue_impl_pred_holds`) uses it for the bounds its
/// own walks do not cover: traits outside the derive family
/// (`S: BuildHasher` on a map's `PartialEq` impl) and bounds whose
/// Self is not a bare parameter. False when the instance still names
/// a parameter.
pub(crate) fn prove_inst_trait_ref(p: &Program, tr: TraitRef, args: &[GenericArg]) -> bool {
    let mut cx = crate::traits::solve::PureCx::new(&p.tys);
    let tr = crate::traits::index::subst_trait_ref_pub(&mut cx.tys, tr, args);
    let open = |g: &GenericArg| match *g {
        GenericArg::Ty(t) => cx.tys.flags(t).contains_param() || cx.tys.flags(t).contains_infer(),
        GenericArg::Const(c) => matches!(cx.tys.const_kind(c), ConstKind::Param(_) | ConstKind::Infer(_)),
        GenericArg::Lifetime(_) => false,
    };
    if cx.tys.args(tr.args).iter().any(open) || cx.tys.bindings(tr.bindings).iter().any(|(_, g)| open(g)) {
        return false;
    }
    let mut solver = crate::traits::solve::Solver::new();
    // A bound on a projection (`A::Item: Clone` with `A = [u8; 4]`) is
    // proven at the projection's normal form.
    let args: Vec<GenericArg> = cx
        .tys
        .args(tr.args)
        .to_vec()
        .into_iter()
        .map(|g| match g {
            GenericArg::Ty(t) => GenericArg::Ty(crate::traits::solve::normalize(&mut solver, &mut cx, &p.gx.index, &[], t)),
            g => g,
        })
        .collect();
    let tr = TraitRef { args: cx.tys.intern_args(&args), ..tr };
    prove_trait_ref(p, &mut solver, &mut cx, &[], tr, 0, &mut Vec::new())
}

/// One closed trait goal in an empty param env, past `finish_collect`
/// (a bounded const fn call in a const or static item,
/// `collect::prove_const_goals`). A goal of a derive-family trait goes
/// through the field prover, which decomposes the structural types
/// core implements those traits for component-wise; any other trait
/// has only its impls.
pub(crate) fn prove_closed_goal(p: &mut Program, tr: TraitRef) -> bool {
    match p.tys.args(tr.args) {
        [GenericArg::Ty(t)] if tr.bindings == EMPTY_BINDINGS && p.gx.index.derive_family.contains(&tr.def) => {
            let t = *t;
            // `&T` is `Copy` and `Clone` whatever `T` is (the field
            // prover follows the pointee).
            let lang = p.gx.lang;
            if (tr.def == lang.clone || tr.def == lang.copy) && matches!(p.tys.kind(t), TyKind::Ref(_, Mut::Shared, _)) {
                return true;
            }
            prove_field_trait(p, &[], tr.def, t)
        }
        _ => prove_goal(p, &[], tr),
    }
}

/// One trait goal with a fresh solver (collect-time proves are
/// independent of each other).
fn prove_goal(p: &Program, env: &[Predicate], tr: TraitRef) -> bool {
    let mut cx = crate::traits::solve::PureCx::new(&p.tys);
    let mut solver = crate::traits::solve::Solver::new();
    prove_trait_ref(p, &mut solver, &mut cx, env, tr, 0, &mut Vec::new())
}

/// The obligations one written impl owes its trait: the trait's
/// own predicates (supertraits, bounds on the trait's
/// parameters, and bounds on its associated types) with the
/// impl's trait ref substituted in and its associated types
/// rewritten to the impl's bindings. Runs at finish, when the
/// whole impl set exists (rustc E0277's class).
fn check_impl_obligations(p: &mut Program, errs: &mut Vec<Diag>, reach: Option<&crate::check::derive_delta::Reach>) {
    use crate::traits::index::{Synthetic, subst_predicate};
    let records: Vec<crate::traits::index::ImplRecord> = p
        .gx
        .index
        .all_impls()
        .filter(|(_, r)| r.synthetic == Synthetic::None && r.local && reach.is_none_or(|x| x.record(&p.tys, r)))
        .map(|(_, r)| r.clone())
        .collect();
    for rec in records {
        let Some(trec) = p.gx.index.trait_record(rec.trait_def).cloned() else { continue };
        if trec.generics.predicates.is_empty() {
            continue;
        }
        let subst_args: Vec<GenericArg> = p.tys.args(rec.trait_ref.args).to_vec();
        let self_ty = subst_args.first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
        let mut goals: Vec<TraitRef> = Vec::new();
        let mut statics: Vec<Ty> = Vec::new();
        for &pred in &trec.generics.predicates {
            let pred = subst_predicate(&mut p.tys, pred, &subst_args);
            // `trait Tr: 'static`: the impl's Self type must be `'static`;
            // `type Req: 'static`: the impl's binding of `Req` must be.
            if let Predicate::TypeOutlives(t, Region::Static) = pred {
                statics.push(rewrite_impl_projections(p, t, self_ty, &rec.assoc_tys));
                continue;
            }
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let old_args: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            let new_args: Vec<GenericArg> = old_args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(rewrite_impl_projections(p, t, self_ty, &rec.assoc_tys)),
                    other => other,
                })
                .collect();
            let args = p.tys.intern_args(&new_args);
            // An item bound's binding names the trait's own assoc types
            // too (`IntoIter: Iterator<Item = Self::Item>`): the impl's.
            let old_bindings: Vec<(DefId, GenericArg)> = p.tys.bindings(b.value.bindings).to_vec();
            let new_bindings: Vec<(DefId, GenericArg)> = old_bindings
                .into_iter()
                .map(|(d, g)| match g {
                    GenericArg::Ty(t) => (d, GenericArg::Ty(rewrite_impl_projections(p, t, self_ty, &rec.assoc_tys))),
                    other => (d, other),
                })
                .collect();
            let bindings = p.tys.intern_bindings(&new_bindings);
            goals.push(TraitRef { def: b.value.def, args, bindings });
        }
        if goals.is_empty() && statics.is_empty() {
            continue;
        }
        let env = elaborate_env(&mut p.tys, &p.gx.index, &rec.generics.predicates);
        let dyn_self = p.gx.static_dyn_impls.contains(&rec.def);
        if statics.iter().any(|&t| !crate::check::object::header_type_static(p, &env, t, dyn_self)) {
            let tname = p.display_path(trec.name);
            errs.push(Diag::new(
                "L0612",
                rec.span,
                format!("this impl of `{tname}` does not satisfy the `'static` bound the trait requires"),
                "Implement the trait for a type without references, or add `'static` bounds to the impl's type parameters.",
            ));
        }
        for goal in goals {
            if !prove_goal(p, &env, goal) {
                let gname = p.gx.index.trait_record(goal.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
                let tname = p.display_path(trec.name);
                errs.push(Diag::new(
                    "L0612",
                    rec.span,
                    format!("this impl of `{tname}` does not satisfy the `{gname}` bound the trait requires"),
                    format!("Add the `{gname}` impl or bound, or change the impl's types so the bound holds."),
                ));
            }
        }
    }
}

/// Supertrait cycles among user traits (rustc E0391): an edge
/// runs from a trait to each trait its own bounds name on
/// `Self`. Every trait on a cycle is reported once.
fn check_supertrait_cycles(p: &Program, errs: &mut Vec<Diag>) {
    let mut edges: FxMap<DefId, Vec<DefId>> = FxMap::default();
    for &def in p.gx.trait_names.values() {
        let Some(rec) = p.gx.index.trait_record(def) else { continue };
        let mut outs = Vec::new();
        for pred in &rec.generics.predicates {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let self_is_param0 = p
                .tys
                .args(b.value.args)
                .first()
                .and_then(|g| g.as_ty())
                .is_some_and(|t| matches!(p.tys.kind(t), TyKind::Param(pid) if pid.0 == 0));
            if self_is_param0 && p.gx.trait_names.values().any(|&d| d == b.value.def) {
                outs.push(b.value.def);
            }
        }
        edges.insert(def, outs);
    }
    // A trait is on a cycle when it can reach itself.
    for start in edges.keys().copied().collect::<Vec<_>>() {
        let mut seen: Vec<DefId> = Vec::new();
        let mut stack: Vec<DefId> = edges.get(&start).cloned().unwrap_or_default();
        let mut cyclic = false;
        while let Some(cur) = stack.pop() {
            if cur == start {
                cyclic = true;
                break;
            }
            if seen.contains(&cur) {
                continue;
            }
            seen.push(cur);
            if let Some(next) = edges.get(&cur) {
                stack.extend(next.iter().copied());
            }
        }
        if cyclic {
            let rec = p.gx.index.trait_record(start);
            errs.push(Diag::new(
                "L0110",
                rec.map_or(Span::default(), |r| r.span),
                format!("the supertraits of `{}` form a cycle", rec.map_or_else(|| "?".to_string(), |r| p.display_path(r.name))),
                "Remove one of the bounds so the trait graph has no cycle.",
            ));
        }
    }
}

/// A manual `Copy` impl needs every field to be `Copy` (rustc
/// E0204), and no type may be both `Copy` and `Drop` (E0184).
fn check_copy_impls(p: &mut Program, errs: &mut Vec<Diag>, reach: Option<&crate::check::derive_delta::Reach>) {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let mut copy_adts: Vec<DefId> = Vec::new();
    for (_, rec) in p.gx.index.all_impls() {
        if rec.trait_def == lang.copy
            && let TyKind::Adt(d, _) = p.tys.kind(rec.self_ty(&p.tys))
        {
            copy_adts.push(d);
        }
    }
    // Only `Drop` and `Copy` impls take part below: copy those alone (the
    // index holds every impl, derived ones included).
    let records: Vec<crate::traits::index::ImplRecord> =
        p.gx.index.all_impls().filter(|(_, r)| r.trait_def == lang.drop || r.trait_def == lang.copy).map(|(_, r)| r.clone()).collect();
    for rec in &records {
        // A derive delta: only impls whose types reach the edited Adt.
        if reach.is_some_and(|x| !x.record(&p.tys, rec)) {
            continue;
        }
        if rec.trait_def == lang.drop
            && rec.synthetic == Synthetic::None
            && let TyKind::Adt(d, _) = p.tys.kind(rec.self_ty(&p.tys))
            && copy_adts.contains(&d)
        {
            errs.push(Diag::new(
                "L0110",
                rec.span,
                "a type cannot implement both `Copy` and `Drop`",
                "Remove the `Copy` impl or the `Drop` impl.",
            ));
        }
        if rec.trait_def != lang.copy || rec.synthetic != Synthetic::None {
            continue;
        }
        let self_ty = rec.self_ty(&p.tys);
        // Only a struct, enum, or union of the crate can be made `Copy`
        // (rustc E0184 for `Box<Local>`, which has a destructor; E0206
        // for `&mut Local`; `&Local` conflicts with core's `&T` impl).
        let user_adt = match p.tys.kind(self_ty) {
            TyKind::Adt(def, _) => p.gx.adt_info.iter().any(|&(d, _)| d == def),
            _ => false,
        };
        if !user_adt && !p.std_source_span(rec.span) && !matches!(p.tys.kind(self_ty), TyKind::Ref(_, Mut::Shared, _)) {
            let boxed = matches!(p.tys.kind(self_ty), TyKind::Adt(d, _) if d == p.tys.builtins().boxed);
            errs.push(Diag::new(
                "L0110",
                rec.span,
                if boxed { "the trait `Copy` cannot be implemented for `Box`: it has a destructor" } else { "the trait `Copy` cannot be implemented for this type" },
                "Implement `Copy` for a struct or enum of this crate.",
            ));
            continue;
        }
        let TyKind::Adt(def, args) = p.tys.kind(self_ty) else { continue };
        let Some(idx) = p.gx.adt_info.iter().position(|&(d, _)| d == def) else { continue };
        let field_tys: Vec<Ty> = p.adt(AdtId(idx as u32)).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        let self_args: Vec<GenericArg> = p.tys.args(args).to_vec();
        let field_tys: Vec<Ty> = field_tys.iter().map(|&t| subst(&mut p.tys, t, &self_args)).collect();
        let env = elaborate_env(&mut p.tys, &p.gx.index, &rec.generics.predicates);
        for ft in field_tys {
            if !prove_field_trait(p, &env, lang.copy, ft) {
                errs.push(Diag::new(
                    "L0110",
                    rec.span,
                    "this type cannot be `Copy` because one of its fields is not `Copy`",
                    "Remove the `Copy` impl, or change the field to a `Copy` type.",
                ));
                break;
            }
        }
    }
}

/// Fills `glue_methods`: the written `Clone`, `Default`, and
/// `PartialEq` (with `Rhs = Self` and no `ne` of its own) methods
/// derived glue may call. Only non-generic impls on non-generic
/// local Adts qualify here (their method is a plain fn with a
/// slot); generic impls join per concrete Adt in
/// `ensure_glue_methods` during mono.
fn compute_glue_methods(p: &mut Program) {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let mut out: FxMap<(AdtId, DefId), LocalDefId> = FxMap::default();
    let mut cf_out: FxMap<AdtId, LocalDefId> = FxMap::default();
    let mut pcmp_out: FxMap<(AdtId, DefId), LocalDefId> = FxMap::default();
    let mut ref_default_out: FxMap<AdtId, LocalDefId> = FxMap::default();
    for (_, rec) in p.gx.index.all_impls() {
        if rec.synthetic != Synthetic::None || !rec.local || !rec.generics.params.is_empty() {
            continue;
        }
        // `impl Default for &'static A` (`ref_default_methods`).
        if rec.trait_def == lang.default
            && let TyKind::Ref(Region::Static | Region::Erased, Mut::Shared, inner) = p.tys.kind(rec.self_ty(&p.tys))
            && let TyKind::Adt(d, EMPTY_ARGS) = p.tys.kind(inner)
            && let Some(a) = p.tys.local_adt_of(d)
            && let Some(f) = rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == "default"))
            && !p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some())
        {
            ref_default_out.insert(a, f);
            continue;
        }
        let name = if rec.trait_def == lang.clone {
            "clone"
        } else if rec.trait_def == lang.default {
            "default"
        } else if rec.trait_def == lang.partial_eq {
            "eq"
        } else if rec.trait_def == lang.partial_ord {
            "partial_cmp"
        } else {
            continue;
        };
        let self_ty = rec.self_ty(&p.tys);
        let TyKind::Adt(d, args) = p.tys.kind(self_ty) else { continue };
        if args != EMPTY_ARGS {
            continue;
        }
        let Some(a) = p.tys.local_adt_of(d) else { continue };
        // A `Copy` type with a written `Clone`: core and derived code
        // copy it in some places and call its `clone` in others; the
        // glue does not model that, so such a field stays rejected.
        if rec.trait_def == lang.clone
            && (p.derives_of(a).copy
                || p.gx.index.impls_of_trait(lang.copy).iter().any(|&id| p.tys.kind(p.gx.index.get(id).self_ty(&p.tys)) == TyKind::Adt(d, EMPTY_ARGS)))
        {
            continue;
        }
        let has = |n: &str| rec.items.iter().any(|&m| p.local_def(m.hash).is_some_and(|l| p.name(p.fn_info(l).name) == n));
        // The `PCmp` glue's written method (`pcmp_methods`): a
        // `PartialOrd` with `Rhs = Self` and core's `lt`. An `Ord`
        // impl may exist too; its `cmp` is the `Cmp` glue's business.
        if rec.trait_def == lang.partial_ord
            && !has("lt")
            && p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty()) == Some(self_ty)
            && let Some(f) = rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == "partial_cmp"))
            && !p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some())
        {
            pcmp_out.insert((a, lang.partial_ord), f);
        }
        // `PartialEq` with `Rhs = Self` and core's `ne`: the eq glue
        // answers `!=` as `!eq`, which is then exactly core's default.
        if rec.trait_def == lang.partial_eq
            && (has("ne") || p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty()) != Some(self_ty))
        {
            continue;
        }
        // `PartialOrd` with `Rhs = Self`, core's `lt`/`le`/`gt`/`ge`,
        // and no `Ord` impl at all: then every ordering of this type,
        // alone or inside a tuple, slice, or derived body, is one
        // `partial_cmp` call per comparison, which is what the cmp
        // glue makes (`partial_cmp`/`cmp` read the glue once).
        if rec.trait_def == lang.partial_ord
            && (["lt", "le", "gt", "ge"].iter().any(|m| has(m))
                || p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty()) != Some(self_ty)
                || p.derives_of(a).ord
                || p.gx.index.impls_of_trait(lang.ord).iter().any(|&id| p.tys.kind(p.gx.index.get(id).self_ty(&p.tys)) == TyKind::Adt(d, EMPTY_ARGS)))
        {
            continue;
        }
        let found = rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == name));
        let Some(f) = found else { continue };
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            continue;
        }
        out.insert((a, rec.trait_def), f);
        // A written `clone_from` next to the `clone` just recorded:
        // the `clonefrom` glue calls it on the same terms.
        if rec.trait_def == lang.clone
            && let Some(cf) = rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == "clone_from"))
            && !p.gx.fn_templates.get(cf.0 as usize).is_some_and(|t| t.is_some())
        {
            cf_out.insert(a, cf);
        }
    }
    p.gx.glue_methods = out.into();
    p.gx.clone_from_methods = cf_out.into();
    p.gx.pcmp_methods = pcmp_out.into();
    p.gx.ref_default_methods = ref_default_out.into();
}

/// Fills `written_hash` and `borrow_impls` (W-STD-B): the written
/// `Hash` and `Borrow` impls the hash glue calls, on the terms of
/// `compute_glue_methods` (a non-generic impl on a non-generic local
/// Adt). A Hash impl with its own `hash_slice` is left out: slices of
/// the type then hash differently from the glue's loop, so such keys
/// stay rejected (L0640).
/// One dyn lookup type of a map key Adt (`GenTables::dyn_keys`): the dyn
/// type (object lifetime erased), its `Borrow::borrow`, `PartialEq::eq` and
/// `Hash::hash` templates, and the `hash::<H>` instances by hasher type
/// (`ensure_written_hash`).
#[derive(Clone, Debug)]
pub struct DynKey {
    pub q: Ty,
    pub borrow: LocalDefId,
    pub eq: LocalDefId,
    pub hash: LocalDefId,
    pub hash_insts: Vec<(Ty, LocalDefId)>,
}

fn compute_written_hash(p: &mut Program) {
    use crate::traits::index::Synthetic;
    let (mut hash, mut borrow) = (FxMap::default(), FxMap::default());
    let lifetimes_only = |g: &Generics| g.params.iter().all(|x| matches!(x.kind, ParamKind::Lifetime));
    for tr in [p.gx.lang.hash, p.gx.lang.borrow] {
        for &id in p.gx.index.impls_of_trait(tr) {
            let rec = p.gx.index.get(id);
            // A lifetime-only impl (`impl<'a> Borrow<dyn K + 'a> for Key`)
            // is one fn too: lifetimes are erased.
            let dyn_borrow = tr == p.gx.lang.borrow
                && lifetimes_only(&rec.generics)
                && p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty()).is_some_and(|q| matches!(p.tys.kind(q), TyKind::Dyn(..)));
            if rec.synthetic != Synthetic::None || !rec.local || !(rec.generics.params.is_empty() || dyn_borrow) {
                continue;
            }
            let TyKind::Adt(d, args) = p.tys.kind(rec.self_ty(&p.tys)) else { continue };
            let Some(a) = p.tys.local_adt_of(d).filter(|_| args == EMPTY_ARGS) else { continue };
            let named = |n: &str| rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == n));
            if tr == p.gx.lang.hash {
                if let (Some(f), None) = (named("hash"), named("hash_slice")) {
                    hash.insert(a, f);
                }
            } else if let (Some(f), Some(q)) = (named("borrow"), p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty())) {
                borrow.insert((a, q), f);
            }
        }
    }
    p.gx.written_hash = hash.into();
    p.gx.dyn_keys = dyn_keys(p, &borrow).into();
    p.gx.borrow_impls = borrow.into();
}

/// The dyn lookups of `borrow` (key Adt, dyn type) whose dyn type has a
/// written lifetime-only `Hash` impl (its own `hash`, no `hash_slice`)
/// and `PartialEq` impl with `Rhs = Self` (its own `eq`, no `ne`): the
/// glue calls those, as rustc's `HashMap::get` does through `Q: Hash + Eq`.
fn dyn_keys(p: &mut Program, borrow: &FxMap<(AdtId, Ty), LocalDefId>) -> FxMap<AdtId, DynKey> {
    use crate::traits::index::Synthetic;
    let mut out: FxMap<AdtId, DynKey> = FxMap::default();
    let lifetimes_only = |g: &Generics| g.params.iter().all(|x| matches!(x.kind, ParamKind::Lifetime));
    let mut by_key: FxMap<AdtId, Vec<(Ty, LocalDefId)>> = FxMap::default();
    for (&(a, q), &f) in borrow {
        if matches!(p.tys.kind(q), TyKind::Dyn(..)) {
            by_key.entry(a).or_default().push((q, f));
        }
    }
    for (a, qs) in by_key {
        // One dyn lookup type per key: the glue's CTy::Dyn names no trait.
        let [(q, borrow_fn)] = qs.as_slice() else { continue };
        let q = crate::check::object::erase_dyn_region(&mut p.tys, *q);
        let find = |p: &mut Program, tr: DefId, method: &str, bad: &str, rhs: bool| -> Option<LocalDefId> {
            let ids: Vec<_> = p.gx.index.impls_of_trait(tr).to_vec();
            let mut found = None;
            for id in ids {
                let rec = p.gx.index.get(id).clone();
                if rec.synthetic != Synthetic::None || !rec.local || !lifetimes_only(&rec.generics) {
                    continue;
                }
                let st = rec.self_ty(&p.tys);
                if crate::check::object::erase_dyn_region(&mut p.tys, st) != q {
                    continue;
                }
                if rhs {
                    let r = p.tys.args(rec.trait_ref.args).get(1).and_then(|g| g.as_ty());
                    if r.map(|r| crate::check::object::erase_dyn_region(&mut p.tys, r)) != Some(q) {
                        continue;
                    }
                }
                let named = |n: &str| rec.items.iter().find_map(|&m| p.local_def(m.hash).filter(|&l| p.name(p.fn_info(l).name) == n));
                if named(bad).is_some() {
                    return None;
                }
                found = named(method);
            }
            found
        };
        let (Some(eq), Some(hash)) = (find(p, p.gx.lang.partial_eq, "eq", "ne", true), find(p, p.gx.lang.hash, "hash", "hash_slice", false)) else {
            continue;
        };
        out.insert(a, DynKey { q, borrow: *borrow_fn, eq, hash, hash_insts: Vec::new() });
    }
    out
}

/// The derived traits that need more than the field checks in
/// collect (rustc E0277 for the generated impls): `Eq` needs
/// `PartialEq` on the type, `PartialOrd` needs `PartialEq`, `Ord`
/// needs `Eq` and `PartialOrd`; and `Eq`, `Hash`, `PartialOrd`,
/// `Ord`, and `Default` need every field to implement the trait.
/// The derived impl bounds each type parameter by the derived
/// trait, as rustc writes it, so those bounds join the field env.
/// Derived `Default` on an enum builds its unit `#[default]`
/// variant and needs nothing of the fields.
fn check_derive_bounds(p: &mut Program, errs: &mut Vec<Diag>, reach: Option<&crate::check::derive_delta::Reach>) {
    let lang = p.gx.lang;
    let n = p.gx.adt_info.len();
    let rows: Vec<usize> = (0..n).filter(|&i| reach.is_none_or(|x| x.row(p, i) && x.cold_row(p, i, 1))).collect();
    for idx in rows {
        let adt_id = AdtId(idx as u32);
        let (def, _) = p.gx.adt_info[idx];
        let (derives, span, is_enum, field_tys) = {
            let a = p.adt(adt_id);
            (p.derives_of(adt_id), a.span, a.is_enum, a.variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect::<Vec<Ty>>())
        };
        // A synthetic std Adt's derives are std's own, valid as written.
        if is_std_adt(&p.tys, adt_id) {
            continue;
        }
        // Derived `Copy` needs a `Clone` impl on the type, derived or
        // written; derived `Clone` needs every field to clone by
        // structure or through a written non-generic impl the glue
        // can call (`glue_methods`). Generic fields carry the bound
        // on the synthetic impl instead (checked per instance).
        if derives.copy {
            let has_clone_impl = derives.clone
                || p.gx.index.impls_of_trait(lang.clone).iter().any(|&id| {
                    matches!(p.tys.kind(p.gx.index.get(id).self_ty(&p.tys)), TyKind::Adt(d, _) if d == def)
                });
            if !has_clone_impl {
                errs.push(Diag::new("L0112", span, "deriving Copy requires Clone", "Add Clone to the derive list."));
            }
            // A field of a local type collect left for the impl index
            // (a written `impl Copy` on it).
            for &ft in &field_tys {
                if !p.tys.flags(ft).contains_param()
                    && crate::check::fmt::mentions_local_adt(&p.tys, ft)
                    && !crate::check::collect::is_copy(p, &p.tys, ft)
                {
                    let tn = crate::check::collect::ty_name(p, &p.tys, ft);
                    errs.push(Diag::new(
                        "L0112",
                        span,
                        format!("cannot derive Copy: field type `{tn}` does not implement Copy"),
                        "Derive Copy on the field type too, or remove Copy from the derive list.",
                    ));
                    break;
                }
            }
        }
        if derives.partial_eq {
            for &ft in &field_tys {
                if p.tys.flags(ft).contains_param() || crate::check::collect::has_eq(p, &p.tys, ft) {
                    continue;
                }
                let tn = crate::check::collect::ty_name(p, &p.tys, ft);
                errs.push(Diag::new(
                    "L0112",
                    span,
                    format!("cannot derive PartialEq: field type `{tn}` does not implement PartialEq"),
                    "Derive PartialEq on the field type too, or remove PartialEq from the derive list.",
                ));
                break;
            }
        }
        if derives.clone {
            for &ft in &field_tys {
                if p.tys.flags(ft).contains_param() || crate::check::collect::has_clone(p, &p.tys, ft) {
                    continue;
                }
                let tn = crate::check::collect::ty_name(p, &p.tys, ft);
                errs.push(Diag::new(
                    "L0112",
                    span,
                    format!("cannot derive Clone: field type `{tn}` does not implement Clone"),
                    "Derive Clone on the field type too, or remove Clone from the derive list.",
                ));
                break;
            }
        }
        check_generic_derive_fields(p, idx, derives, &field_tys, span, errs);
        if !(derives.eq || derives.hash || derives.partial_ord || derives.ord || derives.default) {
            continue;
        }
        // The type's own impl of a trait, derived or written.
        let has_impl = |p: &Program, on: bool, trait_def: DefId| {
            on || p.gx.index.impls_of_trait(trait_def).iter().any(|&id| {
                matches!(p.tys.kind(p.gx.index.get(id).self_ty(&p.tys)), TyKind::Adt(d, _) if d == def)
            })
        };
        let name = p.name(p.adt(adt_id).name).to_string();
        let mut supers_ok = true;
        if derives.eq && !has_impl(p, derives.partial_eq, lang.partial_eq) {
            errs.push(Diag::new(
                "L0110",
                span,
                "deriving `Eq` requires `PartialEq`",
                "Add `PartialEq` to the derive list, or implement it by hand.",
            ));
            supers_ok = false;
        }
        if derives.partial_ord && !has_impl(p, derives.partial_eq, lang.partial_eq) {
            errs.push(Diag::new(
                "L0110",
                span,
                format!("can't compare `{name}` with `{name}`: deriving `PartialOrd` requires `PartialEq`"),
                "Add `PartialEq` to the derive list, or implement it by hand.",
            ));
            supers_ok = false;
        }
        if derives.ord && !(has_impl(p, derives.eq, lang.eq) && has_impl(p, derives.partial_ord, lang.partial_ord)) {
            errs.push(Diag::new(
                "L0110",
                span,
                format!("deriving `Ord` requires `Eq` and `PartialOrd` on `{name}`"),
                "Add `Eq` and `PartialOrd` to the derive list, or implement them by hand.",
            ));
            supers_ok = false;
        }
        if !supers_ok {
            continue;
        }
        let base_env = elaborate_env(&mut p.tys, &p.gx.index, &p.gx.adt_generics[idx].predicates.clone());
        let wanted = [
            (derives.eq, lang.eq, "Eq"),
            (derives.hash, lang.hash, "Hash"),
            (derives.partial_ord, lang.partial_ord, "PartialOrd"),
            (derives.ord, lang.ord, "Ord"),
            (derives.default && !is_enum, lang.default, "Default"),
        ];
        for (wanted, trait_def, dname) in wanted {
            if !wanted {
                continue;
            }
            let env = derive_env(p, idx, &base_env, trait_def);
            for &ft in &field_tys {
                if !prove_field_trait(p, &env, trait_def, ft) {
                    errs.push(Diag::new(
                        "L0110",
                        span,
                        format!("deriving `{dname}` requires every field to implement `{dname}`"),
                        "Change the field type, or implement the trait by hand.",
                    ));
                    break;
                }
            }
        }
    }
}

/// The env a derived impl of `trait_def` on Adt row `idx` checks its
/// fields under, as rustc's derive writes the impl: the Adt's own
/// bounds (`base`, elaborated), `T: Trait` per type param, and
/// `B: Trait` per path part `Field::derive_bounds` holds (`T::Item`).
fn derive_env(p: &mut Program, idx: usize, base: &[Predicate], trait_def: DefId) -> Vec<Predicate> {
    let lang = p.gx.lang;
    let mut on: Vec<Ty> = Vec::new();
    for (i, param) in p.gx.adt_generics[idx].params.iter().enumerate() {
        if param.kind == ParamKind::Type {
            on.push(p.tys.intern(TyKind::Param(ParamId(i as u32))));
        }
    }
    for v in &p.adts[idx].variants {
        for f in &v.fields {
            for &b in &f.derive_bounds {
                if !on.contains(&b) {
                    on.push(b);
                }
            }
        }
    }
    let mut env = base.to_vec();
    for t in on {
        let mut a = vec![GenericArg::Ty(t)];
        if trait_def == lang.partial_eq || trait_def == lang.partial_ord {
            a.push(GenericArg::Ty(t));
        }
        let args = p.tys.intern_args(&a);
        env.push(Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS })));
    }
    elaborate_env(&mut p.tys, &p.gx.index, &env)
}

/// The derived `Debug`, `Clone`, `PartialEq`, and `Copy` impls of a
/// generic Adt row `idx`, checked at the definition as rustc checks them,
/// whether or not a use instantiates them: each field type that names a
/// type param must implement the trait under the derive's env
/// (`derive_env`), and derived `Copy` needs `Self: Clone` there. Fields
/// with no param are collect's (`check_derive_fields`) and the checks
/// above.
fn check_generic_derive_fields(p: &mut Program, idx: usize, derives: crate::check::collect::Derives, field_tys: &[Ty], span: Span, errs: &mut Vec<Diag>) {
    let lang = p.gx.lang;
    let generic: Vec<Ty> = field_tys.iter().copied().filter(|&ft| p.tys.flags(ft).contains_param()).collect();
    let wanted = [
        (derives.debug, lang.debug, "Debug"),
        (derives.clone, lang.clone, "Clone"),
        (derives.partial_eq, lang.partial_eq, "PartialEq"),
        (derives.copy, lang.copy, "Copy"),
    ];
    let has_params = p.gx.adt_generics[idx].params.iter().any(|q| q.kind != ParamKind::Lifetime);
    if !has_params || !wanted.iter().any(|w| w.0) {
        return;
    }
    let base = elaborate_env(&mut p.tys, &p.gx.index, &p.gx.adt_generics[idx].predicates.clone());
    for (on, trait_def, dname) in wanted {
        if !on {
            continue;
        }
        let env = derive_env(p, idx, &base, trait_def);
        if let Some(&ft) = generic.iter().find(|&&ft| !prove_field_trait(p, &env, trait_def, ft)) {
            let tn = crate::check::collect::ty_name(p, &p.tys, ft);
            errs.push(Diag::new(
                "L0112",
                span,
                format!("cannot derive {dname}: field type `{tn}` does not implement {dname}"),
                format!("Derive {dname} on the field type too, or remove {dname} from the derive list."),
            ));
        }
        // `impl<T: Copy> Copy for S<T>` needs `S<T>: Clone` under the same
        // env: a written `Clone` impl must cover it (a derived one does).
        if trait_def == lang.copy && !derives.clone {
            let own: Vec<GenericArg> = p.gx.adt_generics[idx]
                .params
                .iter()
                .enumerate()
                .map(|(i, d)| match d.kind {
                    ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i as u32))),
                    ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                    ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i as u32)))),
                })
                .collect();
            let def = p.gx.adt_info[idx].0;
            let self_ty = p.tys.mk_adt(def, &own);
            if !prove_field_trait(p, &env, lang.clone, self_ty) {
                errs.push(Diag::new("L0112", span, "deriving Copy requires Clone", "Add Clone to the derive list."));
            }
        }
    }
}

/// The collect checks a derive list feeds, run again on a kept program
/// after a derive delta toggled its synthetic records
/// (check/derive_delta.rs): the glue method tables, then each item check
/// over the items that reach the edited Adt (`Reach`; PLAN R13): field
/// checks, derive bounds, and Copy impls over the Adt and its field
/// users; impl obligations and written WF over the items whose types
/// name one of them; the where clause overflow check (E0275) over every
/// written impl; coherence over the impl pairs with such a side;
/// main's Termination and the const fn goals. Only the error count
/// matters to the caller (any error falls back).
pub(crate) fn recheck_derive_items(p: &mut Program, reach: &crate::check::derive_delta::Reach, errs: &mut Vec<Diag>) {
    compute_glue_tables(p);
    crate::driver::laps::mark("kept/derive glue");
    check_impl_obligations(p, errs, Some(reach));
    crate::check::where_overflow::check_impls(p, errs);
    check_copy_impls(p, errs, Some(reach));
    check_derive_bounds(p, errs, Some(reach));
    let deferred = crate::check::collect::check_derive_fields(p, &|i| reach.row(p, i) && reach.cold_row(p, i, 0), errs);
    p.gx.deferred_debug_fields = deferred;
    check_deferred_debug_fields(p, errs);
    crate::driver::laps::mark("kept/derive item checks");
    check_written_wf(p, errs, Some(reach));
    crate::driver::laps::mark("kept/derive wf");
    check_overlaps(p, errs, Some(reach));
    crate::driver::laps::mark("kept/derive overlap");
    crate::check::collect::check_main_termination(p, errs);
    let goals: Vec<(TraitRef, Span)> = p.const_goals.iter().filter(|(tr, _)| reach.trait_ref(&p.tys, tr)).cloned().collect();
    crate::check::collect::prove_const_goals(p, goals, errs);
}

/// The glue tables collect builds from the derive lists and impls
/// (`compute_glue_methods`, `compute_written_hash`), built again after a
/// derive delta or its undo (check/derive_delta.rs).
pub(crate) fn compute_glue_tables(p: &mut Program) {
    compute_glue_methods(p);
    compute_written_hash(p);
}

/// The `#[derive(Debug)]` field types collect deferred (see
/// `deferred_debug_fields`): each must implement Debug, through the
/// impl index now that every written impl is in it (W-STD-B).
fn check_deferred_debug_fields(p: &mut Program, errs: &mut Vec<Diag>) {
    for (ty, span) in std::mem::take(&mut p.gx.deferred_debug_fields) {
        if !prove_field_trait(p, &[], p.gx.lang.debug, ty) {
            errs.push(Diag::new(
                "L0112",
                span,
                format!("cannot derive Debug: field type `{}` does not implement Debug", crate::check::collect::ty_name(p, &p.tys, ty)),
                "Derive Debug on the field type too, or remove Debug from the derive list.",
            ));
        }
    }
}

/// The first index of each def in `adt_info`, built once per
/// pass. It answers exactly what a linear `position` scan over
/// `adt_info` answers (first match wins, duplicates included),
/// without the quadratic cost on crates with many Adts.
fn adt_first_index(p: &Program) -> FxMap<DefId, usize> {
    let mut m: FxMap<DefId, usize> = FxMap::default();
    m.reserve(p.gx.adt_info.len());
    for (i, &(def, _)) in p.gx.adt_info.iter().enumerate() {
        m.entry(def).or_insert(i);
    }
    m
}

/// Collects the trait goals one type owes to be well-formed:
/// for every application of a local Adt inside it, the Adt's
/// parameter predicates under the written arguments, for every
/// projection its trait ref (`<B as Tr>::Out` needs `B: Tr`), and
/// `Sized` for every part `check::sized::parts` names.
fn wf_goals(p: &mut Program, adt_idx: &FxMap<DefId, usize>, t: Ty, seen: &mut Vec<Ty>, out: &mut Vec<TraitRef>, sized: &mut Vec<TraitRef>) {
    use crate::traits::index::subst_predicate;
    if seen.contains(&t) || t == ERROR {
        return;
    }
    seen.push(t);
    let mut need: Vec<Ty> = Vec::new();
    crate::check::sized::parts(&p.tys, t, &mut |e| need.push(e));
    for e in need {
        sized.push(sized_ref(p, e));
    }
    let in_args = |p: &mut Program, seen: &mut Vec<Ty>, out: &mut Vec<TraitRef>, sized: &mut Vec<TraitRef>, a: ArgsId| {
        let argv: Vec<GenericArg> = p.tys.args(a).to_vec();
        for g in argv {
            if let Some(e) = g.as_ty() {
                wf_goals(p, adt_idx, e, seen, out, sized);
            }
        }
    };
    match p.tys.kind(t) {
        TyKind::Adt(d, a) => {
            if let Some(&idx) = adt_idx.get(&d)
                && !p.gx.adt_generics[idx].predicates.is_empty()
            {
                let argv: Vec<GenericArg> = p.tys.args(a).to_vec();
                for &pred in &p.gx.adt_generics[idx].predicates.clone() {
                    if let Predicate::Trait(b) = subst_predicate(&mut p.tys, pred, &argv)
                        && b.count == 0
                    {
                        out.push(b.value);
                    }
                }
            }
            if let Some(g) = adapter_iter_goal(p, t) {
                out.push(g);
            }
            in_args(p, seen, out, sized, a);
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => wf_goals(p, adt_idx, e, seen, out, sized),
        TyKind::Tuple(ts) => {
            for e in p.tys.tys_of(ts).to_vec() {
                wf_goals(p, adt_idx, e, seen, out, sized);
            }
        }
        TyKind::Projection(assoc, a) => {
            if let Some(def) = p.gx.index.trait_of_assoc(assoc.0) {
                out.push(TraitRef { def, args: a, bindings: EMPTY_BINDINGS });
            }
            in_args(p, seen, out, sized, a);
        }
        TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => in_args(p, seen, out, sized, a),
        TyKind::FnPtr(sig) => {
            let b = p.tys.sig(sig);
            for e in p.tys.tys_of(b.value.inputs).to_vec() {
                wf_goals(p, adt_idx, e, seen, out, sized);
            }
            wf_goals(p, adt_idx, b.value.output, seen, out, sized);
        }
        // The principal's args past `Self` (`dyn G<Vec<str>>`).
        TyKind::Dyn(b, _) => {
            if let Some(pr) = p.tys.dyn_bounds(b).principal {
                for g in p.tys.args(pr.value.args).iter().skip(1).copied().collect::<Vec<_>>() {
                    if let Some(e) = g.as_ty() {
                        wf_goals(p, adt_idx, e, seen, out, sized);
                    }
                }
            }
        }
        _ => {}
    }
}

/// The goals a written trait reference owes for the trait's own
/// parameter bounds (`trait Sup<T: Copy>` written `Sup<String>`
/// owes `String: Copy`, rustc E0277 at the item that writes it).
/// Only predicates on a bare non-Self parameter of the trait
/// count: a supertrait names the Self parameter and is an impl
/// obligation, and an associated type bound names a projection,
/// not one of this reference's arguments.
fn trait_ref_param_goals(p: &mut Program, tref: TraitRef, out: &mut Vec<TraitRef>) {
    use crate::traits::index::subst_predicate;
    let Some(rec) = p.gx.index.trait_record(tref.def).cloned() else { return };
    if rec.generics.predicates.is_empty() {
        return;
    }
    let argv: Vec<GenericArg> = p.tys.args(tref.args).to_vec();
    for &pred in &rec.generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        if b.count != 0 {
            continue;
        }
        let subject = p.tys.args(b.value.args).first().and_then(|g| g.as_ty());
        if !subject.is_some_and(|t| matches!(p.tys.kind(t), TyKind::Param(id) if id.0 >= 1)) {
            continue;
        }
        if let Predicate::Trait(sb) = subst_predicate(&mut p.tys, pred, &argv)
            && sb.count == 0
        {
            out.push(sb.value);
        }
    }
}

/// Elaboration through supertraits only, for proving
/// `trait_ref_param_goals`: like `elaborate_in`, but a trait
/// reference contributes only the predicates on its Self
/// parameter (its supertraits), never its parameter bounds.
/// The full elaboration assumes those bounds, so it cannot
/// prove them.
fn elaborate_supers_only(p: &mut Program, written: &[Predicate]) -> Vec<Predicate> {
    use crate::traits::index::subst_predicate;
    let mut out: Vec<Predicate> = Vec::new();
    let mut work: Vec<Predicate> = written.to_vec();
    let mut i = 0;
    while i < work.len() {
        let pred = work[i];
        i += 1;
        if out.contains(&pred) {
            continue;
        }
        out.push(pred);
        if let Predicate::Trait(b) = pred {
            for &(assoc, arg) in p.tys.bindings(b.value.bindings) {
                if let GenericArg::Ty(ty) = arg {
                    work.push(Predicate::AssocEq(Binder { count: b.count, value: AssocEqData { assoc, trait_args: b.value.args, ty } }));
                }
            }
            if let Some(rec) = p.gx.index.trait_record(b.value.def).cloned() {
                let argv: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
                for &q in &rec.generics.predicates {
                    let on_self = matches!(q, Predicate::Trait(qb)
                        if p.tys.args(qb.value.args).first().and_then(|g| g.as_ty())
                            .is_some_and(|t| matches!(p.tys.kind(t), TyKind::Param(id) if id.0 == 0)));
                    if on_self {
                        work.push(subst_predicate(&mut p.tys, q, &argv));
                    }
                }
            }
        }
    }
    out
}

/// The goal `t: Iterator` when `t` is a std adapter type (lust's rule,
/// stricter than rustc's WF, for written types in items and bodies): the
/// builtin uses of an adapter value (`next`, `for`, `count`) do not prove
/// the where clauses of its `Iterator` impl (`T: Clone` for
/// `Cloned<slice::Iter<T>>`), so the written type must.
pub(crate) fn adapter_iter_goal(p: &mut Program, t: Ty) -> Option<TraitRef> {
    let (k, _) = crate::ty::iter::iter_parts(&p.tys, t)?;
    if !k.is_adapter() {
        return None;
    }
    let args = p.tys.intern_args(&[GenericArg::Ty(t)]);
    Some(TraitRef { def: p.gx.lang.iterator, args, bindings: EMPTY_BINDINGS })
}

/// The goal `t: Sized`.
fn sized_ref(p: &mut Program, t: Ty) -> TraitRef {
    let args = p.tys.intern_args(&[GenericArg::Ty(t)]);
    TraitRef { def: p.gx.lang.sized, args, bindings: EMPTY_BINDINGS }
}

/// The `Self: Trait<..>` a trait method's signature and body assume
/// (rustc's implicit trait predicate), over the trait's own params
/// at the front of the method's combined generics.
fn own_trait_pred(p: &mut Program, method_def: DefId, generics: &Generics) -> Option<Predicate> {
    let td = p.gx.index.trait_of_method(method_def)?;
    let n = p.gx.index.trait_record(td)?.generics.params.len();
    let own: Vec<GenericArg> = generics.params[..n.min(generics.params.len())]
        .iter()
        .enumerate()
        .map(|(i, d)| match d.kind {
            ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i as u32))),
            ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
            ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i as u32)))),
        })
        .collect();
    let args = p.tys.intern_args(&own);
    Some(Predicate::Trait(Binder::plain(TraitRef { def: td, args, bindings: EMPTY_BINDINGS })))
}

/// Well-formedness of written types at collect: every type in
/// a signature, a field list, or an impl header must satisfy
/// the parameter bounds of the Adts it names and be `Sized` in
/// the positions `check::sized` names, under the item's own
/// bounds (rustc E0277 at the type). Value positions must be
/// `Sized` themselves: the params (by-value `self` included) and
/// return of a fn with a body, struct fields but the last, every
/// enum field. Body-level written types and literals queue the
/// same obligations in the checker. A where-clause predicate that
/// mentions no parameter of its item is a plain fact and must
/// hold as written.
fn check_written_wf(p: &mut Program, errs: &mut Vec<Diag>, reach: Option<&crate::check::derive_delta::Reach>) {
    use crate::traits::index::Synthetic;
    // (types, value types, item predicates, span); the generics
    // also serve the param-free predicate rule.
    // Each written type carries its own span (a field type's, for an
    // Adt), so a failed bound points at the type that owes it.
    // A derive delta: the fns collect had here (no instance made later).
    let n_fns = if reach.is_some() { p.gx.derive_marks[2].min(p.fns.len()) } else { p.fns.len() };
    // Its types or bounds must name the reach (the retain below decides;
    // this skips building the items that cannot).
    let fn_reaches = |p: &Program, i: usize| {
        reach.is_none_or(|x| {
            let f = &p.fns[i];
            let preds = |g: &Generics| g.predicates.iter().any(|q| x.pred(&p.tys, q));
            f.params.iter().any(|&t| x.ty(&p.tys, t))
                || x.ty(&p.tys, f.ret)
                || p.gx.written_projections.get(&p.fn_defs[i]).is_some_and(|w| w.iter().any(|&t| x.ty(&p.tys, t)))
                || p.gx.fn_templates.get(i).and_then(Option::as_ref).is_some_and(|t| preds(&t.generics))
                || p.defs.get(p.fn_defs[i]).is_some_and(|d| preds(&d.generics))
        })
    };
    let wanted: Vec<usize> = (0..n_fns).filter(|&i| fn_reaches(p, i)).collect();
    // A derive delta checks the types as written (`written_projections`):
    // collect checked them before it normalized them, and a projection
    // owes its trait ref.
    let written =
        |p: &Program, def: DefId, n: usize| p.gx.written_projections.get(&def).filter(|w| reach.is_some() && w.len() == n).cloned();
    let mut items: Vec<WfItem> = wanted
        .into_iter()
        .filter_map(|i| {
            let mut item = wf_fn_item(p, i)?;
            if let Some(w) = written(p, p.fn_defs[i], item.0.len()) {
                let span = item.3;
                item.1 = if item.1.is_empty() { Vec::new() } else { w.iter().map(|&t| (t, span)).collect() };
                item.0 = w.into_iter().map(|t| (t, span)).collect();
            }
            Some(item)
        })
        .collect();
    let at = |tys: Vec<Ty>, span: Span| -> Vec<(Ty, Span)> { tys.into_iter().map(|t| (t, span)).collect() };
    let methods: Vec<(DefId, Vec<Ty>, bool, Generics, Span)> =
        p.gx.trait_methods
            .iter()
            .map(|(&d, t)| {
                (
                    d,
                    t.params.iter().copied().chain([t.ret]).collect(),
                    t.def(&p.ast).body.is_some(),
                    t.generics.clone(),
                    t.def(&p.ast).name_span,
                )
            })
            .collect();
    for (method_def, tys, has_body, mut generics, span) in methods {
        if let Some(own) = own_trait_pred(p, method_def, &generics) {
            generics.predicates.push(own);
        }
        let values = if has_body { tys.clone() } else { Vec::new() };
        items.push((at(tys, span), at(values, span), generics, span));
    }
    for idx in 0..p.gx.adt_info.len() {
        if p.gx.adt_instance_of.get(idx).is_some_and(|i| i.is_some()) {
            continue;
        }
        let a = p.adt(AdtId(idx as u32));
        let n = a.variants.iter().map(|v| v.fields.len()).sum();
        let w = p.defs.def_of_adt(AdtId(idx as u32)).and_then(|d| written(p, d, n));
        // The field types, in field order (as written, see above).
        let field_ty = |k: usize, t: Ty| w.as_ref().map_or(t, |w| w[k]);
        let tys: Vec<(Ty, Span)> =
            a.variants.iter().flat_map(|v| &v.fields).enumerate().map(|(k, f)| (field_ty(k, f.ty), f.span)).collect();
        // Only a struct's last field may be unsized.
        let unsized_ok = usize::from(!a.is_enum);
        let mut k = 0;
        let mut values: Vec<(Ty, Span)> = Vec::new();
        for v in &a.variants {
            let take = v.fields.len().saturating_sub(unsized_ok);
            values.extend(v.fields.iter().enumerate().take(take).map(|(j, f)| (field_ty(k + j, f.ty), f.span)));
            k += v.fields.len();
        }
        items.push((tys, values, p.gx.adt_generics[idx].clone(), a.span));
    }
    for (_, rec) in p.gx.index.all_impls() {
        if rec.synthetic != Synthetic::None || !rec.local {
            continue;
        }
        let mut tys: Vec<Ty> = p.tys.args(rec.trait_ref.args).iter().filter_map(|g| g.as_ty()).collect();
        tys.extend(rec.assoc_tys.iter().map(|&(_, t)| t));
        items.push((at(tys, rec.span), Vec::new(), rec.generics.clone(), rec.span));
    }
    for (ty, generics, span) in &p.gx.wf_headers {
        items.push((vec![(*ty, *span)], Vec::new(), generics.clone(), *span));
    }
    for rec in p.gx.trait_names.values().filter_map(|&d| p.gx.index.trait_record(d)).cloned().collect::<Vec<_>>() {
        // The trait's own definition assumes `Self: Trait<..>` (as
        // its methods do, `own_trait_pred`): a bound on an
        // associated type (`type Out: Copy;`) names the projection,
        // whose well-formedness goal is that own predicate.
        let mut generics = rec.generics.clone();
        let own: Vec<GenericArg> = generics
            .params
            .iter()
            .enumerate()
            .map(|(i, d)| match d.kind {
                ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i as u32))),
                ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i as u32)))),
            })
            .collect();
        let args = p.tys.intern_args(&own);
        generics.predicates.push(Predicate::Trait(Binder::plain(TraitRef { def: rec.def, args, bindings: EMPTY_BINDINGS })));
        // An associated const's written type is a written type of
        // the trait (`const C: Need<String>` is E0277 with no
        // impl): the initializer pass alone cannot see a const
        // with no initializer.
        let const_tys: Vec<(Ty, Span)> = rec
            .assoc_items
            .iter()
            .filter(|&&(_, _, is_type)| !is_type)
            .filter_map(|&(assoc, _, _)| p.gx.trait_assoc_consts.get(&assoc).map(|&(t, _)| (t, rec.span)))
            .collect();
        items.push((const_tys, Vec::new(), generics, rec.span));
    }
    // A derive delta: only items whose types or bounds reach the edited Adt.
    if let Some(x) = reach {
        items.retain(|(tys, _, generics, _)| tys.iter().any(|&(t, _)| x.ty(&p.tys, t)) || generics.predicates.iter().any(|q| x.pred(&p.tys, q)));
    }
    let adt_idx = adt_first_index(p);
    check_default_wf(p, &adt_idx, errs);
    let mut memo = WfMemo::default();
    for item in items {
        check_wf_item(p, &adt_idx, item, &mut memo, errs);
    }
}

/// The types that passed in an earlier WF item with no predicates: under
/// an empty env a type's goals have one answer for every item (most
/// signatures have no where clause), so an item whose types all passed
/// owes nothing new.
#[derive(Default)]
struct WfMemo {
    wf_ok: FxMap<Ty, ()>,
    sized_ok: FxMap<Ty, ()>,
}

/// One item `check_written_wf` checks: its written types and value
/// types with their spans, its generics, and its span.
type WfItem = (Vec<(Ty, Span)>, Vec<(Ty, Span)>, Generics, Span);

/// The WF item of fn `i`, None for a fn checked from `trait_methods`.
fn wf_fn_item(p: &mut Program, i: usize) -> Option<WfItem> {
    // Stubs are trait method signatures again, and a trait
    // default template is its trait method: both are checked
    // from `trait_methods` (`check_written_wf`).
    if p.gx.fn_class.get(i) == Some(&FnClass::Stub) || p.gx.trait_methods.contains_key(&p.fn_defs[i]) {
        return None;
    }
    let at = |tys: Vec<Ty>, span: Span| -> Vec<(Ty, Span)> { tys.into_iter().map(|t| (t, span)).collect() };
    let info = p.fn_info(LocalDefId(i as u32));
    let mut tys: Vec<Ty> = info.params.clone();
    tys.push(info.ret);
    let values = if info.def(&p.ast).body.is_some() { tys.clone() } else { Vec::new() };
    // Plain fns keep their generics (with any where clause)
    // only in the def table, so read them from there.
    let mut generics = match p.gx.fn_templates.get(i).cloned().flatten() {
        Some(t) => t.generics,
        None => p.defs.get(p.def_id(LocalDefId(i as u32))).map_or_else(Generics::default, |d| d.generics.clone()),
    };
    let span = info.def(&p.ast).name_span;
    // A trait default body's signature assumes `Self: Trait`.
    if let Some(own) = own_trait_pred(p, p.def_id(LocalDefId(i as u32)), &generics) {
        generics.predicates.push(own);
    }
    Some((at(tys, span), at(values, span), generics, span))
}

/// `dst: From<src>` or `src: Into<dst>` between scalar types (`where
/// i64: From<u8>`). Core writes these with macros, and the pure solver
/// has no records for them; `Ctx::numeric_from_ok` is core's exact table.
fn scalar_conversion_holds(p: &Program, tr: TraitRef) -> bool {
    let args = p.tys.args(tr.args);
    let (Some(a), Some(b)) = (args.first().and_then(|g| g.as_ty()), args.get(1).and_then(|g| g.as_ty())) else {
        return false;
    };
    let (ak, bk) = (p.tys.kind(a), p.tys.kind(b));
    let scalar = |k: &TyKind| matches!(k, TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Float(_));
    if !scalar(&ak) || !scalar(&bk) {
        return false;
    }
    if tr.def == p.gx.lang.from {
        crate::check::Ctx::numeric_from_ok(bk, ak)
    } else if tr.def == p.gx.lang.into {
        crate::check::Ctx::numeric_from_ok(ak, bk)
    } else {
        false
    }
}

/// `check_written_wf` for one fn only: a signature delta runs it for
/// the fn it edited (`delta_audit::redo_sig`).
pub(crate) fn check_fn_wf(p: &mut Program, f: LocalDefId, errs: &mut Vec<Diag>) {
    if let Some(item) = wf_fn_item(p, f.0 as usize) {
        let adt_idx = adt_first_index(p);
        check_wf_item(p, &adt_idx, item, &mut WfMemo::default(), errs);
    }
}

/// Checks one WF item: Sized for its value types, the bounds its
/// written types and where clause types owe, and that each predicate
/// over none of its params holds.
fn check_wf_item(p: &mut Program, adt_idx: &FxMap<DefId, usize>, (tys, values, generics, span): WfItem, memo: &mut WfMemo, errs: &mut Vec<Diag>) {
    let plain = generics.predicates.is_empty();
    if plain && tys.iter().all(|(t, _)| memo.wf_ok.contains_key(t)) && values.iter().all(|(t, _)| memo.sized_ok.contains_key(t)) {
        return;
    }
    let errs_before = errs.len();
    let (tys_seen, values_seen): (Vec<Ty>, Vec<Ty>) = (tys.iter().map(|x| x.0).collect(), values.iter().map(|x| x.0).collect());
    let env = elaborate_env(&mut p.tys, &p.gx.index, &generics.predicates);
    let mut goals: Vec<(TraitRef, Span)> = Vec::new();
    // Trait parameter goals are proved in a supertrait-only env
    // below: full elaboration assumes exactly these bounds.
    let mut param_goals: Vec<(TraitRef, Span)> = Vec::new();
    // Sized goals from value positions and `parts` fail as
    // L0110; a failed param-bound goal keeps the L0612 shape.
    let mut sized_goals: Vec<(TraitRef, Span)> = Vec::new();
    for (t, tspan) in values {
        sized_goals.push((sized_ref(p, t), tspan));
    }
    let mut seen: Vec<Ty> = Vec::new();
    for (t, tspan) in tys {
        let (mut g2, mut s2) = (Vec::new(), Vec::new());
        wf_goals(p, &adt_idx, t, &mut seen, &mut g2, &mut s2);
        goals.extend(g2.into_iter().map(|g| (g, tspan)));
        sized_goals.extend(s2.into_iter().map(|g| (g, tspan)));
    }
    // The types a where clause names are written types too
    // (`where Vec<T>: Clone` needs `T: Sized`), and a written
    // trait reference owes the trait's own parameter bounds
    // under its arguments (`Sup<String>` for `Sup<T: Copy>`).
    for pred in &generics.predicates {
        if let Predicate::Trait(b) = pred {
            let mut named: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            named.extend(p.tys.bindings(b.value.bindings).iter().map(|(_, g)| *g));
            for g in named {
                if let Some(t) = g.as_ty() {
                    let (mut g2, mut s2) = (Vec::new(), Vec::new());
                    wf_goals(p, &adt_idx, t, &mut seen, &mut g2, &mut s2);
                    goals.extend(g2.into_iter().map(|g| (g, span)));
                    sized_goals.extend(s2.into_iter().map(|g| (g, span)));
                }
            }
            if b.count == 0 {
                let mut g2: Vec<TraitRef> = Vec::new();
                trait_ref_param_goals(p, b.value, &mut g2);
                param_goals.extend(g2.into_iter().map(|g| (g, span)));
            }
        }
    }
    // A predicate over no parameter of the item must hold
    // outright (`where String: Copy`).
    for pred in &generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        if b.count != 0 {
            continue;
        }
        let n_params = generics.params.len() as u32;
        let mentions_param = p
            .tys
            .args(b.value.args)
            .iter()
            .filter_map(|g| g.as_ty())
            .any(|t| (0..n_params).any(|i| ty_uses_param(&p.tys, t, i) || ty_uses_const_param(&p.tys, t, i)));
        if !mentions_param && !prove_goal(p, &[], b.value) && !scalar_conversion_holds(p, b.value) {
            let gname = p.gx.index.trait_record(b.value.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
            errs.push(Diag::new(
                "L0612",
                span,
                format!("the bound `{gname}` in this item's where clause does not hold"),
                "Remove the bound, or change the types so it holds.",
            ));
        }
    }
    if let Some((goal, gspan)) = sized_goals.into_iter().find(|(g, _)| !prove_goal(p, &env, *g)) {
        let t = p.tys.args(goal.args).first().and_then(|g| g.as_ty()).unwrap_or(ERROR);
        errs.push(crate::check::sized::unsized_diag(p, &p.tys, t, gspan));
        return;
    }
    // The trait parameter goals first, in the supertrait-only
    // env: the full env elaborates a written trait reference
    // into all of the trait's predicates, so it would prove
    // each of these goals from itself.
    if !param_goals.is_empty() {
        let wf_env = elaborate_supers_only(p, &generics.predicates);
        for (goal, gspan) in param_goals {
            if !prove_wf_goal(p, &wf_env, goal) {
                let gname = p.gx.index.trait_record(goal.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
                errs.push(Diag::new(
                    "L0612",
                    gspan,
                    format!("a type here does not satisfy the `{gname}` bound its definition requires"),
                    format!("Add the `{gname}` bound to this item, or change the type so the bound holds."),
                ));
                break;
            }
        }
    }
    for (goal, gspan) in goals {
        if !prove_wf_goal(p, &env, goal) {
            let gname = p.gx.index.trait_record(goal.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
            errs.push(Diag::new(
                "L0612",
                gspan,
                format!("a type here does not satisfy the `{gname}` bound its definition requires"),
                format!("Add the `{gname}` bound to this item, or change the type so the bound holds."),
            ));
            break;
        }
    }
    if plain && errs.len() == errs_before {
        memo.wf_ok.extend(tys_seen.into_iter().map(|t| (t, ())));
        memo.sized_ok.extend(values_seen.into_iter().map(|t| (t, ())));
    }
}

/// One bound goal of a written type (check_written_wf). core's
/// structural `Default` impls have no impl record for the pure
/// solver: `[T; N]` (N <= 32, any T at N = 0), tuples of at most 12
/// elements, `&str` and `&[T]`. A `Default` goal on those decomposes
/// to its elements (`LinkStore<K, [SymbolTable; 2]>` with `V: Default`).
fn prove_wf_goal(p: &mut Program, env: &[Predicate], goal: TraitRef) -> bool {
    let &[GenericArg::Ty(t)] = p.tys.args(goal.args) else { return prove_goal(p, env, goal) };
    if goal.def != p.gx.lang.default {
        return prove_goal(p, env, goal);
    }
    let elems: Vec<Ty> = match p.tys.kind(t) {
        TyKind::Array(e, n) => match p.tys.const_kind(n) {
            ConstKind::Int(0) => vec![],
            ConstKind::Int(k) if k <= 32 => vec![e],
            _ => return false,
        },
        TyKind::Tuple(ts) if p.tys.tys_of(ts).len() <= 12 => p.tys.tys_of(ts).to_vec(),
        TyKind::Tuple(_) => return false,
        TyKind::Ref(_, _, e) if matches!(p.tys.kind(e), TyKind::Str | TyKind::Slice(_)) => vec![],
        _ => return prove_goal(p, env, goal),
    };
    elems.into_iter().all(|e| {
        let args = p.tys.intern_args(&[GenericArg::Ty(e)]);
        prove_wf_goal(p, env, TraitRef { args, ..goal })
    })
}

/// Param defaults (rustc's wfcheck): a default that names no param
/// must be well-formed and sized when its param is, and each predicate
/// over exactly one param whose default names no param must hold for
/// that default (`struct S<T: Copy = String>` is E0277). Defaults that
/// name other params are checked at each use instead, as in rustc.
fn check_default_wf(p: &mut Program, adt_idx: &FxMap<DefId, usize>, errs: &mut Vec<Diag>) {
    use crate::traits::index::subst_predicate;
    let mut entries: Vec<(DefId, Vec<Option<GenericArg>>)> = p.gx.param_defaults.iter().map(|(d, v)| (*d, v.clone())).collect();
    entries.sort_by_key(|(d, _)| (d.krate.0, d.hash.0));
    for (def, defaults) in entries {
        let (generics, span, shift) = if let Some(a) = p.adt_by_def(def) {
            (p.gx.adt_generics[a.0 as usize].clone(), p.adt(a).span, 0usize)
        } else if let Some(rec) = p.gx.index.trait_record(def) {
            (rec.generics.clone(), rec.span, 1usize)
        } else {
            continue;
        };
        let n = generics.params.len() as u32;
        let names_param = |p: &Program, g: GenericArg| match g {
            GenericArg::Ty(t) => (0..n).any(|i| ty_uses_param(&p.tys, t, i) || ty_uses_const_param(&p.tys, t, i)),
            GenericArg::Const(c) => matches!(p.tys.const_kind(c), ConstKind::Param(_)),
            GenericArg::Lifetime(_) => false,
        };
        // Identity args, with each non-dependent default in its slot.
        let mut inst: Vec<GenericArg> = generics
            .params
            .iter()
            .enumerate()
            .map(|(i, prm)| match prm.kind {
                ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i as u32))),
                _ => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i as u32)))),
            })
            .collect();
        let mut concrete: Vec<bool> = vec![false; inst.len()];
        for (k, d) in defaults.iter().enumerate() {
            if let Some(d) = *d
                && !names_param(p, d)
                && shift + k < inst.len()
            {
                inst[shift + k] = d;
                concrete[shift + k] = true;
            }
        }
        let mut bad = false;
        for (i, &is_concrete) in concrete.iter().enumerate() {
            let Some(t) = inst[i].as_ty().filter(|_| is_concrete) else { continue };
            let mut goals: Vec<TraitRef> = Vec::new();
            let mut sized_goals: Vec<TraitRef> = Vec::new();
            wf_goals(p, adt_idx, t, &mut Vec::new(), &mut goals, &mut sized_goals);
            goals.append(&mut sized_goals);
            let bad_inner = !crate::check::collect::is_sized_ty(&p.tys, t)
                && !matches!(p.tys.kind(t), TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..));
            if bad_inner || goals.into_iter().any(|g| !prove_goal(p, &[], g)) {
                errs.push(Diag::new(
                    "L0612",
                    span,
                    format!("the default `{}` of a parameter is not a well-formed type", crate::check::collect::ty_name(p, &p.tys, t)),
                    "Change the default so every bound its types need holds.",
                ));
                bad = true;
            }
        }
        if bad {
            continue;
        }
        for &pred in &generics.predicates {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let mentioned: Vec<u32> = (0..n)
                .filter(|&i| {
                    p.tys.args(b.value.args).iter().chain(p.tys.bindings(b.value.bindings).iter().map(|(_, g)| g)).any(|g| match *g {
                        GenericArg::Ty(t) => ty_uses_param(&p.tys, t, i) || ty_uses_const_param(&p.tys, t, i),
                        GenericArg::Const(c) => p.tys.const_kind(c) == ConstKind::Param(i),
                        GenericArg::Lifetime(_) => false,
                    })
                })
                .collect();
            let [only] = mentioned.as_slice() else { continue };
            if !concrete[*only as usize] {
                continue;
            }
            let Predicate::Trait(inst_b) = subst_predicate(&mut p.tys, pred, &inst) else { continue };
            if !prove_goal(p, &[], inst_b.value) {
                let shown = inst[*only as usize].as_ty().map_or_else(|| "?".to_string(), |t| crate::check::collect::ty_name(p, &p.tys, t));
                let gname = p.gx.index.trait_record(b.value.def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
                errs.push(Diag::new(
                    "L0612",
                    span,
                    format!("the default `{shown}` does not satisfy the `{gname}` bound on its parameter"),
                    "Change the default, or relax the bound.",
                ));
            }
        }
    }
}

/// Coherence (section 2.6): overlapping trait impls of the user crate
/// (with each other and with std's shadow impls), and inherent methods
/// and associated consts defined twice for one type. Collect runs it
/// once; a derive delta runs it again (check/derive_delta.rs).
pub(crate) fn check_overlaps(p: &mut Program, errs: &mut Vec<Diag>, reach: Option<&crate::check::derive_delta::Reach>) {
    // Local to the user crate: std source module items (`Duration`,
    // `std::error::Error`) and shipped crates are upstream, so an
    // upstream release may add impls for them (no negative reasoning).
    let upstream_span = |p: &Program, s: Span| p.shipped_crate_at(s).is_some() || p.std_source_span(s);
    let mut upstream: FxMap<DefId, ()> = p.gx.index.trait_records().filter(|r| upstream_span(p, r.span)).map(|r| (r.def, ())).collect();
    for (i, adt) in p.adts.iter().enumerate() {
        if upstream_span(p, adt.span)
            && let Some(d) = p.defs.def_of_adt(AdtId(i as u32))
        {
            upstream.insert(d, ());
        }
    }
    let is_local = |d: DefId| d.krate == p.krate && !upstream.contains_key(&d);
    let lang = p.gx.lang;
    let by_construction = [lang.sized, lang.send, lang.sync, lang.unpin];
    // `Box` is the one fundamental Adt lust has (`Pin` is not a
    // supported type); the reference wrappers are structural. The
    // `Fn` traits are fundamental too (knowable for negative reasoning).
    let fundamental = [p.tys.builtins().boxed, lang.fn_, lang.fn_mut, lang.fn_once];
    // A derive delta tests only the pairs with a side that reaches the
    // edited Adt (no other pair's answer reads its derive list).
    let reaching: Option<Vec<bool>> = reach.map(|x| {
        let mut v = vec![false; p.gx.index.record_count()];
        for (id, rec) in p.gx.index.all_impls() {
            v[id.0 as usize] = x.record(&p.tys, rec);
        }
        v
    });
    let only = |id: crate::traits::ImplId| reaching.as_ref().is_none_or(|v| v[id.0 as usize]);
    let pairs = p.gx.index.coherence_overlaps(&mut p.tys, &fundamental, &by_construction, &is_local, &only);
    // Pairs of two upstream impls (std source among itself) are std's own.
    let user_impl = |id| {
        let rec = p.gx.index.get(id);
        rec.local && !upstream_span(p, rec.span)
    };
    let mut overlapping: Vec<crate::traits::ImplId> = pairs.into_iter().filter(|&(a, b)| user_impl(a) || user_impl(b)).map(|(_, later)| later).collect();
    // By record id: a derive delta's dead records keep their ids.
    let mut users: Vec<bool> = vec![false; p.gx.index.record_count()];
    for (id, rec) in p.gx.index.all_impls() {
        users[id.0 as usize] = rec.local && !upstream_span(p, rec.span);
    }
    let with_std = p.gx.index.shadow_overlaps(&mut p.tys, &fundamental, &by_construction, &is_local, &|id| users[id.0 as usize], &only);
    for id in with_std {
        if !overlapping.contains(&id) {
            overlapping.push(id);
        }
    }
    for later in overlapping {
        let rec = p.gx.index.get(later);
        let trait_name = p.gx.index.trait_record(rec.trait_def).map_or_else(|| "?".to_string(), |r| p.display_path(r.name));
        errs.push(Diag::new(
            "L0615",
            rec.span,
            format!("this impl of `{trait_name}` overlaps with another impl"),
            "Remove one of the impls, or narrow its types so they cannot both apply.",
        ));
    }
    // Inherent overlap (rustc E0592): two inherent methods of one
    // Adt with one name whose Self patterns can both apply.
    let mut inherent_dups: Vec<LocalDefId> = Vec::new();
    // A derive delta: only the groups with a Self pattern or bound that
    // reaches the edited Adt.
    let pat_reaches = |p: &Program, pat: Ty, g: &Generics| reach.is_none_or(|x| x.ty(&p.tys, pat) || g.predicates.iter().any(|q| x.pred(&p.tys, q)));
    for cands in p.gx.inherent_methods.clone().values() {
        if !cands.iter().any(|c| p.gx.inherent_self_pats.get(c).is_some_and(|(pat, g)| pat_reaches(p, *pat, g))) {
            continue;
        }
        for (i, &a) in cands.iter().enumerate() {
            for &b in &cands[i + 1..] {
                let (Some((pat_a, gen_a)), Some((pat_b, gen_b))) =
                    (p.gx.inherent_self_pats.get(&a).cloned(), p.gx.inherent_self_pats.get(&b).cloned())
                else {
                    continue;
                };
                if p.gx.index.inherent_pair_overlaps(&mut p.tys, pat_a, &gen_a, pat_b, &gen_b, &[], &by_construction, &is_local) {
                    inherent_dups.push(b);
                }
            }
        }
    }
    inherent_dups.sort_by_key(|f| f.0);
    inherent_dups.dedup();
    for f in inherent_dups {
        let info = p.fn_info(f);
        errs.push(Diag::new(
            "L0106",
            info.def(&p.ast).name_span,
            format!("`{}` is defined more than once", p.display_name(info.name)),
            "Rename one of the definitions, or narrow one impl's Self type so they cannot both apply.",
        ));
    }
    // Inherent associated consts share the rule, against each
    // other and against methods of the same name.
    let mut const_dups: Vec<u32> = Vec::new();
    for ((adt, name), idxs) in p.assoc_const_names.clone() {
        let adt_def = p.gx.adt_info.get(adt.0 as usize).map(|i| i.0);
        let methods: Vec<LocalDefId> =
            adt_def.and_then(|d| p.gx.inherent_methods.get(&(d, name))).cloned().unwrap_or_default();
        let consts_reach = idxs.iter().any(|i| p.gx.inherent_const_self.get(i).is_some_and(|(pat, g, _)| pat_reaches(p, *pat, g)));
        if !consts_reach && !methods.iter().any(|c| p.gx.inherent_self_pats.get(c).is_some_and(|(pat, g)| pat_reaches(p, *pat, g))) {
            continue;
        }
        for (n, &idx) in idxs.iter().enumerate() {
            let Some((pat, gens, _)) = p.gx.inherent_const_self.get(&idx).cloned() else { continue };
            let vs_const = idxs[..n].iter().any(|&other| {
                p.gx.inherent_const_self
                    .get(&other)
                    .is_some_and(|(opat, ogen, _)| p.gx.index.inherent_pair_overlaps(&mut p.tys, *opat, ogen, pat, &gens, &[], &by_construction, &is_local))
            });
            let vs_method = methods.iter().any(|&m| {
                p.gx.inherent_self_pats
                    .get(&m)
                    .is_some_and(|(mpat, mgen)| p.gx.index.inherent_pair_overlaps(&mut p.tys, *mpat, mgen, pat, &gens, &[], &by_construction, &is_local))
            });
            if vs_const || vs_method {
                const_dups.push(idx);
            }
        }
    }
    const_dups.sort_unstable();
    const_dups.dedup();
    for idx in const_dups {
        let c = &p.consts[idx as usize];
        let span = p.gx.inherent_const_self.get(&idx).map_or(Span::default(), |&(_, _, s)| s);
        errs.push(Diag::new(
            "L0106",
            span,
            format!("`{}` is defined more than once", p.display_name(c.name)),
            "Rename one of the definitions, or narrow one impl's Self type so they cannot both apply.",
        ));
    }
}

/// The last collect step before mono: synthetic impls, then
/// coherence over the whole index (section 2.6).
pub fn finish_collect(p: &mut Program, errs: &mut Vec<Diag>) {
    append_trait_default_templates(p);
    add_synthetic_impls(p);
    compute_glue_methods(p);
    compute_written_hash(p);
    crate::driver::laps::mark("collect/finish impls+glue");
    // Dyn compatibility needs the finished trait tables; the dyn
    // type checks over signatures run before mono builds vtables.
    p.gx.dyn_infos = crate::check::object::compute_dyn_infos(p);
    crate::check::object::check_signatures(p, errs);
    crate::check::caller::check_attrs(p, errs);
    check_supertrait_cycles(p, errs);
    check_impl_obligations(p, errs, None);
    crate::check::where_overflow::check_impls(p, errs);
    crate::check::ambig_assoc::check(p, errs);
    check_copy_impls(p, errs, None);
    p.gx.derive_marks[1] = p.gx.adt_created.len();
    check_derive_bounds(p, errs, None);
    check_deferred_debug_fields(p, errs);
    crate::driver::laps::mark("collect/finish item checks");
    // Well-formedness reads the written projections (each owes its
    // trait ref, where clauses included); normalization comes after.
    p.gx.derive_marks[2] = p.fns.len();
    check_written_wf(p, errs, None);
    crate::check::outlives::check_all(p, errs);
    errs.extend(crate::borrowck::check_impl_supers(p));
    crate::driver::laps::mark("collect/finish wf+outlives");
    normalize_signatures(p);
    crate::check::coherence_std::add_std_shadow_impls(p);
    crate::driver::laps::mark("collect/finish normalize");
    check_overlaps(p, errs, None);
    // Mono runs last: it checks bodies against the finished
    // tables and appends every reachable instance. Plain fns that
    // return `impl Trait` get their hidden types first.
    crate::driver::laps::mark("collect/finish overlap");
    if errs.is_empty() {
        crate::check::opaque::reveal_plain(p);
        crate::driver::laps::mark("collect/finish reveal");
        errs.extend(materialize(p));
        crate::driver::laps::mark("collect/finish materialize");
    }
    if errs.is_empty() {
        crate::check::const_body::check_all(p, errs);
        crate::driver::laps::mark("collect/finish const bodies");
    }
}
