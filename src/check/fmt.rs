// The checker side of `core::fmt` (W-STD-B; ty/fmt.rs, runtime/fmt.h).
//
// User `impl Display` and `impl Debug` for local Adts, the Formatter
// and Debug builder methods, `write!` through `write_fmt`, and `fmt`
// called on a builtin value inside an impl. Format arguments of a type
// with a user impl prove the trait through the obligation queue; the
// impl's `fmt` instance is what cgen's glue calls (`gx.fmt_methods`).
//
// Rule zero: methods Rust declares on these types that lust has no
// port of reject with L0640. A `format_args!` value is an
// `fmt::Arguments` in every position; it formats its arguments at
// each use, as in rustc (cgen/fmt.rs `format_args_value`).
use super::*;
use crate::ty::fmt::{FmtTy, fmt_kind, fmt_ty};

/// Formatter and builder methods Rust declares that lust does not
/// implement yet: a call rejects with L0640 naming the method.
const DECLARED_ONLY: &[&str] = &["align", "flags", "options", "with_options", "sign", "field_with", "entry_with", "key_with", "value_with"];

/// The user (written, not derived) impl of `trait_def` whose Self
/// pattern heads `t`'s Adt def, when it applies to every args of that
/// Adt with no where clause: then `t: trait` holds by structure. A
/// conditional or specialized impl answers through the solver instead.
pub fn user_impl_holds(p: &Program, tys: &impl TyIntern, t: Ty, trait_def: DefId) -> bool {
    use crate::traits::index::{SelfHead, Synthetic};
    let Some((def, _)) = tys.adt_parts(t) else { return false };
    // Written impls only (`peek`: the derived records it skips are no read).
    p.gx.index.impls_of_trait(trait_def).iter().any(|&id| {
        let rec = p.gx.index.peek(id);
        rec.synthetic == Synthetic::None
            && rec.head == SelfHead::Adt(def)
            && rec.generics.predicates.iter().all(|pr| matches!(pr, Predicate::Trait(b) if b.value.def == p.gx.lang.sized))
            && match p.tys.kind(rec.self_ty(&p.tys)) {
                TyKind::Adt(_, a) => {
                    let args = p.tys.args(a);
                    args.iter().enumerate().all(|(i, g)| g.as_ty().is_none_or(|t| p.tys.kind(t) == TyKind::Param(ParamId(i as u32))))
                }
                _ => false,
            }
    })
}

/// True when `t` holds a local (non-builtin) Adt anywhere.
pub fn mentions_local_adt(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) => mentions_local_adt(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_local_adt(tys, e)),
        TyKind::Adt(_, a) => tys.local_adt(t).is_some() || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_local_adt(tys, e))),
        _ => false,
    }
}

/// The fmt traits a builtin receiver's `fmt` may name, in the order
/// the probe tries them: Display, Debug.
const FMT_TRAITS: [FmtKind; 2] = [FmtKind::Display, FmtKind::Debug];

impl<'p> Ctx<'p> {
    /// `fmt::Result`.
    pub(super) fn fmt_result_ty(&mut self) -> Ty {
        generics::fmt_result_ty(&mut self.tys)
    }

    /// True when the trait of `kind` (Display or Debug) is in scope for a
    /// method call here: imported into this module by a `use` of its std
    /// path, or the trait of the impl this body is in (rustc puts an
    /// impl's own trait in scope inside it). Globs and `as _` imports do
    /// not count yet, which can only reject.
    pub(super) fn fmt_trait_in_scope(&mut self, kind: FmtKind) -> bool {
        let p = self.p;
        let (trait_def, name) = match kind {
            FmtKind::Display => (p.gx.lang.display, "Display"),
            _ => (p.gx.lang.debug, "Debug"),
        };
        self.enclosing_impl_trait() == Some(trait_def) || self.std_trait_imported("fmt", name)
    }

    /// True when this module imports the std trait `module::name` by a
    /// `use` of its std path at module level (`use std::fmt::Write;`,
    /// any rename, `as _`), or an enclosing block does (`Ast::use_traits`
    /// paths in `std_trait_scopes`). Module-level globs do not count
    /// yet, which can only reject.
    pub(super) fn std_trait_imported(&mut self, module: &str, name: &str) -> bool {
        let p = self.p;
        if self.std_trait_scopes.iter().flat_map(|layer| layer.iter()).any(|path| {
            path.len() == 3
                && matches!(p.interner.get(path[0]), "std" | "core" | "alloc")
                && p.interner.get(path[1]) == module
                && p.interner.get(path[2]) == name
        }) {
            return true;
        }
        // The module's imports: a `StdImport` read, so removing the `use`
        // checks this body again (Sol's read-gap review r06).
        p.std_import(&mut self.out.reads, self.module, module, name)
    }

    /// True when a glob of std module `module` (or core's: `std::ops::*`,
    /// `std::hash::*`) is imported into this body's module: it brings
    /// every trait of that module in scope. Recorded as a `StdImport` read.
    pub(super) fn std_glob(&mut self, module: &str) -> bool {
        let p = self.p;
        p.std_import(&mut self.out.reads, self.module, module, "*")
    }

    /// `enclosing_impl_trait` for the other std trait modules.
    pub(super) fn enclosing_impl_trait_pub(&self) -> Option<DefId> {
        self.enclosing_impl_trait()
    }

    /// The trait of the impl this body's fn is a method of, walking out
    /// of closures and nested fns and from an instance to its template.
    /// The nearest impl decides: an inherent impl nested in a trait
    /// method has no trait (rustc resets its current trait ref there).
    fn enclosing_impl_trait(&self) -> Option<DefId> {
        let p = self.p;
        let mut f = self.fid;
        if let Some(info) = p.gx.instances.get(&f)
            && let Some(t) = info.template_local
        {
            f = t;
        }
        let mut def = Some(p.def_id(f));
        for _ in 0..64 {
            let d = def?;
            // The body's own impl, covered by its def (`LUST_CHECK_READS`): an
            // impl's path is its header, so a header edit makes new defs.
            if let Some((_, rec)) = crate::driver::read_cover::muted(|| p.gx.index.by_def(d)) {
                return Some(rec.trait_def);
            }
            if matches!(p.defs.kind_of(d), Some(crate::ty::defs::DefKind::Impl)) {
                return None;
            }
            def = p.defs.parent_of(d);
        }
        None
    }

    /// Methods of the Formatter and the Debug builders, `fmt` called on
    /// a builtin value, and `to_string` of an Adt with a Display impl.
    /// None when the call is none of these, so other dispatch runs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn fmt_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        rt: Ty,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
    ) -> Option<Ty> {
        let n = self.p.interner.get(name);
        // `fmt::Arguments` has no inherent methods lust ports; its
        // `to_string` and trait `fmt` run through the generic arms
        // below, like a local Adt with a Display impl.
        if let Some(k) = fmt_kind(&self.tys, base)
            && !(k == FmtTy::Arguments && matches!(n, "to_string" | "fmt"))
        {
            return Some(self.fmt_type_method(e, recv, k, derefs, n, name_span, args));
        }
        // `<String as fmt::Write>`: write_str and write_char append and
        // return Ok, with the trait in scope.
        if self.tys.is_string_ty(base) && matches!(n, "write_str" | "write_char") && self.fmt_write_in_scope() {
            let (b, param) = if n == "write_str" { (Builtin::FmtWriteStr, REF_STR) } else { (Builtin::FmtWriteChar, CHAR) };
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::RefMut });
            self.check_args(&[param], args, name_span);
            return Some(self.fmt_result_ty());
        }
        // A local Adt gets here only when the user method probe found no
        // written `fmt` in scope: its derived Debug is the glue.
        if n == "fmt" && args.len() == 1 {
            return self.builtin_fmt_call(e, recv, base, derefs, name_span, args);
        }
        if n == "to_string"
            && args.is_empty()
            && (self.tys.local_adt(base).is_some()
                || matches!(self.tys.kind(base), TyKind::Dyn(..))
                || fmt_kind(&self.tys, base) == Some(FmtTy::Arguments))
        {
            // `impl<T: Display> ToString for T`, through the receiver's
            // Display impl (Self is bound as rustc's probe binds it).
            // A dyn receiver (`Box<dyn Error>`, F3) is Display through
            // its principal's supertrait and keeps the probe's derefs.
            // With no Display impl there is no `to_string`: other
            // dispatch runs and reports the missing method.
            let t = self.deep(rt);
            if !has_display(self.p, &self.tys, t) && !self.require_fmt(t, FmtKind::Display, name_span) {
                return None;
            }
            let derefs = if matches!(self.tys.kind(base), TyKind::Dyn(..)) {
                derefs
            } else {
                u8::from(matches!(self.tys.kind(t), TyKind::Ref(..)))
            };
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b: Builtin::ToString, derefs, autoref: Autoref::Ref });
            return Some(STRING);
        }
        None
    }

    /// `value.fmt(f)` on a builtin value or an Adt with a derived Debug
    /// (`self.0.fmt(f)` in an impl of Debug): the one fmt trait in scope
    /// that the type implements.
    fn builtin_fmt_call(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let candidates = self.fmt_traits_of(base);
        let kind = match candidates.as_slice() {
            [] => return None,
            [k] => *k,
            _ => {
                self.err(
                    "L0104",
                    name_span,
                    "multiple applicable items in scope: `fmt` of `Display` and of `Debug`",
                    "Call it as `fmt::Display::fmt(&value, f)` or `fmt::Debug::fmt(&value, f)`.",
                );
                for &a in args {
                    self.expr(a, None);
                }
                return Some(ERROR);
            }
        };
        self.check_packed_borrow(recv, name_span);
        Some(self.set_fmt_call(e, kind, derefs, Autoref::Ref, name_span, args))
    }

    /// The fmt traits in scope here (`fmt_trait_in_scope`) that `t`
    /// implements, Display first: the `fmt` candidates of a receiver `&t`.
    pub(super) fn fmt_traits_of(&mut self, t: Ty) -> Vec<FmtKind> {
        let p = self.p;
        FMT_TRAITS
            .iter()
            .copied()
            .filter(|&k| {
                self.fmt_trait_in_scope(k)
                    && match k {
                        FmtKind::Display => has_display(p, &self.tys, t),
                        _ => has_debug(p, &self.tys, t),
                    }
            })
            .collect()
    }

    /// Resolves `x.fmt(f)` as the builtin `fmt` of trait `kind`: the
    /// receiver `derefs` deep, then `autoref`. Returns `fmt::Result`.
    pub(super) fn set_fmt_call(&mut self, e: ExprId, kind: FmtKind, derefs: u8, autoref: Autoref, name_span: Span, args: &[ExprId]) -> Ty {
        let b = if kind == FmtKind::Display { Builtin::FmtCallDisplay } else { Builtin::FmtCallDebug };
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        let f = fmt_ty(&mut self.tys, FmtTy::Formatter);
        let fm = self.tys.mk_ref(true, f);
        self.check_args(&[fm], args, name_span);
        self.fmt_result_ty()
    }

    /// One method of a Formatter or Debug builder receiver.
    #[allow(clippy::too_many_arguments)]
    fn fmt_type_method(&mut self, e: ExprId, recv: ExprId, k: FmtTy, derefs: u8, n: &str, name_span: Span, args: &[ExprId]) -> Ty {
        use Builtin as B;
        let res = self.fmt_result_ty();
        let opt_usize = self.tys.mk_option(USIZE);
        let me = fmt_ty(&mut self.tys, k);
        let me_mut = self.tys.mk_ref(true, me);
        if n == "entries" && matches!(k, FmtTy::DebugList | FmtTy::DebugSet | FmtTy::DebugMap) {
            return self.fmt_entries(e, recv, k, derefs, name_span, args, me_mut);
        }
        // (builtin, autoref, plain params, `&dyn Debug` params, return)
        let found: Option<(B, Autoref, Vec<Ty>, usize, Ty)> = match (k, n) {
            (FmtTy::Formatter, "write_str") => Some((B::FmtWriteStr, Autoref::RefMut, vec![REF_STR], 0, res)),
            (FmtTy::Formatter, "write_char") if self.fmt_write_in_scope() => Some((B::FmtWriteChar, Autoref::RefMut, vec![CHAR], 0, res)),
            (FmtTy::Formatter, "pad") => Some((B::FmtPad, Autoref::RefMut, vec![REF_STR], 0, res)),
            (FmtTy::Formatter, "pad_integral") => Some((B::FmtPadIntegral, Autoref::RefMut, vec![BOOL, REF_STR, REF_STR], 0, res)),
            (FmtTy::Formatter, "width") => Some((B::FmtWidth, Autoref::Ref, vec![], 0, opt_usize)),
            (FmtTy::Formatter, "precision") => Some((B::FmtPrecision, Autoref::Ref, vec![], 0, opt_usize)),
            (FmtTy::Formatter, "fill") => Some((B::FmtFill, Autoref::Ref, vec![], 0, CHAR)),
            (FmtTy::Formatter, "alternate") => Some((B::FmtAlternate, Autoref::Ref, vec![], 0, BOOL)),
            (FmtTy::Formatter, "sign_plus") => Some((B::FmtSignPlus, Autoref::Ref, vec![], 0, BOOL)),
            (FmtTy::Formatter, "sign_minus") => Some((B::FmtSignMinus, Autoref::Ref, vec![], 0, BOOL)),
            (FmtTy::Formatter, "sign_aware_zero_pad") => Some((B::FmtSignAwareZeroPad, Autoref::Ref, vec![], 0, BOOL)),
            (FmtTy::Formatter, "debug_struct") => {
                let t = fmt_ty(&mut self.tys, FmtTy::DebugStruct);
                Some((B::FmtDebugStruct, Autoref::RefMut, vec![REF_STR], 0, t))
            }
            (FmtTy::Formatter, "debug_tuple") => {
                let t = fmt_ty(&mut self.tys, FmtTy::DebugTuple);
                Some((B::FmtDebugTuple, Autoref::RefMut, vec![REF_STR], 0, t))
            }
            (FmtTy::Formatter, "debug_list") => {
                let t = fmt_ty(&mut self.tys, FmtTy::DebugList);
                Some((B::FmtDebugList, Autoref::RefMut, vec![], 0, t))
            }
            (FmtTy::Formatter, "debug_set") => {
                let t = fmt_ty(&mut self.tys, FmtTy::DebugSet);
                Some((B::FmtDebugSet, Autoref::RefMut, vec![], 0, t))
            }
            (FmtTy::Formatter, "debug_map") => {
                let t = fmt_ty(&mut self.tys, FmtTy::DebugMap);
                Some((B::FmtDebugMap, Autoref::RefMut, vec![], 0, t))
            }
            (FmtTy::DebugStruct, "field") => Some((B::DsField, Autoref::RefMut, vec![REF_STR], 1, me_mut)),
            (FmtTy::DebugTuple, "field") => Some((B::DtField, Autoref::RefMut, vec![], 1, me_mut)),
            (FmtTy::DebugList | FmtTy::DebugSet, "entry") => Some((B::DlEntry, Autoref::RefMut, vec![], 1, me_mut)),
            (FmtTy::DebugMap, "entry") => Some((B::DmEntry, Autoref::RefMut, vec![], 2, me_mut)),
            (FmtTy::DebugMap, "key") => Some((B::DmKey, Autoref::RefMut, vec![], 1, me_mut)),
            (FmtTy::DebugMap, "value") => Some((B::DmValue, Autoref::RefMut, vec![], 1, me_mut)),
            (FmtTy::DebugStruct | FmtTy::DebugTuple | FmtTy::DebugList | FmtTy::DebugSet | FmtTy::DebugMap, "finish") => {
                Some((B::FmtFinish, Autoref::RefMut, vec![], 0, res))
            }
            (FmtTy::DebugStruct | FmtTy::DebugTuple | FmtTy::DebugList | FmtTy::DebugSet | FmtTy::DebugMap, "finish_non_exhaustive") => {
                Some((B::FmtFinishNonExhaustive, Autoref::RefMut, vec![], 0, res))
            }
            _ => None,
        };
        let Some((b, autoref, params, dyn_params, ret)) = found else {
            for &a in args {
                self.expr(a, None);
            }
            let tn = self.tn(me);
            if DECLARED_ONLY.contains(&n) || n == "write_fmt" {
                self.errs.push(Diag::new(
                    "L0640",
                    name_span,
                    format!("`{tn}::{n}` is not implemented in lust yet"),
                    "Rewrite this part with the supported subset.",
                ));
            } else {
                self.err("L0104", name_span, format!("no method `{n}` on type `{tn}`"), "Check the method name.");
            }
            return ERROR;
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, name_span);
        }
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        if args.len() != params.len() + dyn_params {
            self.err(
                "L0105",
                name_span,
                format!("this method takes {} argument(s) but {} were given", params.len() + dyn_params, args.len()),
                "Pass exactly the declared arguments.",
            );
            for &a in args {
                self.expr(a, None);
            }
            return ret;
        }
        self.check_args(&params, &args[..params.len()], name_span);
        for &a in &args[params.len()..] {
            self.dyn_debug_arg(a);
        }
        ret
    }

    /// `entries(iter)` on a DebugList, DebugSet, or DebugMap: any
    /// IntoIterator whose items are Debug (`(K, V)` pairs of Debug parts
    /// for a map), one `entry` each, as std loops (lower/iter.rs).
    #[allow(clippy::too_many_arguments)]
    fn fmt_entries(&mut self, e: ExprId, recv: ExprId, k: FmtTy, derefs: u8, name_span: Span, args: &[ExprId], me_mut: Ty) -> Ty {
        let [a] = args else {
            self.err("L0105", name_span, "`entries` takes 1 argument", "Pass an iterator.");
            for &a in args {
                self.expr(a, None);
            }
            return me_mut;
        };
        let at = self.expr(*a, None);
        let at = self.deep(at);
        let span = self.span(*a);
        let Some(it) = crate::ty::iter::as_iter_ty(&mut self.tys, at).or_else(|| self.by_next_arg(*a, at)) else {
            if self.kind(at) != TyKind::Error {
                let tn = self.tn(at);
                self.err("L0612", span, format!("`entries` takes an iterator, not `{tn}`"), "Pass an iterator, a Vec, or a slice.");
            }
            return me_mut;
        };
        if it == ERROR {
            return me_mut;
        }
        let item = crate::ty::iter::item_ty(&mut self.tys, it).unwrap_or(ERROR);
        let item = self.deep(item);
        let debug = FmtSpec { kind: FmtKind::Debug, ..FmtSpec::default() };
        let b = if k == FmtTy::DebugMap {
            let parts = match self.kind(item) {
                TyKind::Tuple(ts) if self.tys.tys_of(ts).len() == 2 => self.tys.tys_of(ts).to_vec(),
                _ => {
                    if self.kind(item) != TyKind::Error {
                        let tn = self.tn(item);
                        self.err("L0612", span, format!("`DebugMap::entries` takes `(K, V)` items, not `{tn}`"), "Iterate over pairs.");
                    }
                    return me_mut;
                }
            };
            for t in parts {
                self.check_fmt_arg(t, debug, span);
            }
            Builtin::DmEntries
        } else {
            self.check_fmt_arg(item, debug, span);
            Builtin::DlEntries
        };
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::RefMut });
        me_mut
    }

    /// One `&dyn Debug` argument of a builder method: a reference to a
    /// sized Debug value (Rust's unsizing coercion), formatted through
    /// its own Debug impl.
    fn dyn_debug_arg(&mut self, a: ExprId) {
        let t = self.expr(a, None);
        let t = self.deep(t);
        let span = self.span(a);
        let TyKind::Ref(_, _, inner) = self.kind(t) else {
            if self.kind(t) != TyKind::Error {
                let tn = self.tn(t);
                self.err("L0111", span, format!("expected `&dyn Debug`, found `{tn}`"), "Pass a reference, such as `&self.field`.");
            }
            return;
        };
        let inner = self.deep(inner);
        let unsized_newtype = matches!(self.kind(inner), TyKind::Adt(d, _) if self.tys.unsized_field(d).is_some());
        if unsized_newtype || matches!(self.kind(inner), TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..)) {
            let tn = self.tn(inner);
            self.err(
                "L0112",
                span,
                format!("the size for values of type `{tn}` cannot be known, so `&{tn}` is not `&dyn Debug`"),
                "Pass a reference to a sized value, such as `&self.name` for a `&str` field.",
            );
            return;
        }
        self.check_fmt_arg(inner, FmtSpec { kind: FmtKind::Debug, ..FmtSpec::default() }, span);
    }

    /// True when `fmt::Write` is in scope by a `use` of its std path.
    fn fmt_write_in_scope(&mut self) -> bool {
        self.std_trait_imported("fmt", "Write")
    }

    /// `t: Display` or `t: Debug` for a format argument whose type the
    /// structural rules do not answer: a local Adt (a user impl, maybe
    /// with where clauses) proves through the obligation queue, so the
    /// impl set and its bounds decide, and an unsatisfied goal reports
    /// L0612. Returns false when the type has no Adt to prove.
    pub(super) fn require_fmt(&mut self, t: Ty, kind: FmtKind, span: Span) -> bool {
        let trait_def = if kind == FmtKind::Display { self.p.gx.lang.display } else { self.p.gx.lang.debug };
        if !self.mentions_user_impl_adt(t, trait_def) {
            return false;
        }
        let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
        self.obl.push_trait_at(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }, span, 0);
        true
    }

    /// True when `t` holds a local Adt that has a written impl of
    /// `trait_def` (a goal the structural rules cannot answer).
    fn mentions_user_impl_adt(&self, t: Ty, trait_def: DefId) -> bool {
        use crate::traits::index::{SelfHead, Synthetic};
        match self.tys.kind(t) {
            TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) => self.mentions_user_impl_adt(e, trait_def),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.mentions_user_impl_adt(e, trait_def)),
            TyKind::Adt(def, a) => {
                let index = &self.p.gx.index;
                index.impls_of_trait(trait_def).iter().any(|&id| {
                    let rec = index.peek(id);
                    rec.synthetic == Synthetic::None && rec.head == SelfHead::Adt(def)
                }) || self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.mentions_user_impl_adt(e, trait_def)))
            }
            _ => false,
        }
    }

    /// `dst.write_fmt(format_args!(..))`, the `write!` shape: on a
    /// Formatter (inherent) or a String (through `fmt::Write`, which
    /// must be in scope). The format arguments check as for `format!`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn write_fmt_call(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let [arg] = args else { return None };
        let Expr::Macro { kind: MacroKind::FormatArgs, .. } = self.p.ast.expr(*arg) else { return None };
        let on_formatter = fmt_kind(&self.tys, base) == Some(FmtTy::Formatter);
        let on_string = self.tys.is_string_ty(base) && self.fmt_write_in_scope();
        if !on_formatter && !on_string {
            // Any other receiver: `io::Write::write_fmt` (W-SHIM, the
            // method-call arm allows the `Arguments` value) or a user
            // method of the name; normal method resolution picks it.
            return None;
        }
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b: Builtin::FmtWriteFmt, derefs, autoref: Autoref::RefMut });
        let fa = fmt_ty(&mut self.tys, FmtTy::Arguments);
        self.check_args(&[fa], args, name_span);
        Some(self.fmt_result_ty())
    }
}

/// Checks a user `impl Display` or `impl Debug` against the trait: one
/// `fmt(&self, f: &mut Formatter<'_>) -> fmt::Result` method. Lang trait
/// impls have no method templates, so this is their signature check.
pub fn check_fmt_impl(p: &mut Program, imp: &ast::ImplDef, tr: TraitRef, self_pat: Ty, method_ids: &[LocalDefId], errs: &mut Vec<Diag>) {
    if tr.def != p.gx.lang.display && tr.def != p.gx.lang.debug {
        return;
    }
    // The glue calls written impls of structs and enums only
    // (`gx.fmt_methods`): one for a `Box`, a reference, or a trait
    // object would never run, the glue formats the pointee instead.
    if !matches!(p.tys.kind(self_pat), TyKind::Adt(..)) || p.tys.builtin_of(self_pat).is_some() {
        let tn = crate::check::collect::ty_name(p, &p.tys, self_pat);
        let trait_name = if tr.def == p.gx.lang.display { "Display" } else { "Debug" };
        errs.push(Diag::new(
            "L0641",
            imp.span,
            format!("an `impl {trait_name}` for `{tn}` is not supported yet"),
            "Implement the trait for a struct or enum, such as a local wrapper of the value.",
        ));
        return;
    }
    let fmt_sym = p.interner.intern("fmt");
    let Some(&m) = method_ids.iter().find(|&&id| p.fn_info(id).name == fmt_sym) else {
        errs.push(Diag::new("L0110", imp.span, "the impl is missing the trait method `fmt`", "Add the method to the impl."));
        return;
    };
    let f = fmt_ty(&mut p.tys, FmtTy::Formatter);
    let want_f = p.tys.mk_ref(true, f);
    let want_self = p.tys.mk_ref(false, self_pat);
    let want_ret = generics::fmt_result_ty(&mut p.tys);
    let info = p.fn_info(m);
    let ok = info.self_kind == Some(ast::SelfKind::Ref) && info.params.len() == 2 && info.params[0] == want_self && info.params[1] == want_f && info.ret == want_ret;
    if !ok {
        errs.push(Diag::new(
            "L0110",
            info.def(&p.ast).name_span,
            "method `fmt` has an incompatible type for the trait",
            "Write `fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result`.",
        ));
    }
}

/// A range kind a `{:?}` argument of type `t` names through plain
/// references, with its bound type (unit for `..`) and the reference
/// count: core's range Debug, which lowering writes as format parts at
/// the site (lower/range_fmt.rs). A range inside another type formats
/// through Debug glue (cgen/fmt.rs `dbg_cty`).
pub fn range_fmt_kind(tys: &impl TyIntern, t: Ty) -> Option<(crate::ty::iter::IterKind, Ty, u32)> {
    let mut t = t;
    let mut refs = 0;
    while let TyKind::Ref(_, _, inner) = tys.kind(t) {
        t = inner;
        refs += 1;
    }
    let (k, a) = crate::ty::iter::iter_parts(tys, t)?;
    if !k.is_range() {
        return None;
    }
    Some((k, a.first().copied().unwrap_or(crate::ty::UNIT), refs))
}
