// A trait method named through its trait as a value or a call:
// `Into::into`, `From::from`, `Clone::clone`, `ToString::to_string`,
// `Default::default`, and user traits in the same shape
// (`.map(Into::into)`, `let f = Clone::clone;`, `Into::into(x)`).
//
// Neither Self nor the trait's other inputs are written, so the
// path is typed like a deferred assoc call (`assoc_call_deferred`):
// the trait obligation stays queued, the value's type is an
// `FnDef` over the trait method itself (its signature is the trait
// method's, so inference through `.map(..)` and friends works),
// and body end selects what the value really calls: a written
// impl's fn, a trait default, a std conversion builtin
// (`Builtin::ConvInto` for `From`/`Into`, `Clone`, `ToString`,
// the `Default` glue), a numeric widening cast, or - in a template
// the param env proves - the trait method's signature stub, as a
// deferred method call does. Anything else is a reject.
use super::*;

/// What a deferred trait fn path selects at body end.
pub(super) enum TraitFnRes {
    /// A real fn (an impl's, a trait default's, or a stub) with its
    /// full generic arguments.
    Fn(LocalDefId, Vec<GenericArg>),
    /// One std conversion builtin (`ConvInto`, `Clone`, `ToString`).
    Builtin(Builtin),
    /// A numeric widening `From`/`Into`: a cast.
    Cast,
    /// The `Default` glue.
    Default,
    /// A comparison trait method at a type whose comparison is builtin
    /// (`PartialEq::eq(&a, &b)` at `u8`): the method form's `PrimCmp`.
    PrimCmp(PrimCmpKind),
    /// `Ord::max`, `min`, or `clamp` at a type compared by structure
    /// (`Ord::max(a, b)` at a tuple): the method form's `OrdPick`.
    OrdPick(OrdPickKind),
    /// Nothing lust can call; already reported, or to report.
    Failed,
}

impl<'p> Ctx<'p> {
    /// The trait a two-or-more segment path heads with, when it is a
    /// trait name (bare, or a canonical std trait path) and its last
    /// segment names one of its methods. Returns the trait def, the
    /// method def, and the trait segment. None when the head is a
    /// type, alias, or type parameter of the same name, as in
    /// `self_from_expected_call`.
    pub(super) fn trait_path_head(&mut self, segs: &[ast::PathSeg]) -> Option<(DefId, DefId, usize)> {
        let p = self.p;
        let tdef = self.trait_path_def(segs)?;
        let last = segs.len() - 1;
        let rec = p.gx.index.trait_record(tdef)?;
        // A std path through another trait of the same bare name must
        // not answer for this one: the record's own name is the seg's.
        if rec.name != segs[last - 1].name && segs.len() > 2 {
            return None;
        }
        let method = rec.method_by_name(segs[last].name)?;
        Some((tdef, method, last - 1))
    }

    /// The trait def the type segments of `segs` (all but the item) name,
    /// as `trait_path_head` reads them.
    fn trait_path_def(&mut self, segs: &[ast::PathSeg]) -> Option<DefId> {
        let p = self.p;
        if segs.len() < 2 {
            return None;
        }
        let last = segs.len() - 1;
        let tdef = if segs.len() == 2 {
            // The flat maps answer with no read of their own (see
            // `self_from_expected_call`).
            self.binding(crate::driver::graph::Namespace::Type, segs[0].name);
            if p.type_names.contains_key(&segs[0].name)
                || p.aliases.contains_key(&segs[0].name)
                || self.body_scope.param_tys.iter().any(|(n, _)| *n == segs[0].name)
            {
                return None;
            }
            p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_bare_name(&p.interner, segs[0].name)?
        } else {
            let path: Vec<&str> = segs[..last].iter().map(|s| self.name(s.name)).collect();
            if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Trait) {
                return None;
            }
            // A full canonical path names std's trait whether or not the
            // trait is in the prelude (`std::borrow::Borrow`), and never a
            // user trait of the same name (a root `trait From`).
            p.gx.lang.by_name(self.name(segs[last - 1].name))?
        };
        Some(tdef)
    }

    /// `Hash::hash(x, &mut state)` (`std::hash::Hash::hash` too): core's
    /// `fn hash<H: Hasher>(&self, state: &mut H)` by path, which lust
    /// has as the method form's `HashInto` builtin, not as a trait
    /// signature. `x` is a coercion site for `&Self` (Self inferred from
    /// it); the first argument is the receiver, by `&*x`. None for other
    /// paths.
    fn hash_path_call(&mut self, e: ExprId, segs: &[ast::PathSeg], args: &[ExprId], span: Span) -> Option<Ty> {
        let lang = self.p.gx.lang;
        if self.name(segs.last()?.name) != "hash" || segs.last()?.has_args() || self.trait_path_def(segs)? != lang.hash {
            return None;
        }
        if segs[segs.len() - 2].has_args() {
            return None;
        }
        if args.len() != 2 {
            self.err("L0105", span, "this function takes 2 arguments but a different number was given", "Pass `&value` and `&mut state`.");
            for &a in args {
                self.expr(a, None);
            }
            return Some(ERROR);
        }
        let (s, h) = (self.new_var(false), self.new_var(false));
        let (rs, rh) = (self.tys.mk_ref(false, s), self.tys.mk_ref(true, h));
        self.check_args(&[rs, rh], args, span);
        let (s, h) = (self.deep(s), self.deep(h));
        if !self.implements(lang.hasher, h) {
            let tn = self.tn(h);
            self.err("L0612", self.span(args[1]), format!("`hash` takes `&mut H` with `H: Hasher`, not `&mut {tn}`"), "Pass `&mut` a hasher.");
            return Some(ERROR);
        }
        self.glue_hashable(s, span);
        self.set_res(e, Res::BuiltinMethod { b: Builtin::HashInto, derefs: 1, autoref: Autoref::Ref });
        Some(UNIT)
    }

    /// True for a `ToString::to_string` path (bare or canonical).
    /// `ToString` is not a lang trait and its shipped-source record
    /// exists only when the program splices that source in, so the
    /// path has a marker form of its own (`to_string_ref`).
    fn is_to_string_path(&self, segs: &[ast::PathSeg]) -> bool {
        let names: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
        matches!(names.as_slice(), ["ToString", "to_string"] | ["std" | "alloc", "string", "ToString", "to_string"])
    }

    /// The marker trait ref of a `ToString::to_string` path with no
    /// trait record in this program: Self a fresh variable, and no
    /// obligation (body end asks for `Display` instead, which is
    /// what the blanket impl needs).
    fn to_string_ref(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Option<(TraitRef, DefId)> {
        if segs.iter().any(|s| s.has_args()) {
            self.err("L0107", span, "`to_string` takes no generic arguments", "Remove the `::<...>`.");
            return None;
        }
        let _ = e;
        let (tdef, method) = generics::to_string_defs();
        let v = self.new_var(false);
        let args = self.tys.intern_args(&[GenericArg::Ty(v)]);
        Some((TraitRef { def: tdef, args, bindings: EMPTY_BINDINGS }, method))
    }

    /// `Trait::method` as a value: its `FnDef` type over the trait
    /// method, with Self and the trait's other inputs as fresh
    /// variables the queued obligation and the uses around it fix.
    pub(super) fn trait_path_fn_value(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Option<Ty> {
        if self.trait_path_head(segs).is_none() && self.is_to_string_path(segs) {
            let (tr, method) = self.to_string_ref(e, segs, span)?;
            self.deferred_trait_fn_values.push((e, tr, segs[segs.len() - 1].name, Vec::new(), span));
            return Some(self.tys.intern(TyKind::FnDef(method, tr.args)));
        }
        let (tdef, method_def, tseg) = self.trait_path_head(segs)?;
        let (tr, full) = self.trait_path_ref(e, segs, tdef, method_def, tseg, span)?;
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_values.push((e, tr, segs[segs.len() - 1].name, full[n_trait..].to_vec(), span));
        let args = self.tys.intern_args(&full);
        Some(self.tys.intern(TyKind::FnDef(method_def, args)))
    }

    /// `Trait::method(args)` as a call, after the assoc-call paths
    /// had no answer: typed by the trait method's signature like the
    /// value form, with the call itself deferred to body end.
    pub(super) fn trait_path_call(&mut self, e: ExprId, callee: ExprId, segs: &[ast::PathSeg], args: &[ExprId], span: Span) -> Option<Ty> {
        if let Some(t) = self.hash_path_call(e, segs, args, span) {
            return Some(t);
        }
        if self.trait_path_head(segs).is_none() && self.is_to_string_path(segs) {
            let (tr, method) = self.to_string_ref(e, segs, span)?;
            let full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            let (mut params, ret) = self.trait_method_sig(method, &full)?;
            self.normalize_params(&mut params, span);
            self.deferred_trait_fn_calls.push((e, tr, segs[segs.len() - 1].name, Vec::new(), span));
            self.check_args(&params, args, span);
            return Some(self.normalize_use(ret, span));
        }
        let (tdef, method_def, tseg) = self.trait_path_head(segs)?;
        let (tr, full) = self.trait_path_ref(e, segs, tdef, method_def, tseg, span)?;
        let _ = callee;
        let (mut params, ret) = self.trait_method_sig(method_def, &full)?;
        self.normalize_params(&mut params, span);
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_calls.push((e, tr, segs[segs.len() - 1].name, full[n_trait..].to_vec(), span));
        self.check_args(&params, args, span);
        Some(self.normalize_use(ret, span))
    }

    /// `<Self as Trait>::method(args)` with the whole trait ref known
    /// (an instance's `T::clone(t)` at the template's `T: Clone` bound,
    /// `T` now `i32`), when the assoc-call paths had no answer: typed by
    /// the trait method's signature, with the call deferred to body end
    /// like `trait_path_call`'s (a std builtin or the impl's fn).
    pub(super) fn trait_ref_call(&mut self, e: ExprId, tr: TraitRef, name: Sym, args: &[ExprId], span: Span) -> Option<Ty> {
        let (method_def, full) = self.trait_ref_full(tr, name)?;
        let (mut params, ret) = self.trait_method_sig(method_def, &full)?;
        self.trait_ref_obligations(e, tr, method_def, &full, span);
        self.normalize_params(&mut params, span);
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_calls.push((e, tr, name, full[n_trait..].to_vec(), span));
        self.check_args(&params, args, span);
        Some(self.normalize_use(ret, span))
    }

    /// `<Self as Trait>::method` as a value with the whole trait ref
    /// known (`T::area` or `<T as Sh>::mk` on a type parameter, its
    /// instance at a concrete `T`, `<i32 as Clone>::clone`): the trait
    /// method's `FnDef`, pointed at the impl fn, the param-env stub, or
    /// a builtin at body end, like `trait_path_fn_value`'s.
    pub(super) fn trait_ref_fn_value(&mut self, e: ExprId, tr: TraitRef, name: Sym, span: Span) -> Option<Ty> {
        let (method_def, full) = self.trait_ref_full(tr, name)?;
        self.trait_method_sig(method_def, &full)?;
        self.trait_ref_obligations(e, tr, method_def, &full, span);
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_values.push((e, tr, name, full[n_trait..].to_vec(), span));
        let args = self.tys.intern_args(&full);
        Some(self.tys.intern(TyKind::FnDef(method_def, args)))
    }

    /// `cmp::min(a, b)` or `cmp::max(a, b)` at a type that is not a
    /// builtin scalar: std's body is `v1.min(v2)`, so the call takes the
    /// pick of `<T as Ord>::min` at body end (a written `min`, the trait
    /// default, or the structural compare). The caller already checked
    /// the arguments at `(T, T) -> T`, the trait method's signature.
    pub(super) fn cmp_free_fn_as_ord(&mut self, e: ExprId, t: Ty, name: Sym, span: Span) {
        let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: self.p.gx.lang.ord, args, bindings: EMPTY_BINDINGS };
        let Some((method_def, full)) = self.trait_ref_full(tr, name) else {
            self.errs.push(crate::diag::unsupported(span, "`cmp::max`/`cmp::min` on this type"));
            return;
        };
        self.trait_ref_obligations(e, tr, method_def, &full, span);
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_calls.push((e, tr, name, full[n_trait..].to_vec(), span));
    }

    /// The method def of `name` in `tr`'s trait and its full generic
    /// arguments: `tr`'s, then fresh ones for the method's own params.
    fn trait_ref_full(&mut self, tr: TraitRef, name: Sym) -> Option<(DefId, Vec<GenericArg>)> {
        let p = self.p;
        let method_def = p.gx.index.trait_record(tr.def)?.method_by_name(name)?;
        let n_trait = self.tys.args(tr.args).len();
        let mut full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        let own_kinds: Vec<ParamKind> = match p.gx.trait_methods.get(&method_def) {
            Some(t) => t.generics.params.iter().skip(n_trait).map(|x| x.kind).collect(),
            None => Vec::new(),
        };
        for kind in own_kinds {
            full.push(match kind {
                ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
            });
        }
        Some((method_def, full))
    }

    /// Queues what a trait-ref call or value needs: the method's own
    /// predicates, the trait obligation, and the pick.
    fn trait_ref_obligations(&mut self, e: ExprId, tr: TraitRef, method_def: DefId, full: &[GenericArg], span: Span) {
        let preds: Vec<Predicate> = self.p.gx.trait_methods.get(&method_def).map(|t| t.generics.predicates.clone()).unwrap_or_default();
        self.push_predicates(&preds, full, span);
        self.obl.push_trait_at(tr, span, 0);
        self.record_pick(e, tr.def, 0, ReceiverForm::Value);
    }

    /// The trait ref and full generic arguments (trait, then the
    /// method's own) of a trait path: Self a fresh variable, written
    /// trait arguments honored, the trait obligation queued and the
    /// pick recorded, as `assoc_call_deferred` records them.
    fn trait_path_ref(
        &mut self,
        e: ExprId,
        segs: &[ast::PathSeg],
        tdef: DefId,
        method_def: DefId,
        tseg: usize,
        span: Span,
    ) -> Option<(TraitRef, Vec<GenericArg>)> {
        let p = self.p;
        let rec = p.gx.index.trait_record(tdef)?.clone();
        let base = self.new_var(false);
        let tr = if matches!(segs[tseg].args, ast::GenericArgs::Angle(_)) {
            let tref = ast::TraitRefExpr { path: segs[..=tseg].to_vec() };
            match self.written_trait_ref(base, &tref, span) {
                Ok(tr) if tr.def == tdef => tr,
                Ok(_) => return None,
                Err(d) => {
                    self.errs.push(d);
                    return None;
                }
            }
        } else {
            self.assoc_trait_ref(e, base, None, tdef, &rec)
        };
        let n_trait = rec.generics.params.len();
        let mut full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        // The method's own arguments: the turbofish on the method
        // segment, else fresh variables.
        let own_written = segs[segs.len() - 1].type_args();
        let (own_kinds, preds): (Vec<ParamKind>, Vec<Predicate>) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => (t.generics.params.iter().skip(n_trait).map(|x| x.kind).collect(), t.generics.predicates.clone()),
            None => (Vec::new(), Vec::new()),
        };
        if own_written.len() > own_kinds.len() {
            self.err("L0107", span, "this trait method takes no generic arguments here", "Remove the `::<...>`.");
            return None;
        }
        for (i, kind) in own_kinds.iter().enumerate() {
            full.push(match own_written.get(i) {
                Some(w) => GenericArg::Ty(self.resolve_written(*w)),
                None => match kind {
                    ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                    ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                    ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
                },
            });
        }
        self.push_predicates(&preds, &full, span);
        self.obl.push_trait_at(tr, span, 0);
        self.record_pick(e, tdef, 0, ReceiverForm::Value);
        Some((tr, full))
    }

    /// True when `def` is a trait method lust has a signature for
    /// (a written trait's template, or a lang trait's sig table).
    pub(super) fn is_trait_method_def(&self, def: DefId) -> bool {
        self.p.gx.trait_methods.contains_key(&def)
            || self.p.gx.lang_method_sigs.contains_key(&def)
            || def == generics::to_string_defs().1
    }

    /// A trait method's signature under `full` (trait arguments,
    /// then its own), as `assoc_call_deferred` instantiates it.
    pub(super) fn trait_method_sig(&mut self, method_def: DefId, full: &[GenericArg]) -> Option<(Vec<Ty>, Ty)> {
        if method_def == generics::to_string_defs().1 {
            let self_ty = full.first().and_then(|g| g.as_ty())?;
            return Some((vec![self.tys.mk_ref(false, self_ty)], STRING));
        }
        let p = self.p;
        let (sig_params, sig_ret) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => (t.params.clone(), t.ret),
            None => {
                let s = p.gx.lang_method_sigs.get(&method_def)?;
                (s.params.clone(), s.ret)
            }
        };
        let params: Vec<Ty> = sig_params.iter().map(|&t| subst(&mut self.tys, t, full)).collect();
        let ret = subst(&mut self.tys, sig_ret, full);
        Some((params, ret))
    }

    /// True when this body's param env bounds `t` by `Display`
    /// (the `ToString` blanket's one need, for a marker value in a
    /// template check).
    fn display_in_env(&mut self, t: Ty) -> bool {
        let display = self.p.gx.lang.display;
        self.solve_env().iter().any(|pred| match pred {
            Predicate::Trait(b) => {
                b.value.def == display && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()).is_some_and(|s| self.deep(s) == t)
            }
            _ => false,
        })
    }

    /// What a deferred trait fn path calls, at body end (see the
    /// file head). `tr`'s arguments are read as bound by now.
    pub(super) fn trait_fn_finish(&mut self, tr: TraitRef, name: Sym, own: &[GenericArg], span: Span) -> TraitFnRes {
        let p = self.p;
        let lang = &p.gx.lang;
        // Reading the trait ref as bound by now.
        let targs: Vec<Ty> = self.tys.args(tr.args).to_vec().into_iter().filter_map(|g| g.as_ty()).map(|t| self.deep(t)).collect();
        let known = |cx: &Self, t: Ty| !cx.tys.flags(t).contains_infer() && !cx.has_error_kind(t);
        let is_from = tr.def == lang.from && self.name(name) == "from";
        let is_into = tr.def == lang.into && self.name(name) == "into";
        if (is_from || is_into) && targs.len() >= 2 {
            let (src, dst) = if is_from { (targs[1], targs[0]) } else { (targs[0], targs[1]) };
            if known(self, src) && known(self, dst) {
                if convert::std_from(p, &self.tys, dst, src).is_some() {
                    return TraitFnRes::Builtin(Builtin::ConvInto);
                }
                let (sk, dk) = (self.kind(src), self.kind(dst));
                if matches!(sk, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
                    && matches!(dk, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char)
                    && Self::numeric_from_ok(sk, dk)
                {
                    return TraitFnRes::Cast;
                }
            }
        }
        // A written impl's fn, or the trait's default body.
        if let Some((f, mut prefix)) = self.trait_fn_of(tr, name, true, span) {
            prefix.extend(own.iter().copied());
            return TraitFnRes::Fn(f, prefix);
        }
        // `Into` through a written `From` impl (core's blanket): the
        // from fn is the value.
        if is_into && targs.len() >= 2 {
            let fargs = self.tys.intern_args(&[GenericArg::Ty(targs[1]), GenericArg::Ty(targs[0])]);
            let ftr = TraitRef { def: lang.from, args: fargs, bindings: EMPTY_BINDINGS };
            let from_name = p.interner.intern("from");
            if let Some((f, prefix)) = self.trait_fn_of(ftr, from_name, true, span) {
                return TraitFnRes::Fn(f, prefix);
            }
        }
        // The param env proves it (a template check): the stub.
        if let Selection::ParamEvidence(i) = self.select_obligation(tr)
            && i != usize::MAX
            && let Some(rec) = p.gx.index.trait_record(tr.def)
            && let Some(m) = rec.method_by_name(name)
            && let Some(&stub) = p.gx.trait_method_stubs.get(&m)
        {
            let mut full: Vec<GenericArg> =
                self.tys.args(tr.args).to_vec().into_iter().map(|g| if let GenericArg::Ty(t) = g { GenericArg::Ty(self.deep(t)) } else { g }).collect();
            full.extend(own.iter().copied());
            return TraitFnRes::Fn(stub, full);
        }
        let self_ty = targs.first().copied().unwrap_or(ERROR);
        // A synthetic conversion impl (`Borrow::borrow` on a builtin
        // Self) has no fn: the value is the conversion builtin.
        if targs.len() >= 2
            && known(self, self_ty)
            && known(self, targs[1])
            && let Some(b) = self.conv_call_builtin(tr.def, self_ty, targs[1])
        {
            return TraitFnRes::Builtin(b);
        }
        if tr.def == lang.clone && self.name(name) == "clone" && has_clone(p, &self.tys, self_ty) {
            return TraitFnRes::Builtin(Builtin::Clone);
        }
        if tr.def == lang.clone && self.name(name) == "clone_from" && has_clone(p, &self.tys, self_ty) {
            return TraitFnRes::Builtin(Builtin::CloneFrom);
        }
        if tr.def == lang.default && self.name(name) == "default" && has_default(p, &self.tys, self_ty) {
            self.record_glue_reads(lang.default, self_ty);
            return TraitFnRes::Default;
        }
        if self.name(name) == "to_string"
            && (tr.def == generics::to_string_defs().0
                || p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_bare_name(&p.interner, p.interner.intern("ToString")) == Some(tr.def))
            && (has_display(p, &self.tys, self_ty) || self.display_in_env(self_ty))
        {
            // `str` is unsized: its `to_string` copies the bytes the `&str` names.
            if self.kind(self_ty) == TyKind::Str {
                return TraitFnRes::Builtin(Builtin::StrToString);
            }
            return TraitFnRes::Builtin(Builtin::ToString);
        }
        if let Some(kind) = self.prim_cmp_path(tr.def, name, &targs) {
            return TraitFnRes::PrimCmp(kind);
        }
        if let Some(r) = self.ord_pick_path(tr.def, name, self_ty) {
            return r;
        }
        // `Debug::fmt(s, f)` and `<str as Display>::fmt(s, f)` at a
        // Self with no written impl (a builtin type, or a derived
        // Debug): the method form's `FmtCall*` (`s.fmt(f)`), which
        // formats as `{:?}` does with the caller's Formatter.
        if self.name(name) == "fmt" && (tr.def == lang.debug || tr.def == lang.display) && known(self, self_ty) {
            if tr.def == lang.display && has_display(p, &self.tys, self_ty) {
                return TraitFnRes::Builtin(Builtin::FmtCallDisplay);
            }
            if tr.def == lang.debug && has_debug(p, &self.tys, self_ty) {
                return TraitFnRes::Builtin(Builtin::FmtCallDebug);
            }
        }
        TraitFnRes::Failed
    }

    /// `Ord::max`, `min`, or `clamp` named through the trait at a Self
    /// type whose order builds in: the `cmp::max` builtin at an integer,
    /// `char`, or `bool`, else core's default bodies by structure, as
    /// the method form (`ord_pick_method`) runs them.
    fn ord_pick_path(&mut self, tdef: DefId, name: Sym, self_ty: Ty) -> Option<TraitFnRes> {
        let p = self.p;
        if tdef != p.gx.lang.ord || self.tys.flags(self_ty).contains_infer() || self.tys.flags(self_ty).contains_param() {
            return None;
        }
        let kind = match self.name(name) {
            "max" => OrdPickKind::Max,
            "min" => OrdPickKind::Min,
            "clamp" => OrdPickKind::Clamp,
            _ => return None,
        };
        if matches!(self.kind(self_ty), TyKind::Int(_) | TyKind::Char | TyKind::Bool) {
            return match kind {
                OrdPickKind::Max => Some(TraitFnRes::Builtin(Builtin::CmpMax)),
                OrdPickKind::Min => Some(TraitFnRes::Builtin(Builtin::CmpMin)),
                OrdPickKind::Clamp => None,
            };
        }
        (has_ord(p, &self.tys, self_ty) && has_total_ord(p, &self.tys, self_ty)).then(|| {
            self.record_glue_reads(p.gx.lang.partial_ord, self_ty);
            TraitFnRes::OrdPick(kind)
        })
    }

    /// A `PartialEq`, `PartialOrd`, or `Ord` comparison method named
    /// through its trait, at a Self type whose comparison core builds
    /// in (scalars, `str`, and structures compared part by part, the
    /// types `prim_cmp_method` takes in method form), with `Rhs` the
    /// Self type: the call is the comparison of its two arguments.
    fn prim_cmp_path(&mut self, tdef: DefId, name: Sym, targs: &[Ty]) -> Option<PrimCmpKind> {
        let p = self.p;
        let lang = &p.gx.lang;
        let self_ty = *targs.first()?;
        if targs.get(1).is_some_and(|&r| r != self_ty)
            || self.tys.flags(self_ty).contains_infer()
            || self.tys.flags(self_ty).contains_param()
            || self.has_error_kind(self_ty)
        {
            return None;
        }
        let float = matches!(self.kind(self_ty), TyKind::Float(_));
        let scalar = float || matches!(self.kind(self_ty), TyKind::Int(_) | TyKind::Bool | TyKind::Char);
        let n = self.name(name);
        let (kind, want, ok) = match n {
            "eq" | "ne" => {
                let op = if n == "eq" { BinOp::Eq } else { BinOp::Ne };
                (PrimCmpKind::Op(op), lang.partial_eq, scalar || has_eq(p, &self.tys, self_ty))
            }
            "lt" | "le" | "gt" | "ge" | "partial_cmp" => {
                let kind = match n {
                    "lt" => PrimCmpKind::Op(BinOp::Lt),
                    "le" => PrimCmpKind::Op(BinOp::Le),
                    "gt" => PrimCmpKind::Op(BinOp::Gt),
                    "ge" => PrimCmpKind::Op(BinOp::Ge),
                    _ => PrimCmpKind::Partial(p.tys.local_adt_of(generics::ordering_def())?),
                };
                (kind, lang.partial_ord, scalar || has_ord(p, &self.tys, self_ty))
            }
            "cmp" => (PrimCmpKind::Total(p.tys.local_adt_of(generics::ordering_def())?), lang.ord, !float && (scalar || has_total_ord(p, &self.tys, self_ty))),
            _ => return None,
        };
        (ok && tdef == want).then_some(kind)
    }

    /// Body end for trait fn values: point each at what it calls
    /// (a real fn item, or a builtin-marker `FnDef` over the trait
    /// method that lowering expands), as `finish_deferred_methods`
    /// points deferred calls.
    pub(super) fn finish_trait_fn_values(&mut self) {
        for (e, tr, name, own, span) in std::mem::take(&mut self.deferred_trait_fn_values) {
            let ei = self.ei(e);
            match self.trait_fn_finish(tr, name, &own, span) {
                TraitFnRes::Fn(f, full) => {
                    if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                        self.generic_sites.push((ei, f, full.clone()));
                    }
                    self.set_res(e, Res::Fn(f));
                    // The value's type was the trait method's
                    // `FnDef`; other recordings embed it (a `Map`
                    // adapter's closure type is its `F` argument),
                    // so rewrite it to the selected fn's item type
                    // through the whole checked body.
                    if let TyKind::FnDef(method, _) = self.kind(self.out.expr_ty[ei]) {
                        let args = self.tys.intern_args(&full);
                        let to = self.tys.intern(TyKind::FnDef(self.p.def_id(f), args));
                        let mut from: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
                        from.extend(own.iter().copied());
                        if method != self.p.def_id(f) {
                            self.rewrite_fn_def(method, &from, to);
                        }
                        self.out.expr_ty[ei] = to;
                    }
                }
                TraitFnRes::Builtin(b) => {
                    self.finish_marker_value(e, Res::Builtin(b), tr, name, span);
                }
                TraitFnRes::Cast => {
                    self.finish_marker_value(e, Res::Builtin(Builtin::ConvInto), tr, name, span);
                }
                TraitFnRes::Default => {
                    self.finish_marker_value(e, Res::Builtin(Builtin::DefaultGlue), tr, name, span);
                }
                // A builtin comparison: the value stays the trait
                // method's `FnDef` with no resolution (zero-sized, as a
                // marker); a call through it selects again by the trait
                // (`value_call`), here `PrimCmp` or `OrdPick`.
                TraitFnRes::PrimCmp(_) | TraitFnRes::OrdPick(_) => self.finish_marker_value(e, Res::None, tr, name, span),
                TraitFnRes::Failed => self.trait_fn_failed(tr, name, span, true),
            }
        }
    }

    /// Rejects a callable a builtin cannot call through its C adapter: a
    /// boxed `dyn` thread function, and a trait fn value left as a marker (`i32::cmp`,
    /// `Clone::clone` at a builtin impl) where a builtin calls it
    /// through a C adapter (`sort_by`, `retain`, `thread::spawn`): the
    /// marker has no fn to call there. The iterator builtins expand
    /// the conversion, clone, default, and `to_string` markers
    /// (lower/iter.rs `call_fn`); every other use calls through the
    /// value, which selects again by the trait (`value_call`).
    pub(super) fn reject_marker_callables(&mut self) {
        if self.is_template_check() {
            return;
        }
        let p = self.p;
        let base = self.out.expr_base;
        for i in 0..self.out.expr_res.len() {
            let e = ExprId(base + i as u32);
            let (b, args) = match (&self.out.expr_res[i], p.ast.expr(e)) {
                // (A builtin method by path, `Vec::len(&v)`, is a call.)
                (Res::BuiltinMethod { b, .. }, ast::Expr::MethodCall { args, .. } | ast::Expr::Call { args, .. }) => (*b, args),
                (Res::Builtin(b), ast::Expr::Call { args, .. }) => (*b, args),
                _ => continue,
            };
            // A thread's main as a `dyn` value other than `Box<dyn
            // FnOnce() -> T>` (a `&dyn Fn`, a `Box<dyn Fn>`): the thread
            // start calls closures, fn items, fn pointers, and boxed
            // `dyn FnOnce` only (cgen/sync.rs `callee_of_ty`).
            let spawn = matches!(
                b,
                Builtin::Sync(
                    crate::check::sync::SyncOp::ThreadSpawn
                        | crate::check::sync::SyncOp::BuilderSpawn
                        | crate::check::sync::SyncOp::BuilderSpawnScoped
                        | crate::check::sync::SyncOp::ScopeSpawn
                )
            );
            for (k, &a) in args.iter().enumerate() {
                // A spawn's function is its last argument (`spawn_scoped`
                // takes the `&Scope` first).
                let spawn = spawn && k + 1 == args.len();
                let t0 = self.deep(self.out.expr_ty[self.ei(a)]);
                // A `Box<dyn FnOnce() -> T>` is fine: the start calls its
                // vtable's `call_once` (cgen/sync.rs `Callee::DynOnce`).
                let boxed_once = self.tys.boxed_elem(t0).and_then(|d| crate::check::object::principal_of(&self.tys, d)).is_some_and(|pr| pr.def == p.gx.lang.fn_once);
                // A `&F` of a `Fn` closure is fine too (`spawn_scoped(scope,
                // &work)`): the start calls the body with the reference as
                // its env (cgen/sync.rs `callee_of_ty`).
                let ref_fn_closure = match self.kind(t0) {
                    TyKind::Ref(_, Mut::Shared, inner) => match { let d = self.deep(inner); self.kind(d) } {
                        TyKind::Closure(def, _) => {
                            self.closures.iter().any(|c| c.def == def && c.kind == crate::check::closure::ClosureKind::Fn)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if spawn && !boxed_once && !ref_fn_closure && (matches!(self.kind(t0), TyKind::Dyn(..) | TyKind::Ref(..)) || self.tys.boxed_elem(t0).is_some()) {
                    let span = self.span(a);
                    self.errs.push(generics::dyn_not_yet(span, "a `dyn FnOnce` value or a reference to a callable as a thread's function"));
                    continue;
                }
                // The builtins whose start calls the value (`catch_unwind`,
                // `get_or_init`, `wait_while`, `fetch_update`, `new_cyclic`,
                // the thread starts) take its last argument through
                // cgen/sync.rs `callee_of`: other forms (a `Box<dyn Fn>`, a
                // reference to a fn pointer, `&&F`) have no call there.
                // `catch_unwind(AssertUnwindSafe(f))` calls `f` (lower/unwind.rs).
                let tc = match self.tys.local_adt(t0) {
                    Some(adt) if b == Builtin::Sync(crate::check::sync::SyncOp::CatchUnwind) && crate::check::unwind::is_assert_unwind_safe(p, adt) => {
                        self.tys.adt_first_ty_arg(t0).map_or(t0, |f| self.deep(f))
                    }
                    _ => t0,
                };
                if k + 1 == args.len() && calls_value(b) && !self.callee_value_ok(tc) {
                    let tn = self.tn(tc);
                    let span = self.span(a);
                    self.err(
                        "L0641",
                        span,
                        format!("a `{tn}` as this builtin's function is not supported yet"),
                        "Wrap the call in a closure, for example `catch_unwind(|| f())`.",
                    );
                    continue;
                }
                let mut t = t0;
                loop {
                    t = match self.kind(t) {
                        TyKind::Ref(_, _, inner) => inner,
                        _ if let Some(inner) = self.tys.boxed_elem(t) => inner,
                        _ => break,
                    };
                }
                let TyKind::FnDef(def, _) = self.kind(t) else { continue };
                let tdef = if def == generics::to_string_defs().1 {
                    generics::to_string_defs().0
                } else {
                    match p.gx.index.trait_of_method(def) {
                        Some(d) => d,
                        None => continue,
                    }
                };
                let lang = &p.gx.lang;
                let expanded = crate::lower::iter::expands(b)
                    && ([lang.from, lang.into, lang.clone, lang.default, generics::to_string_defs().0].contains(&tdef)
                        || p.gx.index.trait_record(tdef).is_some_and(|r| p.interner.get(r.name) == "ToString"));
                if !expanded {
                    let tn = self.trait_name(tdef);
                    let name = p.gx.index.trait_record(tdef).and_then(|r| r.methods.iter().find(|(d, _)| *d == def).map(|&(_, n)| n));
                    let item = name.map(|n| self.name(n).to_string()).unwrap_or_default();
                    let span = self.span(a);
                    self.err(
                        "L0641",
                        span,
                        format!("`{tn}::{item}` with a builtin impl as this builtin's callable is not supported yet"),
                        "Wrap it in a closure instead.",
                    );
                }
            }
        }
    }

    /// Whether cgen/sync.rs `callee_of` calls a value of type `t`: a
    /// closure, fn item, fn pointer or `Box<dyn FnOnce>`; a reference to a
    /// closure or fn item; `&dyn Fn` or `&mut dyn Fn`/`FnMut`.
    fn callee_value_ok(&mut self, t: Ty) -> bool {
        let lang = &self.p.gx.lang;
        if let TyKind::Ref(_, m, i) = self.kind(t) {
            let i = self.deep(i);
            return match self.kind(i) {
                TyKind::Closure(..) | TyKind::FnDef(..) => true,
                TyKind::Dyn(..) => crate::check::object::principal_of(&self.tys, i)
                    .is_some_and(|pr| pr.def == lang.fn_ || (m == Mut::Mut && pr.def == lang.fn_mut)),
                _ => false,
            };
        }
        match self.kind(t) {
            TyKind::Closure(..) | TyKind::FnDef(..) | TyKind::FnPtr(_) => true,
            _ => self.tys.boxed_elem(t).and_then(|d| crate::check::object::principal_of(&self.tys, d)).is_some_and(|pr| pr.def == lang.fn_once),
        }
    }

    /// A builtin-marker trait fn value: the resolution names the
    /// builtin and the type stays the trait method's `FnDef` (its
    /// arguments as bound by now), which calls through it expand.
    /// A reification to a fn pointer has no fn to point at: reject.
    fn finish_marker_value(&mut self, e: ExprId, res: Res, tr: TraitRef, name: Sym, span: Span) {
        let ei = self.ei(e);
        // The reification may sit on a later use of the value (`let g:
        // fn(&i32) -> i32 = f;` after `let f = Clone::clone;`): any
        // reified expression of this trait method's `FnDef` type.
        let method = match self.kind(self.out.expr_ty[ei]) {
            TyKind::FnDef(m, _) => Some(m),
            _ => None,
        };
        let reified = matches!(self.out.coerce[ei], Coerce::ReifyFn(_))
            || method.is_some_and(|m| {
                (0..self.out.coerce.len()).any(|i| {
                    matches!(self.out.coerce[i], Coerce::ReifyFn(_)) && matches!(self.kind(self.out.expr_ty[i]), TyKind::FnDef(d, _) if d == m)
                })
            });
        if reified {
            let tn = self.trait_name(tr.def);
            self.err(
                "L0641",
                span,
                format!("`{tn}::{}` converted to a function pointer is not supported yet", self.name(name)),
                "Wrap it in a closure instead.",
            );
            return;
        }
        self.set_res(e, res);
    }

    /// Body end for calls through a trait fn value (and direct
    /// `Trait::name(..)` calls deferred the same way).
    pub(super) fn finish_trait_fn_calls(&mut self) {
        for (e, tr, name, own, span) in std::mem::take(&mut self.deferred_trait_fn_calls) {
            let ei = self.ei(e);
            match self.trait_fn_finish(tr, name, &own, span) {
                TraitFnRes::Fn(f, full) => {
                    if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                        self.generic_sites.push((ei, f, full));
                    }
                    self.set_res(e, Res::Fn(f));
                }
                TraitFnRes::Builtin(b) => self.set_res(e, Res::Builtin(b)),
                TraitFnRes::Cast => self.set_res(e, Res::FromCast),
                TraitFnRes::Default => self.set_res(e, Res::DefaultVal),
                // The first argument is `&Self`: one deref to the value.
                TraitFnRes::PrimCmp(kind) if !self.coerced_call_arg(e, span) => self.set_res(e, Res::PrimCmp { kind, derefs: 1 }),
                TraitFnRes::OrdPick(kind) if !self.coerced_call_arg(e, span) => {
                    self.set_res(e, Res::OrdPick { kind, f: None, via: CmpVia::Partial(BinOp::Lt) })
                }
                TraitFnRes::PrimCmp(_) | TraitFnRes::OrdPick(_) => {}
                TraitFnRes::Failed => self.trait_fn_failed(tr, name, span, false),
            }
        }
    }

    /// True, with the error reported, when a trait path call that
    /// lowers as the method form (`PrimCmp`, `OrdPick`) has an argument
    /// with a coercion (`<i32 as Ord>::cmp(&&x, &y)`, `str::eq(&s, ..)`
    /// at a `String`): that lowering reads each argument as its written
    /// type, so the call is a reject, never a misread.
    fn coerced_call_arg(&mut self, e: ExprId, span: Span) -> bool {
        let ast::Expr::Call { args, .. } = self.p.ast.expr(e) else { return false };
        if args.iter().all(|&a| self.out.coerce[self.ei(a)] == Coerce::None) {
            return false;
        }
        self.err(
            "L0641",
            span,
            "a builtin comparison through its trait path with a coerced argument is not supported yet",
            "Pass the arguments at the exact types, or call the method form (`a.cmp(b)`).",
        );
        true
    }

    /// Replaces every `FnDef(method, from)` in the checked body's
    /// recorded types with `to` (the selected fn's item type):
    /// adapter types and generic sites embed the value's type, not
    /// just the value expression itself.
    fn rewrite_fn_def(&mut self, method: DefId, from: &[GenericArg], to: Ty) {
        let from: Vec<GenericArg> = from
            .iter()
            .map(|g| match g {
                GenericArg::Ty(t) => GenericArg::Ty(self.deep(*t)),
                other => *other,
            })
            .collect();
        for i in 0..self.out.expr_ty.len() {
            self.out.expr_ty[i] = self.rewrite_ty(self.out.expr_ty[i], method, &from, to);
        }
        for i in 0..self.out.pat_ty.len() {
            self.out.pat_ty[i] = self.rewrite_ty(self.out.pat_ty[i], method, &from, to);
        }
        for i in 0..self.out.locals.len() {
            self.out.locals[i].ty = self.rewrite_ty(self.out.locals[i].ty, method, &from, to);
        }
        for i in 0..self.out.generic_args.len() {
            let args: Vec<GenericArg> = std::mem::take(&mut self.out.generic_args[i]);
            self.out.generic_args[i] = args
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.rewrite_ty(t, method, &from, to)),
                    other => other,
                })
                .collect();
        }
        for i in 0..self.generic_sites.len() {
            let args: Vec<GenericArg> = std::mem::take(&mut self.generic_sites[i].2);
            self.generic_sites[i].2 = args
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.rewrite_ty(t, method, &from, to)),
                    other => other,
                })
                .collect();
        }
    }

    /// `rewrite_fn_def` on one type.
    fn rewrite_ty(&mut self, t: Ty, method: DefId, from: &[GenericArg], to: Ty) -> Ty {
        // An adapter's closure argument is often a variable bound
        // to the FnDef type, not the type itself.
        let t = self.deep(t);
        let args_of = |cx: &mut Self, a: ArgsId| -> Vec<GenericArg> {
            cx.tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(cx.rewrite_ty(e, method, from, to)),
                    other => other,
                })
                .collect()
        };
        match self.tys.kind(t) {
            TyKind::FnDef(def, a) => {
                let cur: Vec<GenericArg> = self
                    .tys
                    .args(a)
                    .to_vec()
                    .into_iter()
                    .map(|g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep(e)),
                        other => other,
                    })
                    .collect();
                if def == method {
                }
                if def == method && cur == from {
                    to
                } else {
                    let na = args_of(self, a);
                    let na = self.tys.intern_args(&na);
                    self.tys.intern(TyKind::FnDef(def, na))
                }
            }
            TyKind::Adt(def, a) => {
                let na = args_of(self, a);
                self.tys.mk_adt(def, &na)
            }
            TyKind::Closure(def, a) => {
                let na = args_of(self, a);
                let na = self.tys.intern_args(&na);
                self.tys.intern(TyKind::Closure(def, na))
            }
            TyKind::Ref(r, m, e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.rewrite_ty(e, method, from, to)).collect();
                let ts = self.tys.intern_tys(&elems);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::FnPtr(sig) => {
                let s = self.tys.sig(sig);
                let (count, value) = (s.count, s.value);
                let inputs: Vec<Ty> =
                    self.tys.tys_of(value.inputs).to_vec().into_iter().map(|e| self.rewrite_ty(e, method, from, to)).collect();
                let inputs = self.tys.intern_tys(&inputs);
                let output = self.rewrite_ty(value.output, method, from, to);
                let ns = self.tys.intern_sig(crate::ty::Binder { count, value: crate::ty::FnSig { inputs, output, ..value } });
                self.tys.intern(TyKind::FnPtr(ns))
            }
            _ => t,
        }
    }

    /// A trait fn path nothing selected for. The queued obligation
    /// already reported most of these; report the rest once.
    fn trait_fn_failed(&mut self, tr: TraitRef, name: Sym, span: Span, _value: bool) {
        if !self.errs.is_empty() {
            return;
        }
        let tn = self.trait_name(tr.def);
        self.err(
            "L0641",
            span,
            format!("`{tn}::{}` as a function is not supported yet", self.name(name)),
            "Call it as a method (`value.name(..)`) with the trait in scope, or wrap that call in a closure.",
        );
    }
}

/// The builtins whose last argument is a function they call through
/// cgen/sync.rs `callee_of` (`Ctx::callee_value_ok`).
fn calls_value(b: Builtin) -> bool {
    use crate::check::sync::SyncOp as S;
    matches!(
        b,
        Builtin::RcNewCyclic
            | Builtin::Sync(
                S::CatchUnwind
                    | S::ThreadSpawn
                    | S::ThreadScope
                    | S::ScopeSpawn
                    | S::BuilderSpawn
                    | S::BuilderSpawnScoped
                    | S::OnceGetOrInit
                    | S::CondvarWaitWhile
                    | S::CondvarWaitTimeoutWhile
                    | S::AtomicFetchUpdate
                    | S::ArcNewCyclic
            )
    )
}
