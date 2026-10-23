// `core::any` (W-CHECK-G3): the `Any` trait, `TypeId`, and downcasts.
//
// `Any` is a lang trait with one synthetic blanket impl for every type
// (`impl<T: 'static + ?Sized> Any for T`, `generics::add_synthetic_impls`);
// selection ignores the `'static` part, as rustc's method probe does, and
// the checks here and in the borrow checker prove it. `TypeId` is a
// synthetic struct of two `u64` words (`generics::type_id_def`): a 128-bit
// hash of the type's structure with regions erased (`type_id_words`), the
// same in every body and every daemon build of one program.
//
// A `dyn Any` vtable stores the value's type id after its header
// (`object::VT_ANY_ID`); a user trait with `Any` as a supertrait reaches
// it through its super slot. This file types the calls; lowering builds
// them (lower/any.rs):
//
// - `x.type_id()` (with `Any` in scope, or on a dyn receiver whose
//   principal has `Any` as a supertrait): Self follows rustc's probe
//   order (a reference step's pointee first, then the step itself under
//   an autoref), so `Box<dyn Any>` in scope answers for the box.
// - `is`, `downcast_ref`, `downcast_mut` on `dyn Any`, `dyn Any + Send`,
//   and `dyn Any + Send + Sync` (std's inherent impls), through
//   references, `Box`, and `Rc`.
// - `Box<dyn Any ..>::downcast` and `Rc<dyn Any>::downcast` by value.
// - `TypeId::of::<T>()`.
//
// The tested type is `Checked::generic_args[e][0]` (the Self type for a
// static `type_id`). It must be known at the call (a turbofish or the
// expected type), sized, and `'static`. lust does not track the regions
// of non-dyn references, so a reference in it passes only where its
// region can be `'static` without a check (written in a turbofish
// without a named lifetime, and not behind `downcast_mut`).
use super::*;
use std::hash::Hasher;

/// Which `core::any` operation a `Res::Any` is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnyOp {
    /// `x.type_id()` with a static Self (`generic_args[e][0]`).
    TypeId,
    /// `x.type_id()` on a dyn receiver: the id in its vtable.
    DynTypeId,
    Is,
    DowncastRef,
    DowncastMut,
    /// `Box<dyn Any>::downcast` or `Rc<dyn Any>::downcast` (by the
    /// receiver type).
    Downcast,
    /// `TypeId::of::<T>()`, on the callee path.
    TypeIdOf,
    /// `std::any::type_name::<T>()`, on the callee path: the named
    /// type is `Checked::generic_args[e][0]`, and lowering bakes
    /// rustc's exact string for it (`type_name_of` below).
    TypeName,
}

/// The two words of the type id of `t` (a concrete type, in any store):
/// a 128-bit hash of its structure, with defs in stable form and regions
/// erased. Lowering builds `TypeId` values from it and codegen writes it
/// into `dyn Any` vtables, so both must see equal types.
pub fn type_id_words(p: &Program, tys: &impl TyIntern, t: Ty) -> (u64, u64) {
    let mut bytes: Vec<u8> = Vec::new();
    encode_ty(p, tys, t, &mut bytes);
    // std's `DefaultHasher::new()` is SipHash with fixed keys: the same
    // in every run of one lust binary.
    let word = |salt: u8| {
        let mut h = std::hash::DefaultHasher::new();
        h.write(&[salt]);
        h.write(&bytes);
        h.finish()
    };
    (word(1), word(2))
}

/// The canonical byte form of a type for `type_id_words`.
fn encode_ty(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<u8>) {
    let def = |out: &mut Vec<u8>, d: crate::def::DefId| {
        out.extend(crate::driver::graph::def_crate_hash(p, d).to_le_bytes());
        out.extend(d.hash.0.to_le_bytes());
    };
    let args = |out: &mut Vec<u8>, a: ArgsId| {
        for g in tys.args(a) {
            match *g {
                GenericArg::Ty(e) => {
                    out.push(b'T');
                    encode_ty(p, tys, e, out);
                }
                GenericArg::Const(c) => {
                    out.push(b'C');
                    out.extend(format!("{:?}", tys.const_kind(c)).bytes());
                }
                // Lifetimes are not part of a type id.
                GenericArg::Lifetime(_) => {}
            }
        }
        out.push(b'.');
    };
    match tys.kind(t) {
        TyKind::Unit => out.push(1),
        TyKind::Bool => out.push(2),
        TyKind::Char => out.push(3),
        TyKind::Never => out.push(4),
        TyKind::Int(i) => {
            out.push(5);
            out.extend(i.name().bytes());
        }
        TyKind::Float(f) => {
            out.push(6);
            out.extend(f.name().bytes());
        }
        TyKind::Str => out.push(7),
        TyKind::Ref(_, m, e) => {
            out.push(if m.is_mut() { 9 } else { 8 });
            encode_ty(p, tys, e, out);
        }
        TyKind::RawPtr(m, e) => {
            out.push(if m.is_mut() { 11 } else { 10 });
            encode_ty(p, tys, e, out);
        }
        TyKind::Slice(e) => {
            out.push(12);
            encode_ty(p, tys, e, out);
        }
        TyKind::Array(e, n) => {
            out.push(13);
            encode_ty(p, tys, e, out);
            out.extend(format!("{:?}", tys.const_kind(n)).bytes());
        }
        TyKind::Tuple(ts) => {
            out.push(14);
            for &e in tys.tys_of(ts) {
                encode_ty(p, tys, e, out);
            }
            out.push(b'.');
        }
        TyKind::Adt(d, a) => {
            out.push(15);
            def(out, d);
            args(out, a);
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            out.push(16);
            out.extend([s.is_unsafe as u8, s.extern_c as u8]);
            for &e in tys.tys_of(s.inputs) {
                encode_ty(p, tys, e, out);
            }
            out.push(b'>');
            encode_ty(p, tys, s.output, out);
        }
        TyKind::FnDef(d, a) => {
            out.push(17);
            def(out, d);
            args(out, a);
        }
        TyKind::Closure(d, a) => {
            out.push(18);
            def(out, d);
            args(out, a);
        }
        TyKind::Dyn(b, _) => {
            out.push(19);
            let b = tys.dyn_bounds(b);
            if let Some(pr) = b.principal {
                def(out, pr.value.def);
                args(out, pr.value.args);
                for &(assoc, g) in tys.bindings(pr.value.bindings) {
                    def(out, assoc);
                    if let GenericArg::Ty(e) = g {
                        encode_ty(p, tys, e, out);
                    }
                }
            }
            out.extend([b.auto.send as u8, b.auto.sync as u8, b.auto.unpin as u8, b.auto.unwind_safe as u8, b.auto.ref_unwind_safe as u8]);
        }
        // Never in a checked concrete type (`any_type_ok` rejects them);
        // a template's placeholder answer is never generated.
        TyKind::Error | TyKind::Opaque(..) | TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) => out.push(0),
    }
}

/// True when the dyn type `t` can answer `type_id` through its vtable:
/// its principal is `Any` or has `Any` as a supertrait.
pub fn dyn_reaches_any(p: &Program, tys: &mut impl TyIntern, t: Ty) -> bool {
    let Some(pr) = object::principal_of(tys, t) else { return false };
    let any = p.gx.lang.any;
    if pr.def == any {
        return true;
    }
    let args = tys.intern_args(&[GenericArg::Ty(DYN_SELF)]);
    object::upcast_path(p, tys, pr, TraitRef { def: any, args, bindings: EMPTY_BINDINGS }).is_some()
}

/// True for `dyn Any`, `dyn Any + Send`, and `dyn Any + Send + Sync`:
/// the dyn types std gives `is` and the downcast methods.
fn is_downcast_dyn(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    let TyKind::Dyn(b, _) = tys.kind(t) else { return false };
    let b = tys.dyn_bounds(b);
    b.principal.is_some_and(|pr| pr.value.def == p.gx.lang.any) && !b.auto.unpin && !b.auto.unwind_safe && !b.auto.ref_unwind_safe && (b.auto.send || !b.auto.sync)
}

impl<'p> Ctx<'p> {
    /// The `core::any` methods (see the file comment). None when the call
    /// is not one of them, or when a user method of the name could apply
    /// (then the ordinary probes answer).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn any_method(
        &mut self,
        e: ExprId,
        rt: Ty,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        explicit: &[Option<GenericArg>],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let p = self.p;
        let n = self.name(name);
        if !matches!(n, "type_id" | "is" | "downcast_ref" | "downcast_mut" | "downcast") {
            return None;
        }
        if p.gx.traits_by_method.get(&name).is_some_and(|ts| ts.iter().any(|t| p.gx.index.trait_record(*t).is_some_and(|r| r.local))) {
            return None;
        }
        if n == "type_id" {
            if !turbofish.is_empty() || p.methods.keys().any(|(_, m)| *m == name) {
                return None;
            }
            return self.type_id_method(e, rt, name_span, args);
        }
        // The steps of the receiver through references, `Box`, and `Rc`.
        let mut steps: Vec<(Ty, u8)> = Vec::new();
        let mut cur = self.resolve(rt);
        for derefs in 0..32u8 {
            steps.push((cur, derefs));
            cur = match self.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => match self.tys.smart_elem(cur) {
                    Some(inner) => self.resolve(inner),
                    None => break,
                },
            };
        }
        if n == "downcast" {
            // By value, at the receiver itself (a `Box` behind a
            // reference would move out of the borrow).
            let (t0, _) = steps[0];
            let elem = self.tys.smart_elem(t0).map(|t| self.resolve(t))?;
            let boxed = self.tys.boxed_elem(t0).is_some();
            // std has `Rc<dyn Any>::downcast` and, for `Arc`, only
            // `Arc<dyn Any + Send + Sync>::downcast`.
            let arc = crate::ty::sync::sync_kind(&self.tys, t0) == Some(crate::ty::sync::SyncTy::Arc);
            let autos = if arc { AutoTraits { send: true, sync: true, ..AutoTraits::default() } } else { AutoTraits::default() };
            let ok = if boxed {
                is_downcast_dyn(p, &self.tys, elem)
            } else {
                object::principal_of(&self.tys, elem).is_some_and(|pr| pr.def == p.gx.lang.any) && object::dyn_auto(p, &self.tys, elem) == autos
            };
            if !ok {
                return None;
            }
            let want = expected.and_then(|x| {
                let x = self.resolve(x);
                let (okt, _) = self.tys.result_args(x)?;
                let okt = self.resolve(okt);
                self.tys.smart_elem(okt)
            });
            let Some(t) = self.any_target(e, explicit, turbofish, want, name_span, true) else { return Some(self.any_fail(args)) };
            self.check_args(&[], args, name_span);
            self.set_res(e, Res::Any { op: AnyOp::Downcast, derefs: 0, autoref: Autoref::None });
            // `Arc::downcast` bounds the target by `Any + Send + Sync`.
            if arc {
                for tr in [p.gx.lang.send, p.gx.lang.sync] {
                    let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
                    let trait_ref = TraitRef { def: tr, args, bindings: EMPTY_BINDINGS };
                    self.obl.push(obligations::Obligation::Trait { trait_ref, span: name_span, depth: 0 });
                }
            }
            let owned = if boxed {
                self.tys.mk_boxed(t)
            } else if arc {
                crate::ty::sync::sync_ty(&mut self.tys, crate::ty::sync::SyncTy::Arc, &[t])
            } else {
                self.tys.mk_rc(t)
            };
            return Some(self.tys.mk_result(owned, t0));
        }
        let (_, derefs) = steps.iter().copied().find(|&(t, _)| is_downcast_dyn(p, &self.tys, t))?;
        let (op, mutable) = match n {
            "is" => (AnyOp::Is, false),
            "downcast_ref" => (AnyOp::DowncastRef, false),
            _ => (AnyOp::DowncastMut, true),
        };
        let want = match op {
            AnyOp::Is => None,
            _ => expected.and_then(|x| {
                let x = self.resolve(x);
                let inner = self.tys.option_elem(x)?;
                match self.kind(inner) {
                    TyKind::Ref(_, _, t) => Some(t),
                    _ => None,
                }
            }),
        };
        let Some(t) = self.any_target(e, explicit, turbofish, want, name_span, !mutable) else { return Some(self.any_fail(args)) };
        self.check_args(&[], args, name_span);
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        self.set_res(e, Res::Any { op, derefs, autoref });
        Some(match op {
            AnyOp::Is => BOOL,
            _ => {
                let r = self.tys.mk_ref(mutable, t);
                self.tys.mk_option(r)
            }
        })
    }

    /// Checks the arguments of a failed call (an error is reported) for
    /// their own errors; the call's type is the error type.
    fn any_fail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }

    /// `x.type_id()`, by rustc's probe order: at each autoderef step,
    /// a reference step's pointee is Self first (the `&self` receiver is
    /// the step itself), then the step under an autoref. A dyn Self whose
    /// principal reaches `Any` answers through its vtable without `Any`
    /// in scope (an object candidate); any other Self needs `Any` in
    /// scope (the blanket impl).
    fn type_id_method(&mut self, e: ExprId, rt: Ty, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let p = self.p;
        let in_scope = method::trait_in_scope_pub(self, p.gx.lang.any);
        let mut cur = self.resolve(rt);
        let mut hit: Option<(Ty, u8, bool)> = None;
        // An instance takes the template's step: a param's bound counts
        // only at that param, which its concrete type no longer shows
        // (`Box<T>` with `T: Any` and no `use` is `T`'s id, not the Box's).
        if let Some(pick) = self.replay_pick(e).filter(|pk| pk.trait_def == p.gx.lang.any) {
            for _ in 0..pick.derefs {
                cur = match self.tys.kind(cur) {
                    TyKind::Ref(_, _, inner) => self.resolve(inner),
                    _ => self.resolve(self.tys.smart_elem(cur)?),
                };
            }
            let dynamic = matches!(self.kind(cur), TyKind::Dyn(..)) && dyn_reaches_any(p, &mut self.tys, cur);
            hit = Some((cur, pick.derefs, dynamic));
        }
        for derefs in 0..32u8 {
            if hit.is_some() {
                break;
            }
            let mut cands: Vec<(Ty, u8)> = Vec::new();
            if let TyKind::Ref(_, Mut::Shared, inner) = self.tys.kind(cur) {
                cands.push((self.resolve(inner), derefs + 1));
            }
            cands.push((cur, derefs));
            for (self_ty, d) in cands {
                if matches!(self.kind(self_ty), TyKind::Dyn(..)) && dyn_reaches_any(p, &mut self.tys, self_ty) {
                    hit = Some((self_ty, d, true));
                    break;
                }
                // A bound on a param Self brings `Any` in for that param only.
                if in_scope || method::param_bound_names(self, p.gx.lang.any, self_ty) {
                    hit = Some((self_ty, d, false));
                    break;
                }
            }
            if hit.is_some() {
                break;
            }
            cur = match self.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => match self.tys.smart_elem(cur) {
                    Some(inner) => self.resolve(inner),
                    None => break,
                },
            };
        }
        let (self_ty, derefs, dynamic) = hit?;
        if !dynamic {
            self.record_pick(e, p.gx.lang.any, derefs, ReceiverForm::Ref);
        }
        self.check_args(&[], args, name_span);
        let id_ty = generics::type_id_ty(&mut self.tys);
        if dynamic {
            self.set_res(e, Res::Any { op: AnyOp::DynTypeId, derefs, autoref: Autoref::Ref });
            return Some(id_ty);
        }
        let self_ty = self.deep(self_ty);
        if !self.any_type_ok(self_ty, None, false, true, name_span) {
            return Some(ERROR);
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(self_ty)];
        self.set_res(e, Res::Any { op: AnyOp::TypeId, derefs, autoref: Autoref::Ref });
        Some(id_ty)
    }

    /// True when a call's callee path is `TypeId::of` (`std::any::TypeId::of`
    /// after the resolver expands an import).
    pub(super) fn is_type_id_of(&self, segs: &[ast::PathSeg]) -> bool {
        let names: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
        matches!(names.as_slice(), ["std" | "core", "any", "TypeId", "of"])
    }

    /// `TypeId::of::<T>()` (`std::any::TypeId::of`): the callee path's
    /// resolution, with T recorded for lowering.
    pub(super) fn type_id_of_path(&mut self, e: ExprId, seg: &ast::PathSeg, span: Span) -> Option<Res> {
        let written = seg.type_args();
        if written.len() != 1 {
            self.err("L0110", span, "`TypeId::of` takes one type argument", "Write `TypeId::of::<Type>()`.");
            return None;
        }
        let t = self.resolve_written(written[0]);
        let t = self.deep(t);
        if !self.any_type_ok(t, Some(written[0]), true, true, span) {
            return None;
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(t)];
        Some(Res::Any { op: AnyOp::TypeIdOf, derefs: 0, autoref: Autoref::None })
    }

    /// True when a call's callee path is `std::any::type_name` (or
    /// `core::any::type_name`, or an import the resolver expanded to
    /// one of them).
    pub(super) fn is_type_name_path(&self, segs: &[ast::PathSeg]) -> bool {
        let names: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
        matches!(names.as_slice(), ["std" | "core", "any", "type_name"])
    }

    /// `std::any::type_name::<T>()`: the callee path's resolution,
    /// with T recorded for lowering. Whether lust can print rustc's
    /// exact string for T is decided at body end
    /// (`deferred_type_names`), when T is fully known.
    pub(super) fn type_name_path(&mut self, e: ExprId, seg: &ast::PathSeg, span: Span) -> Option<Res> {
        let written = seg.type_args();
        if written.len() != 1 {
            self.err("L0110", span, "`type_name` takes one type argument", "Write `type_name::<Type>()`.");
            return None;
        }
        let t = self.resolve_written(written[0]);
        let t = self.deep(t);
        // The baked string names every Adt in T by its full path:
        // record the reads a layout query records, so a rename or a
        // module move rechecks this body.
        self.p.record_layout_reads(&mut self.out.reads, &self.tys, t);
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(t)];
        self.deferred_type_names.push((t, span));
        Some(Res::Any { op: AnyOp::TypeName, derefs: 0, autoref: Autoref::None })
    }

    /// The type a downcast tests: the turbofish, else the type the
    /// expected result fixes (`want`). Records it for lowering. None
    /// (after an error) when it is missing or not a valid `T: Any`.
    fn any_target(
        &mut self,
        e: ExprId,
        explicit: &[Option<GenericArg>],
        turbofish: &[ast::GenericArg],
        want: Option<Ty>,
        span: Span,
        refs_ok: bool,
    ) -> Option<Ty> {
        if explicit.len() > 1 {
            self.err("L0110", span, "this method takes one type argument", "Write `downcast_ref::<Type>()`.");
            return None;
        }
        let written = match turbofish.first() {
            Some(ast::GenericArg::Type(w)) => Some(*w),
            _ => None,
        };
        let t = match explicit.first().copied().flatten() {
            Some(GenericArg::Ty(t)) => t,
            Some(_) => {
                self.err("L0110", span, "this method takes a type argument", "Write `downcast_ref::<Type>()`.");
                return None;
            }
            None => match want {
                Some(t) => t,
                None => {
                    self.err(
                        "L0610",
                        span,
                        "type annotations needed: the type to downcast to must be known here",
                        "Name it with a turbofish, as in `downcast_ref::<Type>()`.",
                    );
                    return None;
                }
            },
        };
        let t = self.deep(t);
        // A turbofish type's elided references may be `'static`; an
        // inferred one's regions come from elsewhere.
        let refs_ok = refs_ok && written.is_some();
        if !self.any_type_ok(t, written, refs_ok, false, span) {
            return None;
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(t)];
        Some(t)
    }

    /// Checks one `T: Any` type at a `core::any` call, reporting why it
    /// fails: unknown parts (L0610), unsized where that is not allowed
    /// (L0110, rustc E0277), or not
    /// provably `'static` (L0612 for a type parameter, L0705 otherwise).
    /// An instance skips the `'static` part: its template proved it.
    pub(super) fn any_type_ok(&mut self, t: Ty, written: Option<ast::TyId>, refs_ok: bool, unsized_ok: bool, span: Span) -> bool {
        let p = self.p;
        if self.tys.flags(t).contains_infer() {
            self.err(
                "L0610",
                span,
                format!("type annotations needed: `{}` must be known here", self.tn(t)),
                "Write the full type, for example with a turbofish.",
            );
            return false;
        }
        if matches!(self.kind(t), TyKind::Error) {
            return false;
        }
        if self.contains_eta_closure(t) {
            self.err(
                "L0702",
                span,
                "the type id of a std fn used as a value is not supported yet",
                "Pass a fn of your own instead, such as `fn new_vec() -> Vec<u8> { Vec::new() }`.",
            );
            return false;
        }
        if contains_opaque(&self.tys, t) {
            self.errs.push(generics::dyn_not_yet(span, "the type id of an `impl Trait` type"));
            return false;
        }
        // `TypeId::of` and `type_id` take `T: ?Sized`; a downcast's T is sized.
        if !unsized_ok && !self.sized_ok(t) {
            let tn = self.tn(t);
            self.err("L0110", span, format!("the size for values of type `{tn}` cannot be known"), "Use a sized type here.");
            return false;
        }
        if matches!(p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance)) {
            return true;
        }
        // A `'static` written on a reference is the elided form here.
        let named = written.is_some_and(|w| generics::names_lifetime_beyond_static_refs(&p.ast, &p.interner, w));
        if named || (!refs_ok && contains_ref(&self.tys, t)) {
            let tn = self.tn(t);
            self.err(
                "L0705",
                span,
                format!("lust cannot prove that `{tn}` lives for `'static`, which `Any` requires"),
                "Use a type without references here.",
            );
            return false;
        }
        if let Some((code, msg)) = self.static_bound_err(t, 0) {
            self.err(code, span, msg, "Use a type that lives for `'static` here, or add a `'static` bound to the type parameter.");
            return false;
        }
        true
    }
}

impl<'p> Ctx<'p> {
    /// True when `t` holds the type of a closure the parser made from a
    /// std fn value (`Ast::is_eta_closure`): rustc gives the fn item's
    /// type there, one type per fn, but each such closure has its own.
    fn contains_eta_closure(&self, t: Ty) -> bool {
        match self.tys.kind(t) {
            TyKind::Closure(def, a) => {
                self.closure_def_is_eta(def) || self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.contains_eta_closure(e)))
            }
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.contains_eta_closure(e),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.contains_eta_closure(e)),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) => self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.contains_eta_closure(e))),
            _ => false,
        }
    }

    /// True when closure def `def` is an eta closure: its parent fn (the
    /// registered one, else this body) has an eta closure at the ordinal
    /// the def hashes (`closure::closure_def`).
    fn closure_def_is_eta(&self, def: DefId) -> bool {
        let p = self.p;
        let parent = p.gx.closures.get(&def).map_or(self.fid, |c| c.parent);
        let (lo, hi) = p.fn_info(parent).loc.def(&p.ast).exprs;
        let mut order: Vec<ExprId> = (lo..hi).map(ExprId).filter(|&x| matches!(p.ast.expr(x), Expr::Closure { .. })).collect();
        order.sort_by_key(|&x| (p.ast.expr_span(x).lo, x.0));
        let ph = p.def_id(parent).hash;
        order.iter().enumerate().any(|(i, &x)| {
            p.ast.is_eta_closure(x) && crate::def::child_hash(ph, crate::def::DefKind::Closure, "{closure}", i as u32) == def.hash
        })
    }
}

/// True when a reference type occurs anywhere in `t`.
fn contains_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
        TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => contains_ref(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_ref(tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) => {
            tys.is_chars_ty(t) || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| contains_ref(tys, e)))
        }
        TyKind::Dyn(..) => {
            object::principal_of(tys, t).is_some_and(|pr| tys.args(pr.args).iter().any(|g| g.as_ty().is_some_and(|e| contains_ref(tys, e))))
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            contains_ref(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| contains_ref(tys, e))
        }
        _ => false,
    }
}

// ---------- `std::any::type_name` ----------
//
// rustc's exact `type_name::<T>()` string: full defining paths
// (`alloc::vec::Vec<i32>`, `mycrate::mod::S`), lifetimes erased
// except the `'_` rustc shows for a lifetime argument and for a
// reference inside a fn pointer signature, and trailing generic
// arguments equal to their defaults trimmed (`D` for `D<u8>` when
// the default is `u8`, `HashMap<K, V>` without the default hasher).
// None when lust cannot be sure of the exact string: closures, fn
// items, `impl Trait`, unnormalized projections, std-source types
// with no verified row below, and iterator kinds with no row. With
// `open`, a type parameter, projection, or inference variable is a
// placeholder instead of None (a template check: each instance
// decides again with its concrete type).

/// The `type_name` string of `t`, when lust can print it exactly.
pub fn type_name_of(p: &Program, tys: &mut impl TyIntern, t: Ty, open: bool) -> Option<String> {
    tn_ty(p, tys, t, open, false)
}

/// One type in `type_name` form. `in_sig` is true inside a fn
/// pointer signature, where an anonymous reference shows `&'_`.
fn tn_ty(p: &Program, tys: &mut impl TyIntern, t: Ty, open: bool, in_sig: bool) -> Option<String> {
    match tys.kind(t) {
        TyKind::Error => None,
        TyKind::Unit => Some("()".into()),
        TyKind::Bool => Some("bool".into()),
        TyKind::Char => Some("char".into()),
        TyKind::Str => Some("str".into()),
        TyKind::Never => Some("!".into()),
        TyKind::Int(i) => Some(i.name().into()),
        TyKind::Float(f) => Some(f.name().into()),
        TyKind::Ref(r, m, e) => {
            let lt = if in_sig && r != Region::Static { "'_ " } else { "" };
            Some(format!("&{lt}{}{}", if m.is_mut() { "mut " } else { "" }, tn_ty(p, tys, e, open, in_sig)?))
        }
        TyKind::RawPtr(m, e) => Some(format!("*{}{}", if m.is_mut() { "mut " } else { "const " }, tn_ty(p, tys, e, open, in_sig)?)),
        TyKind::Slice(e) => Some(format!("[{}]", tn_ty(p, tys, e, open, in_sig)?)),
        TyKind::Array(e, n) => Some(format!("[{}; {}]", tn_ty(p, tys, e, open, in_sig)?, tn_const(tys, n, open)?)),
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec();
            let parts: Option<Vec<String>> = elems.iter().map(|&e| tn_ty(p, tys, e, open, in_sig)).collect();
            let parts = parts?;
            let trail = if parts.len() == 1 { "," } else { "" };
            Some(format!("({}{trail})", parts.join(", ")))
        }
        TyKind::Adt(..) => tn_adt(p, tys, t, open, in_sig),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            let in_tys: Vec<Ty> = tys.tys_of(s.inputs).to_vec();
            let ins: Option<Vec<String>> = in_tys.iter().map(|&e| tn_ty(p, tys, e, open, true)).collect();
            let out = tn_ty(p, tys, s.output, open, true)?;
            let ret = if s.output == UNIT { String::new() } else { format!(" -> {out}") };
            Some(format!(
                "{}{}fn({}){ret}",
                if s.is_unsafe { "unsafe " } else { "" },
                if s.extern_c { "extern \"C\" " } else { "" },
                ins?.join(", ")
            ))
        }
        TyKind::Dyn(b, _) => tn_dyn(p, tys, tys.dyn_bounds(b).clone(), open),
        TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) if open => Some("_".into()),
        _ => None,
    }
}

/// A const generic argument in `type_name` form.
fn tn_const(tys: &impl TyIntern, c: crate::ty::ConstId, open: bool) -> Option<String> {
    match tys.const_kind(c) {
        ConstKind::Int(v) => Some(format!("{v}")),
        ConstKind::Bool(b) => Some(format!("{b}")),
        ConstKind::Char(ch) => Some(format!("'{ch}'", ch = ch.escape_debug())),
        _ if open => Some("_".into()),
        _ => None,
    }
}

/// One generic argument in `type_name` form.
fn tn_arg(p: &Program, tys: &mut impl TyIntern, g: GenericArg, open: bool, in_sig: bool) -> Option<String> {
    match g {
        GenericArg::Ty(t) => tn_ty(p, tys, t, open, in_sig),
        GenericArg::Lifetime(_) => Some("'_".into()),
        GenericArg::Const(c) => tn_const(tys, c, open),
    }
}

/// `path` plus `<args>` (no brackets when `args` is empty).
fn tn_apply(path: &str, args: Vec<String>) -> String {
    if args.is_empty() { path.to_string() } else { format!("{path}<{}>", args.join(", ")) }
}

/// The first type argument of an Adt type, in `type_name` form.
fn tn_first(p: &Program, tys: &mut impl TyIntern, t: Ty, open: bool, in_sig: bool) -> Option<String> {
    tn_ty(p, tys, tys.adt_first_ty_arg(t)?, open, in_sig)
}

/// An Adt type in `type_name` form: builtin, synthetic std, and
/// hashed/sync/iterator tables first (each row checked against
/// rustc 1.99), then a user type by its defining path.
fn tn_adt(p: &Program, tys: &mut impl TyIntern, t: Ty, open: bool, in_sig: bool) -> Option<String> {
    use crate::ty::BuiltinTy as B;
    let mut one = |p: &Program, tys: &mut _, path: &str| Some(tn_apply(path, vec![tn_first(p, tys, t, open, in_sig)?]));
    match tys.builtin_of(t) {
        Some(B::String) => return Some("alloc::string::String".into()),
        Some(B::Vec) => return one(p, tys, "alloc::vec::Vec"),
        Some(B::Option) => return one(p, tys, "core::option::Option"),
        Some(B::Result) => {
            let (a, b) = tys.result_args(t)?;
            return Some(tn_apply(
                "core::result::Result",
                vec![tn_ty(p, tys, a, open, in_sig)?, tn_ty(p, tys, b, open, in_sig)?],
            ));
        }
        Some(B::Boxed) => return one(p, tys, "alloc::boxed::Box"),
        Some(B::Rc) => return one(p, tys, "alloc::rc::Rc"),
        Some(B::Weak) => return one(p, tys, "alloc::rc::Weak"),
        Some(B::RefCell) => return one(p, tys, "core::cell::RefCell"),
        Some(B::Cell) => return one(p, tys, "core::cell::Cell"),
        Some(B::RefGuard) => return Some(tn_apply("core::cell::Ref", vec!["'_".into(), tn_first(p, tys, t, open, in_sig)?])),
        Some(B::RefMutGuard) => return Some(tn_apply("core::cell::RefMut", vec!["'_".into(), tn_first(p, tys, t, open, in_sig)?])),
        Some(B::Chars) => return Some("core::str::iter::Chars<'_>".into()),
        Some(B::ExitCode) => return Some("std::process::ExitCode".into()),
        Some(B::LocalKey) => return one(p, tys, "std::thread::local::LocalKey"),
        Some(B::AccessError) => return Some("std::thread::local::AccessError".into()),
        Some(B::Fmt(k)) => {
            use crate::ty::fmt::FmtTy as F;
            return Some(match k {
                F::Formatter => "core::fmt::Formatter<'_>".into(),
                F::Arguments => "core::fmt::Arguments<'_>".into(),
                F::DebugStruct => "core::fmt::builders::DebugStruct<'_, '_>".into(),
                F::DebugTuple => "core::fmt::builders::DebugTuple<'_, '_>".into(),
                F::DebugList => "core::fmt::builders::DebugList<'_, '_>".into(),
                F::DebugSet => "core::fmt::builders::DebugSet<'_, '_>".into(),
                F::DebugMap => "core::fmt::builders::DebugMap<'_, '_>".into(),
            });
        }
        Some(B::Sync(k)) => return tn_sync(p, tys, t, k, open, in_sig),
        Some(B::Hash(k)) => return tn_hash(p, tys, t, k, open, in_sig),
        Some(B::Iter(k)) => return tn_iter(p, tys, t, k, open, in_sig),
        None => {}
    }
    let (def, args_id) = tys.adt_parts(t)?;
    // The synthetic std Adts (`generics::std_adts`), by def.
    if let Some(s) = tn_std_adt(p, tys, t, def, open, in_sig) {
        return s;
    }
    let a = p.adt_by_def(def).or_else(|| tys.local_adt(t))?;
    let path = tn_def_path(p, def, p.adt(a).name)?;
    let args: Vec<GenericArg> = tys.args(args_id).to_vec();
    let shown = tn_user_args(p, tys, a, def, &args, open, in_sig)?;
    Some(tn_apply(&path, shown))
}

/// A `SyncTy` in `type_name` form (rustc 1.99 paths; atomics print
/// through the generic `Atomic<T>`).
fn tn_sync(p: &Program, tys: &mut impl TyIntern, t: Ty, k: crate::ty::sync::SyncTy, open: bool, in_sig: bool) -> Option<String> {
    use crate::ty::sync::SyncTy as S;
    let first = tn_first(p, tys, t, open, in_sig);
    let one = |path: &str| Some(tn_apply(path, vec![first.clone()?]));
    let lt_one = |path: &str| Some(tn_apply(path, vec!["'_".into(), first.clone()?]));
    Some(match k {
        S::Arc => return one("alloc::sync::Arc"),
        S::ArcWeak => return one("alloc::sync::Weak"),
        S::AtomicBool => "core::sync::atomic::Atomic<bool>".into(),
        S::AtomicI8 => "core::sync::atomic::Atomic<i8>".into(),
        S::AtomicU8 => "core::sync::atomic::Atomic<u8>".into(),
        S::AtomicI16 => "core::sync::atomic::Atomic<i16>".into(),
        S::AtomicU16 => "core::sync::atomic::Atomic<u16>".into(),
        S::AtomicI32 => "core::sync::atomic::Atomic<i32>".into(),
        S::AtomicU32 => "core::sync::atomic::Atomic<u32>".into(),
        S::AtomicI64 => "core::sync::atomic::Atomic<i64>".into(),
        S::AtomicU64 => "core::sync::atomic::Atomic<u64>".into(),
        S::AtomicIsize => "core::sync::atomic::Atomic<isize>".into(),
        S::AtomicUsize => "core::sync::atomic::Atomic<usize>".into(),
        S::Mutex => return one("std::sync::poison::mutex::Mutex"),
        S::MutexGuard => return lt_one("std::sync::poison::mutex::MutexGuard"),
        S::RwLock => return one("std::sync::poison::rwlock::RwLock"),
        S::RwLockReadGuard => return lt_one("std::sync::poison::rwlock::RwLockReadGuard"),
        S::RwLockWriteGuard => return lt_one("std::sync::poison::rwlock::RwLockWriteGuard"),
        S::PoisonError => return one("std::sync::poison::PoisonError"),
        S::JoinHandle => return one("std::thread::join_handle::JoinHandle"),
        S::Thread => "std::thread::thread::Thread".into(),
        S::ThreadId => "std::thread::id::ThreadId".into(),
        S::ThreadBuilder => "std::thread::builder::Builder".into(),
        S::ScopedJoinHandle => return lt_one("std::thread::scoped::ScopedJoinHandle"),
        S::Sender => return one("std::sync::mpsc::Sender"),
        S::SyncSender => return one("std::sync::mpsc::SyncSender"),
        S::Receiver => return one("std::sync::mpsc::Receiver"),
        S::SendError => return one("std::sync::mpsc::SendError"),
        S::Condvar => "std::sync::poison::condvar::Condvar".into(),
        S::Barrier => "std::sync::barrier::Barrier".into(),
        S::BarrierWaitResult => "std::sync::barrier::BarrierWaitResult".into(),
        S::OnceLock => return one("std::sync::once_lock::OnceLock"),
        S::Duration => "core::time::Duration".into(),
        // No path names these in a form rustc prints from a written
        // type lust accepts (`JoinError` stands for `Box<dyn Any>`).
        S::JoinError | S::Scope => return None,
    })
}

/// A `HashTy` in `type_name` form. The default hasher argument is
/// trimmed, as rustc trims it.
fn tn_hash(p: &Program, tys: &mut impl TyIntern, t: Ty, k: crate::ty::hash::HashTy, open: bool, in_sig: bool) -> Option<String> {
    use crate::ty::hash::HashTy as H;
    let args: Vec<Ty> = tys.adt_parts(t).map(|(_, a)| tys.args(a).iter().filter_map(|g| g.as_ty()).collect()).unwrap_or_default();
    let show = |tys: &mut _, i: usize| tn_ty(p, tys, *args.get(i)?, open, in_sig);
    let random = crate::ty::BuiltinTy::Hash(H::RandomState);
    match k {
        H::HashMap => {
            let trim = args.get(2).is_some_and(|&s| tys.builtin_of(s) == Some(random));
            let mut shown = vec![show(tys, 0)?, show(tys, 1)?];
            if args.len() > 2 && !trim {
                shown.push(show(tys, 2)?);
            }
            Some(tn_apply("std::collections::hash::map::HashMap", shown))
        }
        H::HashSet => {
            let trim = args.get(1).is_some_and(|&s| tys.builtin_of(s) == Some(random));
            let mut shown = vec![show(tys, 0)?];
            if args.len() > 1 && !trim {
                shown.push(show(tys, 1)?);
            }
            Some(tn_apply("std::collections::hash::set::HashSet", shown))
        }
        H::RandomState => Some("std::hash::random::RandomState".into()),
        H::DefaultHasher => Some("std::hash::random::DefaultHasher".into()),
        H::BuildHasherDefault => Some(tn_apply("core::hash::BuildHasherDefault", vec![show(tys, 0)?])),
        H::Entry => Some(tn_apply("std::collections::hash::map::Entry", vec!["'_".into(), show(tys, 0)?, show(tys, 1)?])),
        _ => None,
    }
}

/// An `IterKind` in `type_name` form, for the kinds whose rustc
/// path and argument shape are verified. An argument that does not
/// print (a closure in `Map<I, F>`) rejects the whole string.
fn tn_iter(p: &Program, tys: &mut impl TyIntern, t: Ty, k: crate::ty::iter::IterKind, open: bool, in_sig: bool) -> Option<String> {
    use crate::ty::iter::IterKind as K;
    let args: Vec<GenericArg> = tys.adt_parts(t).map(|(_, a)| tys.args(a).to_vec()).unwrap_or_default();
    let mut arg = |tys: &mut _, i: usize| tn_arg(p, tys, *args.get(i)?, open, in_sig);
    let one = |tys: &mut _, path: &str| Some(tn_apply(path, vec![tn_arg(p, tys, *args.get(0)?, open, in_sig)?]));
    let lt_one = |tys: &mut _, path: &str| Some(tn_apply(path, vec!["'_".into(), tn_arg(p, tys, *args.get(0)?, open, in_sig)?]));
    let two = |tys: &mut _, path: &str| Some(tn_apply(path, vec![tn_arg(p, tys, *args.get(0)?, open, in_sig)?, tn_arg(p, tys, *args.get(1)?, open, in_sig)?]));
    match k {
        K::Range => one(tys, "core::ops::range::Range"),
        K::RangeInclusive => one(tys, "core::ops::range::RangeInclusive"),
        K::RangeFrom => one(tys, "core::ops::range::RangeFrom"),
        K::RangeTo => one(tys, "core::ops::range::RangeTo"),
        K::RangeToInclusive => one(tys, "core::ops::range::RangeToInclusive"),
        K::RangeFull => Some("core::ops::range::RangeFull".into()),
        K::SliceIter => lt_one(tys, "core::slice::iter::Iter"),
        K::SliceIterMut => lt_one(tys, "core::slice::iter::IterMut"),
        K::VecIntoIter => one(tys, "alloc::vec::into_iter::IntoIter"),
        K::ArrayIntoIter => two(tys, "core::array::iter::IntoIter"),
        K::OptionIntoIter => one(tys, "core::option::IntoIter"),
        K::OptionIter => lt_one(tys, "core::option::Iter"),
        K::OptionIterMut => lt_one(tys, "core::option::IterMut"),
        K::ResultIntoIter => one(tys, "core::result::IntoIter"),
        K::ResultIter => lt_one(tys, "core::result::Iter"),
        K::ResultIterMut => lt_one(tys, "core::result::IterMut"),
        K::Enumerate => one(tys, "core::iter::adapters::enumerate::Enumerate"),
        K::Rev => one(tys, "core::iter::adapters::rev::Rev"),
        K::Take => one(tys, "core::iter::adapters::take::Take"),
        K::Skip => one(tys, "core::iter::adapters::skip::Skip"),
        K::Peekable => one(tys, "core::iter::adapters::peekable::Peekable"),
        K::StepBy => one(tys, "core::iter::adapters::step_by::StepBy"),
        K::Copied => one(tys, "core::iter::adapters::copied::Copied"),
        K::Cloned => one(tys, "core::iter::adapters::cloned::Cloned"),
        K::Flatten => one(tys, "core::iter::adapters::flatten::Flatten"),
        K::Chain => two(tys, "core::iter::adapters::chain::Chain"),
        K::Zip => two(tys, "core::iter::adapters::zip::Zip"),
        K::Map => two(tys, "core::iter::adapters::map::Map"),
        K::Filter => two(tys, "core::iter::adapters::filter::Filter"),
        K::FilterMap => two(tys, "core::iter::adapters::filter_map::FilterMap"),
        K::MapWhile => two(tys, "core::iter::adapters::map_while::MapWhile"),
        K::TakeWhile => two(tys, "core::iter::adapters::take_while::TakeWhile"),
        K::SkipWhile => two(tys, "core::iter::adapters::skip_while::SkipWhile"),
        K::Inspect => two(tys, "core::iter::adapters::inspect::Inspect"),
        K::Windows => lt_one(tys, "core::slice::iter::Windows"),
        K::Chunks => lt_one(tys, "core::slice::iter::Chunks"),
        K::ChunksMut => lt_one(tys, "core::slice::iter::ChunksMut"),
        K::ChunksExact => lt_one(tys, "core::slice::iter::ChunksExact"),
        K::ChunksExactMut => lt_one(tys, "core::slice::iter::ChunksExactMut"),
        K::Utf8Chunks => Some("core::str::lossy::Utf8Chunks<'_>".into()),
        K::Utf8Chunk => Some("core::str::lossy::Utf8Chunk<'_>".into()),
        K::CharIndices => Some("core::str::iter::CharIndices<'_>".into()),
        K::VecDrain => lt_one(tys, "alloc::vec::drain::Drain"),
        K::StringDrain => Some("alloc::string::Drain<'_>".into()),
        K::ByNext => arg(tys, 0),
        K::MapIter => Some(tn_apply("std::collections::hash::map::Iter", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::MapIterMut => Some(tn_apply("std::collections::hash::map::IterMut", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::MapKeys => Some(tn_apply("std::collections::hash::map::Keys", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::MapValues => Some(tn_apply("std::collections::hash::map::Values", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::MapValuesMut => Some(tn_apply("std::collections::hash::map::ValuesMut", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::MapIntoIter => two(tys, "std::collections::hash::map::IntoIter"),
        K::MapIntoKeys => two(tys, "std::collections::hash::map::IntoKeys"),
        K::MapIntoValues => two(tys, "std::collections::hash::map::IntoValues"),
        K::SetIter => lt_one(tys, "std::collections::hash::set::Iter"),
        K::SetIntoIter => one(tys, "std::collections::hash::set::IntoIter"),
        K::MapDrain => Some(tn_apply("std::collections::hash::map::Drain", vec!["'_".into(), arg(tys, 0)?, arg(tys, 1)?])),
        K::SetDrain => lt_one(tys, "std::collections::hash::set::Drain"),
        K::StrSplit => tn_str_split(p, tys, &args, open, in_sig),
        K::Args => Some("std::env::Args".into()),
        _ => None,
    }
}

/// A `str` split iterator in `type_name` form (see `collect::ty_name`
/// for the mode read).
fn tn_str_split(p: &Program, tys: &mut impl TyIntern, args: &[GenericArg], open: bool, in_sig: bool) -> Option<String> {
    use crate::ty::iter::SplitMode as M;
    let tys_arg: Vec<Ty> = args.iter().filter_map(|g| g.as_ty()).collect();
    let mode = tys_arg.get(1).and_then(|&m| crate::ty::iter::split_mode(tys, m))?;
    let mut pat = || tn_arg(p, tys, *args.first()?, open, in_sig);
    Some(match mode {
        M::SplitWhitespace => "core::str::iter::SplitWhitespace<'_>".into(),
        M::SplitAsciiWhitespace => "core::str::iter::SplitAsciiWhitespace<'_>".into(),
        M::Lines => "core::str::iter::Lines<'_>".into(),
        M::RSplit => tn_apply("core::str::iter::RSplit", vec!["'_".into(), pat()?]),
        M::SplitTerminator => tn_apply("core::str::iter::SplitTerminator", vec!["'_".into(), pat()?]),
        M::RSplitTerminator => tn_apply("core::str::iter::RSplitTerminator", vec!["'_".into(), pat()?]),
        M::SplitN => tn_apply("core::str::iter::SplitN", vec!["'_".into(), pat()?]),
        M::RSplitN => tn_apply("core::str::iter::RSplitN", vec!["'_".into(), pat()?]),
        M::SplitInclusive => tn_apply("core::str::iter::SplitInclusive", vec!["'_".into(), pat()?]),
        _ => tn_apply("core::str::iter::Split", vec!["'_".into(), pat()?]),
    })
}

/// The synthetic std Adts (`generics::std_adts`) in `type_name`
/// form, by def. Some(None) for a row with no verified string.
fn tn_std_adt(p: &Program, tys: &mut impl TyIntern, t: Ty, def: DefId, open: bool, in_sig: bool) -> Option<Option<String>> {
    let row = generics::std_adts().iter().position(|r| r.2 == def)?;
    let plain = |s: &str| Some(Some(s.to_string()));
    Some(Some(match row {
        0 => return plain("core::cmp::Ordering"),
        1 => return plain("core::fmt::Error"),
        2 => return plain("core::str::error::Utf8Error"),
        3 => return plain("alloc::string::FromUtf8Error"),
        4 => return plain("core::sync::atomic::Ordering"),
        5 => return plain("std::sync::mpsc::RecvError"),
        6 => return plain("std::sync::mpsc::TryRecvError"),
        7 => return plain("core::any::TypeId"),
        8 => return plain("core::panic::location::Location<'_>"),
        9 => {
            let b = crate::check::collect::cow_arg(tys, t)?;
            tn_apply("alloc::borrow::Cow", vec!["'_".into(), tn_ty(p, tys, b, open, in_sig)?])
        }
        10 => return plain("core::cell::BorrowError"),
        11 => return plain("core::cell::BorrowMutError"),
        12 => tn_apply("core::ops::range::Bound", vec![tn_first(p, tys, t, open, in_sig)?]),
        13 => return plain("core::num::error::TryFromIntError"),
        14 => return plain("core::num::error::IntErrorKind"),
        15 => return plain("core::char::convert::CharTryFromError"),
        16 => return plain("core::char::TryFromCharError"),
        17 => return plain("core::convert::Infallible"),
        18 => return plain("core::num::error::ParseIntError"),
        19 => return plain("core::num::float_parse::ParseFloatError"),
        20 => return plain("core::num::error::FloatErrorKind"),
        21 => return plain("core::str::error::ParseBoolError"),
        22 => return plain("core::char::convert::ParseCharError"),
        23 => return plain("core::char::convert::CharErrorKind"),
        24 => return plain("core::array::TryFromSliceError"),
        25 => tn_apply("core::num::nonzero::NonZero", vec![tn_first(p, tys, t, open, in_sig)?]),
        26 => tn_apply("std::sync::mpsc::TrySendError", vec![tn_first(p, tys, t, open, in_sig)?]),
        27 => return plain("std::sync::WaitTimeoutResult"),
        29 => return plain("std::sync::mpsc::RecvTimeoutError"),
        30 => tn_apply("std::sync::poison::TryLockError", vec![tn_first(p, tys, t, open, in_sig)?]),
        _ => return plain("core::char::convert::CharErrorKind"),
    }))
}

/// Verified `type_name` paths for Adts and traits that come from
/// shipped std source, keyed by the display path collect knows
/// (the public path, which is not always rustc's defining path).
fn tn_std_source_path(display: &str) -> Option<&'static str> {
    Some(match display {
        "core::marker::PhantomData" => "core::marker::PhantomData",
        "core::marker::PhantomPinned" => "core::marker::PhantomPinned",
        "std::collections::VecDeque" | "alloc::collections::VecDeque" => "alloc::collections::vec_deque::VecDeque",
        "std::collections::LinkedList" | "alloc::collections::LinkedList" => "alloc::collections::linked_list::LinkedList",
        "std::collections::BTreeMap" | "alloc::collections::BTreeMap" => "alloc::collections::btree::map::BTreeMap",
        "std::collections::BTreeSet" | "alloc::collections::BTreeSet" => "alloc::collections::btree::set::BTreeSet",
        "std::collections::BinaryHeap" | "alloc::collections::BinaryHeap" => "alloc::collections::binary_heap::BinaryHeap",
        "std::num::Wrapping" => "core::num::wrapping::Wrapping",
        "std::mem::ManuallyDrop" | "core::mem::ManuallyDrop" => "core::mem::manually_drop::ManuallyDrop",
        "std::mem::MaybeUninit" => "core::mem::maybe_uninit::MaybeUninit",
        "std::pin::Pin" => "core::pin::Pin",
        "std::error::Error" => "core::error::Error",
        "std::cell::OnceCell" | "core::cell::OnceCell" => "core::cell::once::OnceCell",
        "std::time::Instant" => "std::time::Instant",
        "std::time::SystemTime" => "std::time::SystemTime",
        "std::path::Path" => "std::path::Path",
        "std::path::PathBuf" => "std::path::PathBuf",
        "std::io::Error" => "core::io::error::Error",
        "std::fs::File" => "std::fs::File",
        "core::time::Duration" | "std::time::Duration" => "core::time::Duration",
        _ => return None,
    })
}

/// The defining path of a user type or trait (`crate::mod::Name`,
/// with a fn-local type's enclosing fns in between, as rustc
/// prints them). None when the resolver tables do not name the def
/// or the def is shipped std source with no verified row.
fn tn_def_path(p: &Program, def: DefId, flat: Sym) -> Option<String> {
    let display = p.display_path(flat);
    if let Some(s) = tn_std_source_path(&display) {
        return Some(s.to_string());
    }
    let tables = p.resolved.as_ref()?;
    // A def inside a function body has no resolver row: its module
    // is the enclosing fn's, found by walking the def parents.
    let mut info = tables.def_info.get(&def);
    let mut local = false;
    if info.is_none() {
        local = true;
        let mut data = p.defs.get(def)?;
        while let Some(parent) = data.parent {
            if let Some(i) = tables.def_info.get(&parent) {
                info = Some(i);
                break;
            }
            data = p.defs.get(parent)?;
        }
    }
    let info = info?;
    let module = tables.modules.get(info.module.0 as usize)?;
    // A type from the shipped std source splice: its display path
    // is a std path, and only the verified rows above may print.
    if module.path.first().is_some_and(|s| tables.std_modules.iter().any(|(n, _)| n == s)) {
        return None;
    }
    if matches!(display.split("::").next(), Some("std" | "core" | "alloc")) && info.module.0 != 0 {
        // A std platform/adapter type whose display path only looks
        // like a source path: not verified, do not guess.
        if tables.std_platform.is_some_and(|(root, _)| module.krate_root == root) {
            return None;
        }
    }
    // Fn-local items: the enclosing fn names sit between the module
    // path and the item name in rustc's print.
    let mut mid: Vec<String> = Vec::new();
    let mut data = p.defs.get(def)?;
    while let Some(parent) = data.parent {
        let pd = p.defs.get(parent)?;
        match pd.kind {
            crate::ty::defs::DefKind::Module => break,
            crate::ty::defs::DefKind::Fn | crate::ty::defs::DefKind::Method | crate::ty::defs::DefKind::AssocFn => {
                mid.push(crate::intern::source_name(p.interner.get(pd.name)).to_string());
                data = pd;
            }
            _ => return None,
        }
    }
    mid.reverse();
    // A fn-local def's display name is bare: its path is the
    // enclosing fn's module path plus the name.
    let display = if local {
        let mut s = String::new();
        for seg in &module.path {
            s.push_str(crate::intern::source_name(p.interner.get(*seg)));
            s.push_str("::");
        }
        s.push_str(&display);
        s
    } else {
        display
    };
    let base = if module.krate_root.0 == 0 {
        let krate = crate::intern::source_name(p.interner.get(tables.modules[0].name)).replace('-', "_");
        format!("{krate}::{display}")
    } else {
        display
    };
    if mid.is_empty() {
        return Some(base);
    }
    // Insert the fn names before the item's own last segment.
    let (head, last) = base.rsplit_once("::")?;
    Some(format!("{head}::{}::{last}", mid.join("::")))
}

/// A user Adt's generic arguments in `type_name` form: lifetimes
/// show as `'_` in their declared positions, and trailing type or
/// const arguments equal to their defaults are trimmed.
fn tn_user_args(p: &Program, tys: &mut impl TyIntern, a: AdtId, def: DefId, args: &[GenericArg], open: bool, in_sig: bool) -> Option<Vec<String>> {
    // One shown entry per declared param when the generics are
    // known (so a lifetime the args omit still shows), else one per
    // stored argument. `value_i` is the entry's index among the
    // type/const params, for the defaults table.
    let mut shown: Vec<(Option<usize>, String)> = Vec::new();
    // The written generics name the lifetime parameters too, which
    // the Adt's own generics omit: rustc prints each as `'_` in its
    // declared position.
    let ast_params: Option<Vec<bool>> = {
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        crate::check::defaults::type_generics(&p.ast, &cx, p.adt(a).name)
            .map(|g| g.params.iter().map(|x| matches!(x, ast::GenericParam::Lifetime { .. })).collect())
    };
    let generics = p.gx.adt_generics.get(a.0 as usize);
    match ast_params {
        Some(is_lt) if !is_lt.is_empty() => {
            let mut ai = 0usize;
            let mut vi = 0usize;
            for lt in is_lt {
                if lt {
                    if matches!(args.get(ai), Some(GenericArg::Lifetime(_))) {
                        ai += 1;
                    }
                    shown.push((None, "'_".into()));
                } else {
                    let g = args.get(ai)?;
                    ai += 1;
                    shown.push((Some(vi), tn_arg(p, tys, *g, open, in_sig)?));
                    vi += 1;
                }
            }
            while ai < args.len() {
                shown.push((None, tn_arg(p, tys, args[ai], open, in_sig)?));
                ai += 1;
            }
        }
        _ => match generics {
        Some(g) if !g.params.is_empty() => {
            let mut ai = 0usize;
            let mut vi = 0usize;
            for param in &g.params {
                match param.kind {
                    ParamKind::Lifetime => {
                        if matches!(args.get(ai), Some(GenericArg::Lifetime(_))) {
                            ai += 1;
                        }
                        shown.push((None, "'_".into()));
                    }
                    ParamKind::Type | ParamKind::Const(_) => {
                        let g = args.get(ai)?;
                        ai += 1;
                        shown.push((Some(vi), tn_arg(p, tys, *g, open, in_sig)?));
                        vi += 1;
                    }
                }
            }
            // Stored arguments past the declared params (an
            // instance's own encoding): show them as they are.
            while ai < args.len() {
                shown.push((None, tn_arg(p, tys, args[ai], open, in_sig)?));
                ai += 1;
            }
        }
        _ => {
            let mut vi = 0usize;
            for g in args {
                let is_lt = matches!(g, GenericArg::Lifetime(_));
                shown.push((if is_lt { None } else { Some(vi) }, tn_arg(p, tys, *g, open, in_sig)?));
                if !is_lt {
                    vi += 1;
                }
            }
        }
        },
    }
    // Trim trailing arguments equal to their defaults (the default
    // substituted with the arguments before it, compared by their
    // printed forms).
    if let Some(defaults) = p.gx.param_defaults.get(&def).cloned() {
        while let Some(&(Some(vi), ref s)) = shown.last() {
            let Some(Some(d)) = defaults.get(vi) else { break };
            let ds = match *d {
                GenericArg::Ty(dt) => {
                    let prefix: Vec<GenericArg> = args.iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
                    let dt = subst(tys, dt, &prefix[..vi.min(prefix.len())]);
                    tn_ty(p, tys, dt, open, in_sig)
                }
                GenericArg::Const(c) => tn_const(tys, c, open),
                GenericArg::Lifetime(_) => None,
            };
            if ds.as_deref() == Some(s.as_str()) {
                shown.pop();
            } else {
                break;
            }
        }
    }
    Some(shown.into_iter().map(|(_, s)| s).collect())
}

/// A trait's path in `type_name` form: a lang trait by its verified
/// row, else the defining path of a user trait.
fn tn_trait_path(p: &Program, def: DefId) -> Option<String> {
    let lang = &p.gx.lang;
    let row = match def {
        d if d == lang.debug => Some("core::fmt::Debug"),
        d if d == lang.display => Some("core::fmt::Display"),
        d if d == lang.any => Some("core::any::Any"),
        d if d == lang.clone => Some("core::clone::Clone"),
        d if d == lang.copy => Some("core::marker::Copy"),
        d if d == lang.iterator => Some("core::iter::traits::iterator::Iterator"),
        d if d == lang.into_iterator => Some("core::iter::traits::collect::IntoIterator"),
        d if d == lang.from_iterator => Some("core::iter::traits::collect::FromIterator"),
        d if d == lang.default => Some("core::default::Default"),
        d if d == lang.from => Some("core::convert::From"),
        d if d == lang.into => Some("core::convert::Into"),
        d if d == lang.hash => Some("core::hash::Hash"),
        d if d == lang.partial_eq => Some("core::cmp::PartialEq"),
        d if d == lang.eq => Some("core::cmp::Eq"),
        d if d == lang.partial_ord => Some("core::cmp::PartialOrd"),
        d if d == lang.ord => Some("core::cmp::Ord"),
        d if d == lang.deref => Some("core::ops::deref::Deref"),
        d if d == lang.deref_mut => Some("core::ops::deref::DerefMut"),
        _ => None,
    };
    if let Some(s) = row {
        return Some(s.to_string());
    }
    let rec = p.gx.index.trait_record(def)?;
    tn_def_path(p, def, rec.name)
}

/// A `dyn` type in `type_name` form: the principal (the Fn family
/// in sugar form), then the auto traits. The region never prints.
fn tn_dyn(p: &Program, tys: &mut impl TyIntern, b: DynBounds, open: bool) -> Option<String> {
    let mut parts: Vec<String> = Vec::new();
    if let Some(pr) = b.principal {
        let tr = pr.value;
        let lang = &p.gx.lang;
        if lang.is_fn_family(tr.def) {
            let name = tn_trait_path(p, tr.def).or_else(|| {
                Some(match () {
                    _ if tr.def == lang.fn_ => "core::ops::function::Fn".into(),
                    _ if tr.def == lang.fn_mut => "core::ops::function::FnMut".into(),
                    _ => "core::ops::function::FnOnce".into(),
                })
            })?;
            let ins_ty = tys.args(tr.args).get(1).and_then(|g| g.as_ty())?;
            let ins: Vec<String> = match tys.kind(ins_ty) {
                TyKind::Tuple(ts) => {
                    let ins_tys: Vec<Ty> = tys.tys_of(ts).to_vec();
                    let v: Option<Vec<String>> = ins_tys.iter().map(|&e| tn_ty(p, tys, e, open, true)).collect();
                    v?
                }
                _ => return None,
            };
            let out = tys.bindings(tr.bindings).first().and_then(|(_, g)| g.as_ty()).filter(|&t| t != UNIT);
            let ret = match out {
                Some(o) => format!(" -> {}", tn_ty(p, tys, o, open, true)?),
                None => String::new(),
            };
            parts.push(format!("{name}({}){ret}", ins.join(", ")));
        } else {
            let name = tn_trait_path(p, tr.def)?;
            let mut shown: Vec<String> = Vec::new();
            let rest: Vec<GenericArg> = tys.args(tr.args).iter().skip(1).copied().collect();
            for g in rest {
                shown.push(tn_arg(p, tys, g, open, false)?);
            }
            let rec = p.gx.index.trait_record(tr.def);
            for (assoc, g) in tys.bindings(tr.bindings).to_vec() {
                let an = rec.and_then(|r| r.assoc_items.iter().find(|(d, _, _)| *d == assoc).map(|(_, n, _)| p.interner.get(*n).to_string()))?;
                shown.push(format!("{an} = {}", tn_arg(p, tys, g, open, false)?));
            }
            parts.push(tn_apply(&name, shown));
        }
    }
    for (on, name) in [
        (b.auto.send, "core::marker::Send"),
        (b.auto.sync, "core::marker::Sync"),
        (b.auto.unpin, "core::marker::Unpin"),
        (b.auto.unwind_safe, "core::panic::unwind_safe::UnwindSafe"),
        (b.auto.ref_unwind_safe, "core::panic::unwind_safe::RefUnwindSafe"),
    ] {
        if on {
            parts.push(name.to_string());
        }
    }
    if parts.is_empty() {
        return None;
    }
    Some(format!("dyn {}", parts.join(" + ")))
}

/// True when an `impl Trait` type occurs anywhere in `t`.
fn contains_opaque(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Opaque(..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => contains_opaque(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_opaque(tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| contains_opaque(tys, e)))
        }
        _ => false,
    }
}
