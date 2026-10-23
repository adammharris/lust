// Trait selection without search (docs/ARCH.md section 2.4), the
// provably-false check behind the clause filter, and normalization
// of associated-type projections (section 2.5).
//
// Selection matches the whole trait reference, Self and every input
// argument, by tentative probe unifications over header patterns.
// At most one probe is ever confirmed. The clause filter can only
// remove candidates whose where clauses are provably false; it
// never selects a candidate because its clauses held, and anything
// it cannot decide stays ambiguous and defers. There is no
// backtracking and no speculative predicate search anywhere here.
//
// The solver runs over the `SolveCx` interface so the checker (with
// body-local inference variables) and mono (with concrete types,
// through `PureCx`) share one algorithm.
use super::index::{ImplId, ImplIndex, ImplRecord, head_of, subst_predicate, subst_trait_ref_pub};
use crate::def::DefId;
use crate::intern::FxMap;
use crate::ty::*;

pub mod eval;

/// The shared depth cap of selection, the clause filter, and
/// normalization (section 2.4 step 7). Re-entering one trait ref on
/// the stack, or passing the cap, is an overflow.
pub const MAX_DEPTH: usize = 64;

/// The unification surface selection needs. `snapshot` and
/// `rollback` make probes tentative: every binding a probe makes is
/// undone by rollback, and fresh variables stay allocated (their ids
/// remain usable in argument lists built during the probe).
pub trait SolveCx {
    /// A saved unification state, restored by `rollback`.
    type Snapshot;
    /// The type store of the running body (or of mono).
    type Store: TyIntern;
    fn tys(&mut self) -> &mut Self::Store;
    /// Deeply follows inference links in one type.
    fn deep_resolve(&mut self, t: Ty) -> Ty;
    /// Unifies two types, binding inference variables. False on a
    /// mismatch; bindings made before the mismatch may stand, which
    /// is why probes run under a snapshot.
    fn unify(&mut self, a: Ty, b: Ty) -> bool;
    /// A fresh type inference variable.
    fn fresh_var(&mut self) -> Ty;
    /// A fresh const inference variable, for an impl's const params
    /// in a probe (`impl<T, const N: usize> Tr for [T; N]`).
    fn fresh_const_var(&mut self) -> ConstId;
    /// Unifies two consts, binding a const variable; the binding is
    /// undone by rollback like a type binding.
    fn unify_const(&mut self, a: ConstId, b: ConstId) -> bool;
    /// The const a const variable is bound to, or the const itself.
    fn resolve_const(&self, c: ConstId) -> ConstId;
    fn snapshot(&mut self) -> Self::Snapshot;
    fn rollback(&mut self, snap: Self::Snapshot);
    /// Records one `ImplSet` read (section 8.2): the bucket for this
    /// trait and Self type was read, and was empty when `failed`.
    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, failed: bool);
    /// Builtin selection for a closure Self type (ARCH 2.9): a closure
    /// implements the Fn traits its kind allows, with no impl in the
    /// index. `Some(Builtin)` confirms and unifies the input tuple with
    /// the closure's parameters; `Some(NoImpl)` is a definite no;
    /// `Some(Ambiguous)` waits for an input that is still an open
    /// projection; `None` (the default, and for traits outside the Fn
    /// family) leaves the obligation to the impl index.
    fn closure_select(&mut self, _obl: TraitRef) -> Option<Selection> {
        None
    }
    /// The `FnOnce::Output` of a closure Self type, for normalization.
    /// `None` when `assoc` is not that def or the closure is unknown.
    fn closure_output(&mut self, _assoc: DefId, _self_ty: Ty) -> Option<Ty> {
        None
    }
    /// A builtin associated type with no impl record behind it
    /// (the scalar `TryFrom` pairs' `Error`, fx-tryfrom), for
    /// normalization. `None` leaves the projection to selection.
    fn builtin_assoc(&mut self, _assoc: DefId, _args: ArgsId) -> Option<Ty> {
        None
    }
    /// Builtin selection for a trait ref with no impl records (the
    /// scalar `TryFrom` and `TryInto` pairs, fx-tryfrom), so a nested
    /// where clause such as `u8: TryFrom<i64>` holds as it does at
    /// the top level. `None` leaves the obligation to the impl index.
    fn builtin_select(&mut self, _obl: TraitRef) -> Option<Selection> {
        None
    }
    /// The structural answer for a trait ref the impl index has no
    /// records for (`Sized` and the auto traits; the derive family
    /// on tuples, arrays, slices, and references): Some(holds) when
    /// this context knows it, None to leave it open. The
    /// provably-false check (section 2.4) asks before it reads an
    /// empty bucket as "no".
    fn structural(&mut self, _tr: TraitRef) -> Option<bool> {
        None
    }
}

/// The answer of one selection (section 2.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selection {
    /// One impl confirmed. `args` are the impl's parameters in
    /// declared order, deeply resolved; a parameter in `unbound`
    /// could not be bound by the header, an obligation binding, or
    /// step 4, and defers (at body end it is the impl-parameter error of step 4). `nested` are
    /// the impl's predicates, substituted and elaborated, which the
    /// caller must prove; a failure there is an error, never a
    /// reason to try another candidate.
    Impl { id: ImplId, args: Vec<GenericArg>, nested: Vec<Predicate>, unbound: Vec<ParamId> },
    /// A param-env predicate proves the obligation (step 1). The
    /// payload is that predicate's index in the env slice passed
    /// to `select`. Mono re-solves with concrete types.
    ParamEvidence(usize),
    /// Two or more answers remain, or the Self type has no known
    /// head yet. The caller defers (step 6).
    Ambiguous,
    /// No candidate can apply and inference cannot change that
    /// (step 5). The caller reports the no-impl error.
    NoImpl,
    /// The depth cap or the cycle set stopped selection (step 7).
    /// The caller reports the selection-overflow error.
    Overflow,
    /// A builtin answer with no impl and no nested obligations: a
    /// closure implementing an Fn trait (`SolveCx::closure_select`).
    Builtin,
}

/// One body's solver state: the selection memo and cycle stack
/// (section 2.4 step 7). Memos are keyed by deeply resolved trait
/// refs, so they never outlive the inference variables they name.
#[derive(Default)]
pub struct Solver {
    /// Deep trait ref to the impl or env index a full selection
    /// confirmed. A hit re-runs that one probe to bind variables,
    /// instead of scanning every candidate again.
    memo: FxMap<TraitRef, MemoSel>,
    /// Deep trait ref to its provably-false answer. The check binds
    /// nothing, so its answers are safe to reuse as they are.
    false_memo: FxMap<TraitRef, bool>,
    /// The trait refs on the selection stack, for cycle detection.
    stack: Vec<TraitRef>,
}

#[derive(Clone, Copy)]
enum MemoSel {
    Impl(ImplId),
    Param(usize),
    NoImpl,
}

impl Solver {
    /// A solver with empty memos, for one body.
    pub fn new() -> Solver {
        Solver::default()
    }
}

/// Deeply resolves every type in one trait ref, so memo keys and
/// candidate probes see the current state of inference.
fn deep_trait_ref<C: SolveCx>(cx: &mut C, tr: TraitRef) -> TraitRef {
    let old_args: Vec<GenericArg> = cx.tys().args(tr.args).to_vec();
    let mut new_args: Vec<GenericArg> = Vec::with_capacity(old_args.len());
    for g in old_args {
        new_args.push(match g {
            GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)),
            GenericArg::Const(c) => GenericArg::Const(cx.resolve_const(c)),
            other => other,
        });
    }
    let args = cx.tys().intern_args(&new_args);
    let old_b: Vec<(DefId, GenericArg)> = cx.tys().bindings(tr.bindings).to_vec();
    let mut new_b: Vec<(DefId, GenericArg)> = Vec::with_capacity(old_b.len());
    for (d, g) in old_b {
        new_b.push((
            d,
            match g {
                GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)),
                other => other,
            },
        ));
    }
    let bindings = cx.tys().intern_bindings(&new_b);
    TraitRef { def: tr.def, args, bindings }
}

/// True when a where-bound names no generic parameter (rustc's
/// "global" bound). The bound itself is proved where it is written
/// (L0612), so selection may answer it from impls.
fn is_global_bound(tys: &impl TyIntern, tr: TraitRef) -> bool {
    tys.args(tr.args).iter().all(|g| match *g {
        GenericArg::Ty(t) => !tys.flags(t).contains_param(),
        GenericArg::Const(c) => !matches!(tys.const_kind(c), ConstKind::Param(_)),
        GenericArg::Lifetime(_) => true,
    })
}

/// The Self type of a trait ref (`args[0]`).
fn self_ty_of(cx: &impl TyIntern, tr: &TraitRef) -> Ty {
    cx.args(tr.args)[0].as_ty().expect("trait ref args start with the Self type")
}

/// Unifies two trait refs that name the same trait: every type
/// argument, and every associated binding present on both sides.
/// A binding written on one side only is an extra fact (an
/// `AssocEq` after elaboration), not a mismatch.
/// True for a rigid Self type of a template check: a type parameter,
/// or a projection over no inference variable (normalization already
/// had its chance). Only the param env and blanket impls can match
/// one, and that set is final, so selection need not defer.
fn is_rigid(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) => true,
        // An `impl Trait` type is rigid where it is opaque: its bounds
        // speak for it (check/opaque.rs).
        TyKind::Projection(..) | TyKind::Opaque(..) => !tys.flags(t).contains_infer(),
        _ => false,
    }
}

fn unify_trait_refs<C: SolveCx>(cx: &mut C, a: TraitRef, b: TraitRef) -> bool {
    let (aa, ba): (Vec<GenericArg>, Vec<GenericArg>) = (cx.tys().args(a.args).to_vec(), cx.tys().args(b.args).to_vec());
    if aa.len() != ba.len() {
        return false;
    }
    for (x, y) in aa.iter().zip(&ba) {
        let ok = match (x, y) {
            (GenericArg::Ty(u), GenericArg::Ty(v)) => cx.unify(*u, *v),
            (GenericArg::Const(u), GenericArg::Const(v)) => cx.unify_const(*u, *v),
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
            _ => x == y,
        };
        if !ok {
            return false;
        }
    }
    let ab: Vec<(DefId, GenericArg)> = cx.tys().bindings(a.bindings).to_vec();
    let bb: Vec<(DefId, GenericArg)> = cx.tys().bindings(b.bindings).to_vec();
    for (assoc, ga) in &ab {
        if let (GenericArg::Ty(x), Some((_, GenericArg::Ty(y)))) = (ga, bb.iter().find(|(d, _)| d == assoc))
            && !cx.unify(*x, *y)
        {
            return false;
        }
    }
    true
}

/// Replaces each projection in an impl header type by a fresh
/// variable, recording `(projection, variable)` (see `probe_impl`).
fn split_projections<C: SolveCx>(cx: &mut C, t: Ty, out: &mut Vec<(Ty, Ty)>) -> Ty {
    if !cx.tys().flags(t).contains_projection() {
        return t;
    }
    match cx.tys().kind(t) {
        TyKind::Projection(..) => {
            let v = cx.fresh_var();
            out.push((t, v));
            v
        }
        TyKind::Ref(r, m, e) => {
            let e = split_projections(cx, e, out);
            cx.tys().intern(TyKind::Ref(r, m, e))
        }
        TyKind::RawPtr(m, e) => {
            let e = split_projections(cx, e, out);
            cx.tys().intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = split_projections(cx, e, out);
            cx.tys().intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = split_projections(cx, e, out);
            cx.tys().intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let old: Vec<Ty> = cx.tys().tys_of(ts).to_vec();
            let new: Vec<Ty> = old.into_iter().map(|e| split_projections(cx, e, out)).collect();
            let ts = cx.tys().intern_tys(&new);
            cx.tys().intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let old: Vec<GenericArg> = cx.tys().args(a).to_vec();
            let new: Vec<GenericArg> = old
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(split_projections(cx, e, out)),
                    other => other,
                })
                .collect();
            let a = cx.tys().intern_args(&new);
            cx.tys().intern(TyKind::Adt(d, a))
        }
        // Other forms keep their projections: a header projection
        // inside a fn pointer or dyn type stays a rigid match.
        _ => t,
    }
}

/// True when type `t` (deeply resolved) mentions one of the
/// inference variables in `vars`.
fn mentions_any<S: TyIntern>(tys: &S, t: Ty, vars: &[Ty]) -> bool {
    if vars.contains(&t) {
        return true;
    }
    match tys.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_any(tys, e, vars),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_any(tys, e, vars)))
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_any(tys, e, vars)),
        _ => false,
    }
}

/// Fresh instantiation arguments for one item's parameters: a fresh
/// variable per type parameter, an erased region per lifetime, and
/// a fresh const variable per const parameter.
fn fresh_inst_args<C: SolveCx>(cx: &mut C, generics: &Generics) -> Vec<GenericArg> {
    generics
        .params
        .iter()
        .map(|p| match p.kind {
            ParamKind::Type => GenericArg::Ty(cx.fresh_var()),
            ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
            ParamKind::Const(_) => GenericArg::Const(cx.fresh_const_var()),
        })
        .collect()
}

impl Solver {
    /// Probes one impl header against the obligation: instantiates
    /// the impl pattern with fresh variables, unifies the whole
    /// trait ref, then unifies each obligation binding with the
    /// impl's binding for that associated item. On success the
    /// probe's bindings stand and the instantiation args are
    /// returned; on failure the caller rolls back.
    ///
    /// A projection in the header (`impl<A: Array> Sink<A::Item> for
    /// P<A>`) matches as a fresh variable, then normalizes once the
    /// header bound the impl's params, as rustc's `match_impl`
    /// normalizes the impl trait ref: a rewrite that disagrees drops
    /// the candidate, and one still blocked on inference comes back
    /// as an `AssocEq` for the nested predicates.
    fn probe_impl<C: SolveCx>(
        &mut self,
        cx: &mut C,
        index: &ImplIndex,
        env: &[Predicate],
        rec: &ImplRecord,
        obl: TraitRef,
    ) -> Option<(Vec<GenericArg>, Vec<Predicate>)> {
        let inst = fresh_inst_args(cx, &rec.generics);
        let mut pattern = subst_trait_ref_pub(cx.tys(), rec.trait_ref, &inst);
        let mut projs: Vec<(Ty, Ty)> = Vec::new();
        let old: Vec<GenericArg> = cx.tys().args(pattern.args).to_vec();
        if old.iter().any(|g| g.as_ty().is_some_and(|t| cx.tys().flags(t).contains_projection())) {
            let new: Vec<GenericArg> = old
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(split_projections(cx, t, &mut projs)),
                    other => other,
                })
                .collect();
            pattern.args = cx.tys().intern_args(&new);
        }
        if !unify_trait_refs(cx, pattern, obl) {
            return None;
        }
        let mut deferred: Vec<Predicate> = Vec::new();
        for (proj, var) in projs {
            let normed = self.normalize_inner(cx, index, env, proj, 0);
            if matches!(cx.tys().kind(normed), TyKind::Projection(..)) && cx.tys().flags(normed).contains_infer() {
                let TyKind::Projection(assoc, trait_args) = cx.tys().kind(normed) else { continue };
                deferred.push(Predicate::AssocEq(Binder::plain(AssocEqData { assoc: assoc.0, trait_args, ty: var })));
            } else if !cx.unify(normed, var) {
                return None;
            }
        }
        // A binding on the obligation (`I: IntoIterator<Item = u32>`)
        // against the impl's assoc type, normalized the same way: the
        // blanket's `Item = <I as Iterator>::Item` is the user impl's type.
        let obl_bindings: Vec<(DefId, GenericArg)> = cx.tys().bindings(obl.bindings).to_vec();
        for (assoc, ga) in obl_bindings {
            let GenericArg::Ty(want) = ga else { continue };
            // A binding that names a supertrait's associated item
            // (`ExactSizeIterator<Item = ..>`) is not this impl's to
            // set: it defers to an equality on that supertrait's
            // projection, with the supertrait ref's own args.
            let pat = match rec.assoc_ty(assoc) {
                Some(pat) => pat,
                None => {
                    let want = self.normalize_inner(cx, index, env, want, 0);
                    let tdef = index.trait_of_assoc(assoc)?;
                    let mut found: Option<ArgsId> = None;
                    let mut seen: Vec<DefId> = Vec::new();
                    let mut stack = vec![obl];
                    while let Some(tr) = stack.pop() {
                        if seen.contains(&tr.def) {
                            continue;
                        }
                        seen.push(tr.def);
                        for pred in index.supertraits_of(cx.tys(), &tr) {
                            let Predicate::Trait(b) = pred else { continue };
                            if b.value.def == tdef {
                                found = Some(b.value.args);
                            } else {
                                stack.push(b.value);
                            }
                        }
                    }
                    let trait_args = found?;
                    deferred.push(Predicate::AssocEq(Binder::plain(AssocEqData { assoc, trait_args, ty: want })));
                    continue;
                }
            };
            let have = subst(cx.tys(), pat, &inst);
            let have = self.normalize_inner(cx, index, env, have, 0);
            let want = self.normalize_inner(cx, index, env, want, 0);
            if let TyKind::Projection(a, trait_args) = cx.tys().kind(have)
                && cx.tys().flags(have).contains_infer()
            {
                deferred.push(Predicate::AssocEq(Binder::plain(AssocEqData { assoc: a.0, trait_args, ty: want })));
                continue;
            }
            if !cx.unify(want, have) {
                return None;
            }
        }
        Some((inst, deferred))
    }

    /// The impl's predicates after confirmation: substituted with
    /// the confirmed args, then elaborated (supertraits and
    /// associated equalities) through the index.
    fn nested_predicates<C: SolveCx>(&self, cx: &mut C, index: &ImplIndex, rec: &ImplRecord, inst: &[GenericArg]) -> Vec<Predicate> {
        let written: Vec<Predicate> = rec.generics.predicates.iter().map(|&p| subst_predicate(cx.tys(), p, inst)).collect();
        // `elaborate` needs a `&dyn Fn` over the store only, but the
        // index's supertrait walk must intern into the same store.
        // Run the fixpoint here instead of through `ty::elaborate`,
        // which stays the one implementation for param envs built
        // over the global store at collect (where a shared provider
        // over an immutable store is exact).
        elaborate_in(cx.tys(), index, &written)
    }

    /// Step 4: binds impl parameters the header left free (the
    /// `unbound` list), from associated equalities in the impl's
    /// own elaborated predicates whose projection normalizes now.
    /// One pass, no search. Obligation bindings already bound their
    /// parameters during the probe (step 4a), so only 4b runs here.
    fn bind_unbound_from_assoc_eqs<C: SolveCx>(
        &mut self,
        cx: &mut C,
        index: &ImplIndex,
        env: &[Predicate],
        nested: &[Predicate],
        inst: &[GenericArg],
    ) {
        for pred in nested {
            let Predicate::AssocEq(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let eq = b.value;
            // Only an equality whose right side holds a still free
            // impl parameter variable can bind it: the variable itself,
            // or a type around it (`F: FnMut() -> Option<T>` binds `T`
            // from the closure's return type, as rustc's projection
            // equality does).
            let rhs = cx.deep_resolve(eq.ty);
            let mut free: Vec<Ty> = Vec::new();
            for t in inst.iter().filter_map(|g| g.as_ty()) {
                let t = cx.deep_resolve(t);
                if matches!(cx.tys().kind(t), TyKind::Infer(_)) {
                    free.push(t);
                }
            }
            let exact = free.contains(&rhs);
            if !exact && !mentions_any(cx.tys(), rhs, &free) {
                continue;
            }
            let proj = cx.tys().intern(TyKind::Projection(AssocId(eq.assoc), eq.trait_args));
            let normed = self.normalize_inner(cx, index, env, proj, 0);
            // "Normalizes now" means the top projection rewrote.
            // Binding the variable to an unrewritten projection (its
            // Ty id can differ from `proj`'s by re-interning) would
            // only move the unknown, so it does not count.
            let normed = cx.deep_resolve(normed);
            if !matches!(cx.tys().kind(normed), TyKind::Projection(..)) && normed != rhs {
                if exact {
                    cx.unify(rhs, normed);
                } else {
                    // A structured side binds all or nothing; the nested
                    // predicate still reports a mismatch.
                    let snap = cx.snapshot();
                    if !cx.unify(rhs, normed) {
                        cx.rollback(snap);
                    }
                }
            }
        }
    }

    /// Confirms one candidate (steps 3 and 4): re-runs its probe
    /// without rollback, binds free impl parameters where step 4
    /// can, and builds the nested predicates the caller must prove.
    /// Callers reach this only with exactly one candidate left.
    fn confirm_impl<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], id: ImplId, obl: TraitRef) -> Selection {
        let rec = index.get(id).clone();
        let Some((inst, deferred)) = self.probe_impl(cx, index, env, &rec, obl) else {
            // The candidate matched a probe a moment ago; a failure
            // here means inference moved under it. Defer rather
            // than guess.
            return Selection::Ambiguous;
        };
        let mut nested = self.nested_predicates(cx, index, &rec, &inst);
        nested.extend(deferred);
        self.bind_unbound_from_assoc_eqs(cx, index, env, &nested, &inst);
        let mut args: Vec<GenericArg> = Vec::with_capacity(inst.len());
        let mut unbound: Vec<ParamId> = Vec::new();
        for (i, g) in inst.iter().enumerate() {
            match g {
                GenericArg::Ty(t) => {
                    let r = cx.deep_resolve(*t);
                    if rec.generics.params[i].kind == ParamKind::Type && matches!(cx.tys().kind(r), TyKind::Infer(_)) {
                        unbound.push(ParamId(i as u32));
                    }
                    args.push(GenericArg::Ty(r));
                }
                GenericArg::Const(c) => {
                    let r = cx.resolve_const(*c);
                    if matches!(cx.tys().const_kind(r), ConstKind::Infer(_)) {
                        unbound.push(ParamId(i as u32));
                    }
                    args.push(GenericArg::Const(r));
                }
                other => args.push(*other),
            }
        }
        Selection::Impl { id, args, nested, unbound }
    }

    /// True when a deeply resolved Self type settles the candidate
    /// set for good: a known head and no inference variable in it
    /// that could still change the head. The head is the outermost
    /// form, so variables inside a fixed constructor cannot.
    fn head_is_settled<C: SolveCx>(&self, cx: &mut C, self_ty: Ty) -> bool {
        let resolved = cx.deep_resolve(self_ty);
        head_of(cx.tys(), resolved, &|t| t).is_some() || is_rigid(cx.tys(), resolved)
    }

    /// Selects evidence for one obligation (the algorithm of
    /// section 2.4). `env` is the elaborated param env already
    /// substituted into this body's types. A confirmed selection
    /// commits its probe bindings; every other answer binds
    /// nothing.
    pub fn select<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], obl: TraitRef) -> Selection {
        // A window check of mono discovery stops after its step budget
        // (check/spec.rs).
        crate::check::spec::step(1);
        let obl = deep_trait_ref(cx, obl);
        if self.stack.len() >= MAX_DEPTH || self.stack.contains(&obl) {
            return Selection::Overflow;
        }
        // A bare parameter Self with no env evidence cannot be
        // selected from impls at all: only the param env speaks
        // for it (mono re-solves the rest with concrete types).
        self.stack.push(obl);
        let out = self.select_inner(cx, index, env, obl);
        self.stack.pop();
        out
    }

    fn select_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], obl: TraitRef) -> Selection {
        // The memo re-runs one known probe instead of scanning.
        match self.memo.get(&obl).copied() {
            Some(MemoSel::Impl(id)) => return self.confirm_impl(cx, index, env, id, obl),
            Some(MemoSel::Param(i)) => {
                if let Some(Predicate::Trait(b)) = env.get(i).copied() {
                    unify_trait_refs(cx, b.value, obl);
                }
                return Selection::ParamEvidence(i);
            }
            Some(MemoSel::NoImpl) => return Selection::NoImpl,
            None => {}
        }

        // A general inference variable as Self selects nothing, not
        // even from the param env: an impl could answer once inference
        // names the type (`?U: Send` with `T: Send` in the env must
        // not bind `?U = T`; the argument may make it `&T`). Defer,
        // as rustc does (ARCH 2.4 step 6).
        {
            let self_ty = self_ty_of(cx.tys(), &obl);
            let deep = cx.deep_resolve(self_ty);
            if matches!(cx.tys().kind(deep), TyKind::Infer(v) if !v.is_int() && !v.is_float()) {
                return Selection::Ambiguous;
            }
        }

        // Step 1: param-env evidence wins over impls. Two matching
        // predicates defer; the first match is never taken. A global
        // bound (one that names no generic parameter, like `A: Tr` on
        // a plain fn) does not win: as in rustc's winnowing, a
        // matching impl answers it, and the bound is used only when
        // no impl matches. A global and a non-global match defer.
        let mut env_hits: Vec<usize> = Vec::new();
        let mut global_hit: Option<usize> = None;
        for (i, pred) in env.iter().enumerate() {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || b.value.def != obl.def {
                continue;
            }
            let snap = cx.snapshot();
            let ok = unify_trait_refs(cx, b.value, obl);
            cx.rollback(snap);
            if !ok {
                continue;
            }
            // Global by its resolved args: a bound noted while an arg was
            // still a variable (an opaque's) is the param's once it binds.
            let resolved: Vec<GenericArg> = cx
                .tys()
                .args(b.value.args)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)),
                    g => g,
                })
                .collect();
            let resolved = TraitRef { args: cx.tys().intern_args(&resolved), ..b.value };
            if is_global_bound(cx.tys(), resolved) {
                global_hit.get_or_insert(i);
            } else {
                env_hits.push(i);
            }
        }
        // Hits that name one trait ref once their variables resolve are
        // one piece of evidence (an opaque's bounds noted before and
        // after its args were inferred).
        if env_hits.len() > 1 {
            let key = |cx: &mut C, i: usize| -> Option<Vec<GenericArg>> {
                let Predicate::Trait(b) = env[i] else { return None };
                let args: Vec<GenericArg> = cx.tys().args(b.value.args).to_vec();
                Some(args.into_iter().map(|g| match g { GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)), g => g }).collect())
            };
            let first = key(cx, env_hits[0]);
            if first.is_some() && env_hits[1..].iter().all(|&i| key(cx, i) == first) {
                env_hits.truncate(1);
            }
        }
        match env_hits.len() {
            1 if global_hit.is_none() => {
                let i = env_hits[0];
                if let Predicate::Trait(b) = env[i] {
                    unify_trait_refs(cx, b.value, obl);
                }
                self.memo.insert(obl, MemoSel::Param(i));
                return Selection::ParamEvidence(i);
            }
            1.. => return Selection::Ambiguous,
            _ => {}
        }

        // Step 6's other half, checked before any candidate can
        // confirm: with no known head, selection always defers.
        // A blanket probe binding here would pick the blanket
        // before inference can name the concrete impl. An integer
        // or float literal variable is the exception: it can only
        // become a numeric type, so the impls for those are its
        // candidates, and exactly one match selects it (as rustc).
        {
            let self_ty = self_ty_of(cx.tys(), &obl);
            let deep = cx.deep_resolve(self_ty);
            let numeric_var = matches!(cx.tys().kind(deep), TyKind::Infer(v) if v.is_int() || v.is_float());
            if head_of(cx.tys(), deep, &|t| t).is_none() && !numeric_var && !is_rigid(cx.tys(), deep) {
                return Selection::Ambiguous;
            }
        }

        // Closures implement the Fn traits builtin (ARCH 2.9), and so do
        // `dyn Fn` types and core's forwarding impls for `&F`, `&mut F`,
        // and `Box<F>` (the hook answers None for other types).
        {
            let self_ty = self_ty_of(cx.tys(), &obl);
            let deep = cx.deep_resolve(self_ty);
            if matches!(
                cx.tys().kind(deep),
                TyKind::Closure(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Dyn(..) | TyKind::Ref(..) | TyKind::Adt(..)
            ) && let Some(sel) = cx.closure_select(obl)
            {
                return sel;
            }
        }

        if let Some(sel) = cx.builtin_select(obl) {
            return sel;
        }

        // Step 2: header candidates by probe unification.
        let self_ty = self_ty_of(cx.tys(), &obl);
        let cands: Vec<ImplId> = {
            // `candidates` reads through an immutable store view;
            // resolve in a snapshot-free way by deep-resolving Self
            // first, so `&|t| t` is exact for its head test.
            let self_deep = cx.deep_resolve(self_ty);
            index.candidates(cx.tys(), obl.def, self_deep, &|t| t)
        };
        cx.record_impl_set(obl.def, self_ty, cands.is_empty());
        let mut matched: Vec<ImplId> = Vec::new();
        for id in cands {
            let rec = index.get(id).clone();
            let snap = cx.snapshot();
            let ok = self.probe_impl(cx, index, env, &rec, obl).is_some();
            cx.rollback(snap);
            if ok {
                matched.push(id);
            }
        }

        // Step 3: the clause filter. It runs only when more than
        // one candidate matched and Self is settled enough to ask
        // the provably-false question.
        if matched.len() > 1 && self.head_is_settled(cx, self_ty) {
            let before = matched.clone();
            matched.retain(|&id| {
                let rec = index.get(id).clone();
                let snap = cx.snapshot();
                let dropped = match self.probe_impl(cx, index, env, &rec, obl) {
                    Some((inst, _)) => rec.generics.predicates.iter().any(|&p| {
                        let p = subst_predicate(cx.tys(), p, &inst);
                        matches!(p, Predicate::Trait(b) if b.count == 0)
                            && self.provably_false(
                                cx,
                                index,
                                env,
                                match p {
                                    Predicate::Trait(b) => b.value,
                                    _ => unreachable!(),
                                },
                            )
                    }),
                    None => true,
                };
                cx.rollback(snap);
                !dropped
            });
            let _ = before;
        }

        match matched.len() {
            1 => {
                let id = matched[0];
                self.memo.insert(obl, MemoSel::Impl(id));
                self.confirm_impl(cx, index, env, id, obl)
            }
            0 if global_hit.is_some() => {
                let i = global_hit.unwrap_or_default();
                if let Predicate::Trait(b) = env[i] {
                    unify_trait_refs(cx, b.value, obl);
                }
                self.memo.insert(obl, MemoSel::Param(i));
                Selection::ParamEvidence(i)
            }
            0 => {
                // Step 5 or step 6, by whether inference can still
                // change the candidate set.
                if self.head_is_settled(cx, self_ty) {
                    self.memo.insert(obl, MemoSel::NoImpl);
                    Selection::NoImpl
                } else {
                    Selection::Ambiguous
                }
            }
            _ => Selection::Ambiguous,
        }
    }

    /// The provably-false check of section 2.4. True only on a
    /// definite "no": a param-env match, an unknown head, a cycle,
    /// a cap, or a clause that can hold all answer false. Binds
    /// nothing and commits nothing; records the same `ImplSet`
    /// reads as a failed selection.
    pub fn provably_false<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], tr: TraitRef) -> bool {
        let tr = deep_trait_ref(cx, tr);
        if let Some(&memo) = self.false_memo.get(&tr) {
            return memo;
        }
        let out = self.provably_false_inner(cx, index, env, tr);
        self.false_memo.insert(tr, out);
        out
    }

    fn provably_false_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], tr: TraitRef) -> bool {
        if self.stack.len() >= MAX_DEPTH || self.stack.contains(&tr) {
            return false;
        }
        // A param-env match can hold by definition.
        for pred in env {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || b.value.def != tr.def {
                continue;
            }
            let snap = cx.snapshot();
            let ok = unify_trait_refs(cx, b.value, tr);
            cx.rollback(snap);
            if ok {
                return false;
            }
        }
        let self_ty = self_ty_of(cx.tys(), &tr);
        let self_deep = cx.deep_resolve(self_ty);
        // The Fn traits of closures, fn items, fn pointers, and the
        // forwarding impls are builtin (no records), as in `select`.
        if matches!(
            cx.tys().kind(self_deep),
            TyKind::Closure(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Dyn(..) | TyKind::Ref(..) | TyKind::Adt(..)
        ) {
            let snap = cx.snapshot();
            let answer = cx.closure_select(tr);
            cx.rollback(snap);
            if let Some(sel) = answer {
                return matches!(sel, Selection::NoImpl);
            }
        }
        // An integer or float literal variable is one of a closed set
        // of heads, which `candidates` reads all of (`{integer}:
        // Into<S>` is false when no `From` impl of S takes an integer).
        let literal_var = matches!(cx.tys().kind(self_deep), TyKind::Infer(v) if v.is_int() || v.is_float());
        if !literal_var && head_of(cx.tys(), self_deep, &|t| t).is_none() {
            return false;
        }
        // A trait that needs `Self: Sized` never holds for an unsized
        // head.
        if index.sized_only.contains(&tr.def) && matches!(cx.tys().kind(self_deep), TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..)) {
            return true;
        }
        // Traits answered by structure: an empty bucket is no answer.
        if let Some(holds) = cx.structural(tr) {
            return !holds;
        }
        if index.structural.contains(&tr.def) {
            return false;
        }
        if index.derive_family.contains(&tr.def)
            && matches!(
                cx.tys().kind(self_deep),
                TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::Closure(..)
            )
        {
            return false;
        }
        let cands = index.candidates(cx.tys(), tr.def, self_deep, &|t| t);
        cx.record_impl_set(tr.def, self_ty, cands.is_empty());
        if cands.is_empty() {
            return true;
        }
        // False only when every candidate is dead: its header does
        // not actually match, or one of its trait clauses is itself
        // provably false under its own probe bindings. Recursing
        // through candidates is what makes the two-level
        // `Box<[T]>` case work.
        self.stack.push(tr);
        let mut all_dead = true;
        'cands: for id in cands {
            let rec = index.get(id).clone();
            let snap = cx.snapshot();
            let dead = match self.probe_impl(cx, index, env, &rec, tr) {
                None => true,
                Some((inst, _)) => {
                    let mut any_false_clause = false;
                    for &p in &rec.generics.predicates {
                        let p = subst_predicate(cx.tys(), p, &inst);
                        if let Predicate::Trait(b) = p
                            && b.count == 0
                            && self.provably_false(cx, index, env, b.value)
                        {
                            any_false_clause = true;
                            break;
                        }
                    }
                    any_false_clause
                }
            };
            cx.rollback(snap);
            if !dead {
                all_dead = false;
                break 'cands;
            }
        }
        self.stack.pop();
        all_dead
    }
}

/// Elaboration over a mutable store: the fixpoint of section 2.1
/// (written predicates, supertraits through the index, one
/// `AssocEq` per type binding under its binder, deduplicated in
/// first-occurrence order). `ty::elaborate` is the same fixpoint
/// over an immutable store plus a caller provider, for the global
/// param envs in `Defs`; bodies elaborate substituted predicates
/// here because supertrait substitution must intern into the
/// body's own store.
pub fn elaborate_in(tys: &mut impl TyIntern, index: &ImplIndex, written: &[Predicate]) -> Vec<Predicate> {
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
            for &(assoc, arg) in tys.bindings(b.value.bindings) {
                if let GenericArg::Ty(ty) = arg {
                    work.push(Predicate::AssocEq(Binder { count: b.count, value: AssocEqData { assoc, trait_args: b.value.args, ty } }));
                }
            }
            work.extend(index.supertraits_of(tys, &b.value));
        }
    }
    out
}

/// The type a dyn principal gives associated type `assoc`: its own
/// binding (keyed by the assoc def, so a supertrait's assoc too), or
/// one a supertrait bound fixes (`trait Sub: Base<Out = u8>`).
pub fn dyn_assoc_binding(tys: &mut impl TyIntern, index: &ImplIndex, principal: TraitRef, assoc: DefId) -> Option<Ty> {
    let mut work = vec![principal];
    let mut seen: Vec<TraitRef> = Vec::new();
    while let Some(tr) = work.pop() {
        if seen.contains(&tr) {
            continue;
        }
        seen.push(tr);
        if let Some(t) = tys.bindings(tr.bindings).iter().find(|(d, _)| *d == assoc).and_then(|(_, g)| g.as_ty()) {
            return Some(t);
        }
        for pred in index.supertraits_of(tys, &tr) {
            match pred {
                Predicate::Trait(b) if b.count == 0 && tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(DYN_SELF) => work.push(b.value),
                Predicate::AssocEq(b)
                    if b.count == 0 && b.value.assoc == assoc && tys.args(b.value.trait_args).first().and_then(|g| g.as_ty()) == Some(DYN_SELF) =>
                {
                    return Some(b.value.ty);
                }
                _ => {}
            }
        }
    }
    None
}

/// Normalizes one type (section 2.5): rewrites projections through
/// the impl selection picks, through param-env associated
/// equalities, and recurses. A projection that cannot rewrite
/// stays a projection. This is the `normalize` of section 2.1; it
/// lives with selection because it needs the solver, while
/// `ty::subst` stays pure in `ty`.
pub fn normalize<C: SolveCx>(solver: &mut Solver, cx: &mut C, index: &ImplIndex, env: &[Predicate], t: Ty) -> Ty {
    solver.normalize_inner(cx, index, env, t, 0)
}

impl Solver {
    fn normalize_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], t: Ty, depth: usize) -> Ty {
        let t = cx.deep_resolve(t);
        if depth >= MAX_DEPTH || !cx.tys().flags(t).contains_projection() {
            return t;
        }
        match cx.tys().kind(t) {
            TyKind::Projection(assoc, args) => {
                // `<Closure as FnOnce<A>>::Output` is the closure's
                // return type (ARCH 2.9), with no impl to read it from.
                if let Some(self_ty) = cx.tys().args(args).first().and_then(|g| g.as_ty()) {
                    let deep = cx.deep_resolve(self_ty);
                    if matches!(
                        cx.tys().kind(deep),
                        TyKind::Closure(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Dyn(..) | TyKind::Ref(..) | TyKind::Adt(..)
                    ) && let Some(out) = cx.closure_output(assoc.0, deep)
                    {
                        return self.normalize_inner(cx, index, env, out, depth + 1);
                    }
                    // `<dyn Tr<A = X> as Tr>::A` is the binding the dyn
                    // type writes (the builtin object impl has no record
                    // to read it from).
                    if let TyKind::Dyn(b, _) = cx.tys().kind(deep)
                        && let Some(pr) = cx.tys().dyn_bounds(b).principal
                        && let Some(out) = dyn_assoc_binding(cx.tys(), index, pr.value, assoc.0)
                    {
                        return self.normalize_inner(cx, index, env, out, depth + 1);
                    }
                }
                let Some(trait_def) = index.trait_of_assoc(assoc.0) else { return t };
                // Normalize inside the trait args first, so nested
                // projections reach selection in their simplest form.
                let normed_args = self.normalize_args(cx, index, env, args, depth + 1);
                // A builtin assoc with no impl record (a scalar
                // `TryFrom` pair's `Error`, fx-tryfrom).
                if let Some(out) = cx.builtin_assoc(assoc.0, normed_args) {
                    return self.normalize_inner(cx, index, env, out, depth + 1);
                }
                let t = cx.tys().intern(TyKind::Projection(assoc, normed_args));
                let tr = TraitRef { def: trait_def, args: normed_args, bindings: EMPTY_BINDINGS };
                match self.select(cx, index, env, tr) {
                    Selection::Impl { id, args: inst, .. } => {
                        let rec = index.get(id);
                        match rec.assoc_ty(assoc.0) {
                            Some(pat) => {
                                let bound = subst(cx.tys(), pat, &inst);
                                self.normalize_inner(cx, index, env, bound, depth + 1)
                            }
                            None => t,
                        }
                    }
                    Selection::ParamEvidence(_) => match self.env_assoc_eq(cx, env, assoc.0, normed_args) {
                        Some(ty) => self.normalize_inner(cx, index, env, ty, depth + 1),
                        None => t,
                    },
                    _ => t,
                }
            }
            TyKind::Ref(r, m, e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = cx.tys().tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.normalize_inner(cx, index, env, e, depth + 1)).collect();
                let ts = cx.tys().intern_tys(&new);
                cx.tys().intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Adt(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::FnDef(d, a))
            }
            TyKind::Closure(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Closure(d, a))
            }
            TyKind::Opaque(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Opaque(d, a))
            }
            TyKind::FnPtr(sig) => {
                let b = cx.tys().sig(sig);
                let old: Vec<Ty> = cx.tys().tys_of(b.value.inputs).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.normalize_inner(cx, index, env, e, depth + 1)).collect();
                let inputs = cx.tys().intern_tys(&new);
                let output = self.normalize_inner(cx, index, env, b.value.output, depth + 1);
                let sig = cx.tys().intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..b.value } });
                cx.tys().intern(TyKind::FnPtr(sig))
            }
            // `dyn Tr<A = <X as U>::B>`: the principal's args and
            // bindings (`RuleExt::boxed` returns `Box<dyn Rule<Out =
            // Self::Out>>`).
            TyKind::Dyn(bid, r) => {
                let old = cx.tys().dyn_bounds(bid).clone();
                let Some(pr) = old.principal else { return t };
                let args = self.normalize_args(cx, index, env, pr.value.args, depth + 1);
                let binds: Vec<(DefId, GenericArg)> = cx.tys().bindings(pr.value.bindings).to_vec();
                let binds: Vec<(DefId, GenericArg)> = binds
                    .into_iter()
                    .map(|(d, g)| match g {
                        GenericArg::Ty(e) => (d, GenericArg::Ty(self.normalize_inner(cx, index, env, e, depth + 1))),
                        other => (d, other),
                    })
                    .collect();
                let bindings = cx.tys().intern_bindings(&binds);
                let principal = Some(Binder { count: pr.count, value: TraitRef { args, bindings, ..pr.value } });
                let bid = cx.tys().intern_dyn_bounds(DynBounds { principal, ..old });
                cx.tys().intern(TyKind::Dyn(bid, r))
            }
            _ => t,
        }
    }

    fn normalize_args<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], a: ArgsId, depth: usize) -> ArgsId {
        let old: Vec<GenericArg> = cx.tys().args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.normalize_inner(cx, index, env, e, depth)),
                other => other,
            })
            .collect();
        cx.tys().intern_args(&new)
    }

    /// The right side of a param-env associated equality for this
    /// projection, matched under its binder. Only rank-0 binders
    /// match here; a higher-ranked equality (a `for<'a> Fn` output)
    /// is instantiated by the closure call path, not by this
    /// rewrite, and the projection stays.
    fn env_assoc_eq<C: SolveCx>(&self, cx: &mut C, env: &[Predicate], assoc: DefId, trait_args: ArgsId) -> Option<Ty> {
        for pred in env {
            let Predicate::AssocEq(b) = pred else { continue };
            if b.count != 0 || b.value.assoc != assoc {
                continue;
            }
            let snap = cx.snapshot();
            let (xs, ys): (Vec<GenericArg>, Vec<GenericArg>) =
                (cx.tys().args(b.value.trait_args).to_vec(), cx.tys().args(trait_args).to_vec());
            let ok = xs.len() == ys.len()
                && xs.iter().zip(&ys).all(|(x, y)| match (x, y) {
                    (GenericArg::Ty(u), GenericArg::Ty(v)) => cx.unify(*u, *v),
                    _ => x == y,
                });
            if ok {
                // Keep the bindings: they only ever equate the
                // projection's own args with the env fact's args.
                return Some(b.value.ty);
            }
            cx.rollback(snap);
        }
        None
    }
}

// ---------- A pure SolveCx over a body-local store ----------

/// A self-contained `SolveCx`: a body-local `Tys` plus its own
/// inference variables with a rollback trail. Mono uses it to
/// re-solve param evidence over concrete types (its variables exist
/// only inside impl probes), and unit tests drive selection with
/// it. `reads` records every `ImplSet` read as
/// `(trait, Self type, bucket was empty)`, which mono translates
/// into graph reads and tests assert on.
pub struct PureCx<'g> {
    pub tys: Tys<'g>,
    vars: Vec<Option<Ty>>,
    /// Const variable bindings; a const variable is `ConstKind::Infer`
    /// of its index here.
    consts: Vec<Option<ConstId>>,
    /// Bound variables in binding order: type variable indexes, and
    /// const variable indexes tagged with `CONST_TRAIL`.
    trail: Vec<u32>,
    pub reads: Vec<(DefId, Ty, bool)>,
}

/// Marks a const variable on `PureCx::trail`.
const CONST_TRAIL: u32 = 1 << 31;

impl<'g> PureCx<'g> {
    /// A pure context over the given global store.
    pub fn new(global: &'g GlobalTys) -> PureCx<'g> {
        PureCx { tys: Tys::new(global), vars: Vec::new(), consts: Vec::new(), trail: Vec::new(), reads: Vec::new() }
    }

    fn resolve_shallow(&self, mut t: Ty) -> Ty {
        while let TyKind::Infer(v) = self.tys.kind(t) {
            match self.vars[v.index() as usize] {
                Some(b) => t = b,
                None => return t,
            }
        }
        t
    }

    fn occurs(&self, var: u32, t: Ty) -> bool {
        // A type with no variable in it is a DAG that a walk would visit
        // as a tree: exponential on a doubling type (`((T, T), (T, T))`).
        if !self.tys.flags(t).contains_infer() {
            return false;
        }
        let t = self.resolve_shallow(t);
        match self.tys.kind(t) {
            TyKind::Infer(v) => v.index() == var,
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.occurs(var, e),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
                self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.occurs(var, e)))
            }
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.occurs(var, e)),
            _ => false,
        }
    }

    fn bind(&mut self, var: u32, t: Ty) {
        self.trail.push(var);
        self.vars[var as usize] = Some(t);
    }

    fn unify_args(&mut self, a: ArgsId, b: ArgsId) -> bool {
        let n = self.tys.args(a).len();
        if n != self.tys.args(b).len() {
            // An Adt in a dyn's `Fn*` sugar may carry its late-bound
            // lifetimes (`Lifetime(DYN_LATE)`, R11); regions take no part.
            let strip = |x: ArgsId| -> Vec<GenericArg> {
                self.tys.args(x).iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect()
            };
            let (xs, ys) = (strip(a), strip(b));
            if xs.len() == n && ys.len() == self.tys.args(b).len() {
                return false;
            }
            return xs.len() == ys.len()
                && xs.into_iter().zip(ys).all(|(x, y)| match (x, y) {
                    (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                    (GenericArg::Const(x), GenericArg::Const(y)) => self.unify_const(x, y),
                    (x, y) => x == y,
                });
        }
        for i in 0..n {
            let ok = match (self.tys.args(a)[i], self.tys.args(b)[i]) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                (GenericArg::Const(x), GenericArg::Const(y)) => self.unify_const(x, y),
                (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
                (x, y) => x == y,
            };
            if !ok {
                return false;
            }
        }
        true
    }
}

impl<'g> SolveCx for PureCx<'g> {
    type Snapshot = usize;
    type Store = Tys<'g>;

    /// A scalar `TryFrom` pair's `Error` (fx-tryfrom), by the same
    /// table body checking uses.
    fn builtin_assoc(&mut self, assoc: DefId, args: ArgsId) -> Option<Ty> {
        use crate::check::generics as g;
        let a: Vec<Ty> = self.tys.args(args).iter().filter_map(|x| x.as_ty()).collect();
        let [a0, a1] = a[..] else { return None };
        let (src, dst) = if assoc == g::try_from_error_assoc() {
            (a1, a0)
        } else if assoc == g::try_into_error_assoc() {
            (a0, a1)
        } else {
            return None;
        };
        let src = self.deep_resolve(src);
        let dst = self.deep_resolve(dst);
        if crate::check::tryfrom::slice_try_shape(&self.tys, src, dst) {
            return Some(g::try_from_slice_error_ty(&mut self.tys));
        }
        if crate::check::tryfrom::vec_try_shape(&self.tys, src, dst) {
            return Some(src);
        }
        let (sk, dk) = (self.tys.kind(src), self.tys.kind(dst));
        let sort = crate::check::tryfrom::scalar_try_from(sk, dk)?;
        Some(match sort {
            crate::check::tryfrom::TryErr::Infallible => g::infallible_ty(&mut self.tys),
            crate::check::tryfrom::TryErr::Int => g::try_from_int_error_ty(&mut self.tys),
            crate::check::tryfrom::TryErr::CharFrom => g::char_try_from_error_ty(&mut self.tys),
            crate::check::tryfrom::TryErr::FromChar => g::try_from_char_error_ty(&mut self.tys),
            crate::check::tryfrom::TryErr::Slice => g::try_from_slice_error_ty(&mut self.tys),
        })
    }

    fn tys(&mut self) -> &mut Tys<'g> {
        &mut self.tys
    }

    /// Deeply resolves variables, rebuilding compound types whose
    /// parts moved. A type with no inference variable (the cached
    /// flag) comes back as it is.
    fn deep_resolve(&mut self, t: Ty) -> Ty {
        let t = self.resolve_shallow(t);
        if !self.tys.flags(t).contains_infer() {
            return t;
        }
        match self.tys.kind(t) {
            TyKind::Ref(r, m, e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.deep_resolve(e);
                let n = self.resolve_const(n);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.deep_resolve(e)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let old: Vec<GenericArg> = self.tys.args(a).to_vec();
                let new: Vec<GenericArg> = old
                    .iter()
                    .map(|&g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep_resolve(e)),
                        GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                        other => other,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            TyKind::Projection(d, a) => {
                let old: Vec<GenericArg> = self.tys.args(a).to_vec();
                let new: Vec<GenericArg> = old
                    .iter()
                    .map(|&g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep_resolve(e)),
                        other => other,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Projection(d, a))
            }
            _ => t,
        }
    }

    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve_shallow(a), self.resolve_shallow(b));
        if a == b {
            return true;
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Infer(v), TyKind::Infer(w)) => {
                if v.is_int() && !w.is_int() {
                    self.bind(w.index(), a);
                } else {
                    self.bind(v.index(), b);
                }
                true
            }
            (TyKind::Infer(v), k) | (k, TyKind::Infer(v)) => {
                if v.is_int() && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Infer(_)) { b } else { a };
                if self.occurs(v.index(), other) {
                    return false;
                }
                self.bind(v.index(), other);
                true
            }
            (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && self.unify(x, y),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && self.unify(x, y),
            (TyKind::Slice(x), TyKind::Slice(y)) => self.unify(x, y),
            (TyKind::Array(x, cx), TyKind::Array(y, cy)) => self.unify_const(cx, cy) && self.unify(x, y),
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                let (xs, ys): (Vec<Ty>, Vec<Ty>) = (self.tys.tys_of(x).to_vec(), self.tys.tys_of(y).to_vec());
                xs.len() == ys.len() && xs.iter().zip(&ys).all(|(&u, &v)| self.unify(u, v))
            }
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Projection(d, x), TyKind::Projection(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::FnDef(d, x), TyKind::FnDef(e, y)) => d == e && self.unify_args(x, y),
            (ka, kb) => ka == kb,
        }
    }

    fn fresh_var(&mut self) -> Ty {
        self.vars.push(None);
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, InferKind::General)))
    }

    fn fresh_const_var(&mut self) -> ConstId {
        self.consts.push(None);
        let id = self.consts.len() as u32 - 1;
        self.tys.intern_const(ConstKind::Infer(id))
    }

    fn unify_const(&mut self, a: ConstId, b: ConstId) -> bool {
        let (a, b) = (self.resolve_const(a), self.resolve_const(b));
        if a == b {
            return true;
        }
        let var = |cx: &Self, c: ConstId| match cx.tys.const_kind(c) {
            ConstKind::Infer(i) if (i as usize) < cx.consts.len() => Some(i),
            _ => None,
        };
        match (var(self, a), var(self, b)) {
            (Some(i), _) => {
                self.consts[i as usize] = Some(b);
                self.trail.push(i | CONST_TRAIL);
                true
            }
            (None, Some(j)) => {
                self.consts[j as usize] = Some(a);
                self.trail.push(j | CONST_TRAIL);
                true
            }
            (None, None) => false,
        }
    }

    fn resolve_const(&self, mut c: ConstId) -> ConstId {
        while let ConstKind::Infer(i) = self.tys.const_kind(c) {
            match self.consts.get(i as usize).copied().flatten() {
                Some(b) => c = b,
                None => break,
            }
        }
        c
    }

    fn snapshot(&mut self) -> usize {
        self.trail.len()
    }

    fn rollback(&mut self, snap: usize) {
        while self.trail.len() > snap {
            let var = self.trail.pop().unwrap();
            if var & CONST_TRAIL != 0 {
                self.consts[(var & !CONST_TRAIL) as usize] = None;
            } else {
                self.vars[var as usize] = None;
            }
        }
    }

    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, failed: bool) {
        self.reads.push((trait_def, self_ty, failed));
    }
}

impl PureCx<'_> {
    /// A fresh integer-literal variable, for callers modeling
    /// `{integer}` inference (the `s[x]` case of section 2.4).
    pub fn fresh_int_var(&mut self) -> Ty {
        self.vars.push(None);
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, InferKind::Int)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, LOCAL_CRATE};
    use crate::diag::Span;
    use crate::traits::index::{ImplRecord, Synthetic, TraitRecord, pattern_head};

    fn def(hash: u64) -> DefId {
        DefId { krate: LOCAL_CRATE, hash: DefPathHash(hash) }
    }

    fn ty_param(g: &mut GlobalTys, i: u32) -> Ty {
        g.intern(TyKind::Param(ParamId(i)))
    }

    fn params(n: usize) -> Vec<ParamDef> {
        (0..n).map(|_| ParamDef { name: crate::intern::Sym(0), kind: ParamKind::Type, span: Span::default() }).collect()
    }

    /// Declares a trait with `n_inputs` written params (Self is
    /// prepended by the module convention) and the given supertrait
    /// predicates and associated types.
    fn declare_trait(index: &mut ImplIndex, trait_def: DefId, n_inputs: usize, predicates: Vec<Predicate>, assoc_tys: Vec<DefId>) {
        index.insert_trait(TraitRecord {
            def: trait_def,
            name: crate::intern::Sym(0),
            generics: Generics { parent: None, params: params(n_inputs + 1), predicates },
            assoc_items: assoc_tys.iter().map(|&d| (d, crate::intern::Sym(0), true)).collect(),
            methods: Vec::new(),
            local: true,
            span: Span::default(),
        });
    }

    fn trait_pred(g: &mut impl TyIntern, trait_def: DefId, args: &[Ty]) -> Predicate {
        let args: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = g.intern_args(&args);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    }

    fn trait_ref(g: &mut impl TyIntern, trait_def: DefId, args: &[Ty]) -> TraitRef {
        let args: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = g.intern_args(&args);
        TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }
    }

    /// Inserts one impl; its bucket head comes from `pattern_head`,
    /// exactly as collect computes it.
    fn add_impl(
        g: &mut GlobalTys,
        index: &mut ImplIndex,
        impl_hash: u64,
        trait_def: DefId,
        self_pat: Ty,
        rest_args: &[Ty],
        n_params: usize,
        predicates: Vec<Predicate>,
        assoc_tys: Vec<(DefId, Ty)>,
    ) -> ImplId {
        let mut all = vec![GenericArg::Ty(self_pat)];
        all.extend(rest_args.iter().map(|&t| GenericArg::Ty(t)));
        let args = g.intern_args(&all);
        let (head, blanket) = pattern_head(g, self_pat, &[]).unwrap();
        index.insert_impl(ImplRecord {
            def: def(impl_hash),
            trait_def,
            trait_ref: TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS },
            generics: Generics { parent: None, params: params(n_params), predicates },
            assoc_tys,
            assoc_consts: Vec::new(),
            items: Vec::new(),
            synthetic: Synthetic::None,
            local: true,
            span: Span::default(),
            head,
            blanket,
        })
    }

    fn u8_ty() -> Ty {
        int(IntTy::U8)
    }
    fn u16_ty() -> Ty {
        int(IntTy::U16)
    }

    /// Section 2.4: two impls on one Self with different trait
    /// inputs are picked apart by the whole trait ref.
    #[test]
    fn same_self_different_inputs() {
        let mut g = GlobalTys::new();
        let (tr, s) = (def(10), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, tr, 1, vec![], vec![]);
        let s_ty = g.mk_adt(s, &[]);
        add_impl(&mut g, &mut index, 100, tr, s_ty, &[u8_ty()], 0, vec![], vec![]);
        add_impl(&mut g, &mut index, 101, tr, s_ty, &[u16_ty()], 0, vec![], vec![]);
        for (input, want_hash) in [(u8_ty(), 100u64), (u16_ty(), 101)] {
            let mut cx = PureCx::new(&g);
            let obl = trait_ref(&mut cx.tys, tr, &[s_ty, input]);
            match Solver::new().select(&mut cx, &index, &[], obl) {
                Selection::Impl { id, unbound, .. } => {
                    assert_eq!(index.get(id).def, def(want_hash));
                    assert!(unbound.is_empty());
                }
                other => panic!("expected impl {want_hash}, got {other:?}"),
            }
        }
        // An input no impl names is NoImpl, not a guess.
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty, BOOL]);
        assert_eq!(Solver::new().select(&mut cx, &index, &[], obl), Selection::NoImpl);
        assert!(cx.reads.iter().any(|(d, _, failed)| *d == tr && !failed), "the non-empty bucket read is recorded");
    }

    /// The N1 shape (2.4 step 3): a concrete impl and a bounded
    /// bare-param blanket both match by header; the blanket's
    /// clause is provably false for the concrete type, so the
    /// concrete impl wins. For an iterator type the blanket wins.
    #[test]
    fn clause_filter_picks_concrete_over_blanket() {
        let mut g = GlobalTys::new();
        let (iter_tr, into_tr, local, local_it) = (def(10), def(11), def(20), def(21));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![]);
        declare_trait(&mut index, into_tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        let local_ty = g.mk_adt(local, &[]);
        let it_ty = g.mk_adt(local_it, &[]);
        // impl Iterator for LocalIt; impl IntoIterator for Local;
        // impl<I: Iterator> IntoIterator for I.
        add_impl(&mut g, &mut index, 100, iter_tr, it_ty, &[], 0, vec![], vec![]);
        let concrete = add_impl(&mut g, &mut index, 101, into_tr, local_ty, &[], 0, vec![], vec![]);
        let blanket_pred = trait_pred(&mut g, iter_tr, &[p0]);
        let blanket = add_impl(&mut g, &mut index, 102, into_tr, p0, &[], 1, vec![blanket_pred], vec![]);

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, into_tr, &[local_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, .. } => assert_eq!(id, concrete),
            other => panic!("expected the concrete impl, got {other:?}"),
        }
        // The filter read the Iterator bucket for Local and found
        // it empty: that failed lookup is a recorded read.
        assert!(cx.reads.iter().any(|(d, _, failed)| *d == iter_tr && *failed));

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, into_tr, &[it_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, args, nested, .. } => {
                assert_eq!(id, blanket);
                assert_eq!(args[0].as_ty(), Some(it_ty));
                assert_eq!(nested.len(), 1, "the blanket clause is a nested obligation");
            }
            other => panic!("expected the blanket impl, got {other:?}"),
        }
    }

    /// Two blanket impls whose clauses can both hold stay
    /// ambiguous: the filter never selects on a "yes".
    #[test]
    fn clause_filter_never_selects_on_yes() {
        let mut g = GlobalTys::new();
        let (a_tr, b_tr, tr, s) = (def(10), def(11), def(12), def(20));
        let mut index = ImplIndex::new();
        for t in [a_tr, b_tr, tr] {
            declare_trait(&mut index, t, 0, vec![], vec![]);
        }
        let p0 = ty_param(&mut g, 0);
        let s_ty = g.mk_adt(s, &[]);
        add_impl(&mut g, &mut index, 100, a_tr, s_ty, &[], 0, vec![], vec![]);
        add_impl(&mut g, &mut index, 101, b_tr, s_ty, &[], 0, vec![], vec![]);
        let pa = trait_pred(&mut g, a_tr, &[p0]);
        let pb = trait_pred(&mut g, b_tr, &[p0]);
        add_impl(&mut g, &mut index, 102, tr, p0, &[], 1, vec![pa], vec![]);
        add_impl(&mut g, &mut index, 103, tr, p0, &[], 1, vec![pb], vec![]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty]);
        assert_eq!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Ambiguous);
    }

    /// The two-level shape (2.4): `Box2<[u8]>` matches the
    /// `Iterator` blanket only through `Iterator for Box2<J>`,
    /// which needs `[u8]: Iterator`, and that has no candidate at
    /// all. One level of filter is not enough.
    #[test]
    fn clause_filter_is_multi_level() {
        let mut g = GlobalTys::new();
        let (iter_tr, into_tr, box2) = (def(10), def(11), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![]);
        declare_trait(&mut index, into_tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // impl<J: Iter> Iter for Box2<J>
        let box_p = g.mk_adt(box2, &[GenericArg::Ty(p0)]);
        let jp = trait_pred(&mut g, iter_tr, &[p0]);
        add_impl(&mut g, &mut index, 100, iter_tr, box_p, &[], 1, vec![jp], vec![]);
        // impl<T> Into for Box2<[T]> (the direct impl)
        let slice_p = g.intern(TyKind::Slice(p0));
        let box_slice = g.mk_adt(box2, &[GenericArg::Ty(slice_p)]);
        let direct = add_impl(&mut g, &mut index, 101, into_tr, box_slice, &[], 1, vec![], vec![]);
        // impl<I: Iter> Into for I (the blanket)
        let ip = trait_pred(&mut g, iter_tr, &[p0]);
        add_impl(&mut g, &mut index, 102, into_tr, p0, &[], 1, vec![ip], vec![]);

        let mut cx = PureCx::new(&g);
        let slice_u8 = cx.tys.intern(TyKind::Slice(u8_ty()));
        let self_ty = cx.tys.mk_adt(box2, &[GenericArg::Ty(slice_u8)]);
        // One level down: `Box2<[u8]>: Iter` is provably false.
        let iter_obl = trait_ref(&mut cx.tys, iter_tr, &[self_ty]);
        assert!(Solver::new().provably_false(&mut cx, &index, &[], iter_obl));
        let obl = trait_ref(&mut cx.tys, into_tr, &[self_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, args, .. } => {
                assert_eq!(id, direct);
                assert_eq!(args[0].as_ty(), Some(u8_ty()));
            }
            other => panic!("expected the direct impl, got {other:?}"),
        }
    }

    /// Steps 1 and 6: param-env evidence wins, and two predicates
    /// that both match an open obligation defer (E0283 parity),
    /// while a concrete input picks one.
    #[test]
    fn param_env_wins_and_two_matches_defer() {
        let mut g = GlobalTys::new();
        let from_tr = def(10);
        let mut index = ImplIndex::new();
        declare_trait(&mut index, from_tr, 1, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // The env of `fn f<T: From<u8> + From<u16>>()`, with T still
        // the abstract parameter type.
        let env = [trait_pred(&mut g, from_tr, &[p0, u8_ty()]), trait_pred(&mut g, from_tr, &[p0, u16_ty()])];

        // `T: From<?X>` matches both: ambiguous, and ?X stays free.
        let mut cx = PureCx::new(&g);
        let x = cx.fresh_var();
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, x]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::Ambiguous);
        let rx = cx.deep_resolve(x);
        assert!(matches!(cx.tys.kind(rx), TyKind::Infer(_)), "an ambiguous selection binds nothing");

        // `T: From<u8>` matches one and commits.
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, u8_ty()]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::ParamEvidence(0));

        // A bare parameter Self is rigid: with no env match and no
        // blanket impl, nothing can prove it (the template check is
        // authoritative, ARCH 4.1; rustc reports E0277 there).
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, BOOL]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::NoImpl);
    }

    /// Step 3 binds inference: one `FromIter` candidate fixes the
    /// element type of a `Bag<_>` target (the `Vec<_>` collect
    /// shape), and one `Index` candidate fixes an integer variable
    /// to `usize` (the `s[x]` shape).
    #[test]
    fn one_candidate_binds_inference_vars() {
        let mut g = GlobalTys::new();
        let (from_iter, index_tr, bag, arr_like) = (def(10), def(11), def(20), def(21));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, from_iter, 1, vec![], vec![]);
        declare_trait(&mut index, index_tr, 1, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // impl<A> FromIter<A> for Bag<A>
        let bag_p = g.mk_adt(bag, &[GenericArg::Ty(p0)]);
        add_impl(&mut g, &mut index, 100, from_iter, bag_p, &[p0], 1, vec![], vec![]);
        // impl Index<usize> for ArrLike
        let arr_ty = g.mk_adt(arr_like, &[]);
        add_impl(&mut g, &mut index, 101, index_tr, arr_ty, &[USIZE], 0, vec![], vec![]);

        let mut cx = PureCx::new(&g);
        let elem = cx.fresh_var();
        let bag_ty = cx.tys.mk_adt(bag, &[GenericArg::Ty(elem)]);
        let obl = trait_ref(&mut cx.tys, from_iter, &[bag_ty, u8_ty()]);
        assert!(matches!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Impl { .. }));
        assert_eq!(cx.deep_resolve(elem), u8_ty(), "the element type is fixed by the one candidate");

        let mut cx = PureCx::new(&g);
        let x = cx.fresh_int_var();
        let obl = trait_ref(&mut cx.tys, index_tr, &[arr_ty, x]);
        assert!(matches!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Impl { .. }));
        assert_eq!(cx.deep_resolve(x), USIZE, "the integer variable is fixed to usize");
    }

    /// Section 2.5: an associated equality on a supertrait bound
    /// reaches normalization through elaboration, and a concrete
    /// impl's binding normalizes at mono time.
    #[test]
    fn assoc_eq_normalizes_through_supertrait_and_impl() {
        let mut g = GlobalTys::new();
        let (iter_tr, byte_tr, item, count) = (def(10), def(11), def(30), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![item]);
        // trait ByteIter: Iter<Item = u8> -- the supertrait pred
        // over ByteIter's own Self (Param 0), with the binding.
        let p0 = ty_param(&mut g, 0);
        let super_args = g.intern_args(&[GenericArg::Ty(p0)]);
        let super_bindings = g.intern_bindings(&[(item, GenericArg::Ty(u8_ty()))]);
        let super_pred = Predicate::Trait(Binder::plain(TraitRef { def: iter_tr, args: super_args, bindings: super_bindings }));
        declare_trait(&mut index, byte_tr, 0, vec![super_pred], vec![]);
        let count_ty = g.mk_adt(count, &[]);
        add_impl(&mut g, &mut index, 100, iter_tr, count_ty, &[], 0, vec![], vec![(item, u8_ty())]);
        add_impl(&mut g, &mut index, 101, byte_tr, count_ty, &[], 0, vec![], vec![]);

        // Inside `fn sum<I: ByteIter>(..)`: <I as Iter>::Item is u8.
        let mut cx = PureCx::new(&g);
        let byte_pred = trait_pred(&mut cx.tys, byte_tr, &[p0]);
        let env = elaborate_in(&mut cx.tys, &index, &[byte_pred]);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(p0)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &env, proj), u8_ty());

        // At mono time with Count: the impl binding rewrites it.
        let mut cx = PureCx::new(&g);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(count_ty)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &[], proj), u8_ty());

        // With no evidence at all the projection stays a projection.
        let other = g.mk_adt(def(77), &[]);
        let mut cx = PureCx::new(&g);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(other)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &[], proj), proj);
    }

    /// Step 4b: `impl<T, U> Tr for T where T: A<Item = U>` binds U
    /// from the equality once `<u8 as A>::Item` normalizes. With a
    /// Self that has no `A` impl the parameter stays unbound (the
    /// impl-parameter case), never guessed.
    #[test]
    fn step4_binds_impl_param_from_assoc_eq() {
        let mut g = GlobalTys::new();
        let (a_tr, tr, item, no_a) = (def(10), def(11), def(30), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, a_tr, 0, vec![], vec![item]);
        declare_trait(&mut index, tr, 0, vec![], vec![]);
        // impl A for u8 { type Item = u16 }
        add_impl(&mut g, &mut index, 100, a_tr, u8_ty(), &[], 0, vec![], vec![(item, u16_ty())]);
        // impl<T, U> Tr for T where T: A<Item = U>
        let (p0, p1) = (ty_param(&mut g, 0), ty_param(&mut g, 1));
        let clause_args = g.intern_args(&[GenericArg::Ty(p0)]);
        let clause_bindings = g.intern_bindings(&[(item, GenericArg::Ty(p1))]);
        let clause = Predicate::Trait(Binder::plain(TraitRef { def: a_tr, args: clause_args, bindings: clause_bindings }));
        add_impl(&mut g, &mut index, 101, tr, p0, &[], 2, vec![clause], vec![]);

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[u8_ty()]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { args, unbound, .. } => {
                assert_eq!(args[0].as_ty(), Some(u8_ty()));
                assert_eq!(args[1].as_ty(), Some(u16_ty()), "U is bound from the associated equality");
                assert!(unbound.is_empty());
            }
            other => panic!("expected an impl selection, got {other:?}"),
        }

        let no_a_ty = g.mk_adt(no_a, &[]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[no_a_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { args, unbound, .. } => {
                assert_eq!(unbound, [ParamId(1)], "the impl-parameter split: it stays unbound, args {args:?}")
            }
            other => panic!("expected an impl selection with an unbound param, got {other:?}"),
        }
    }

    /// A clause cycle is unknown, never false, and never loops:
    /// `Tr` needs `A`, `A` needs `Tr`, both by blanket.
    #[test]
    fn provably_false_cycle_is_unknown() {
        let mut g = GlobalTys::new();
        let (a_tr, tr, s) = (def(10), def(11), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, a_tr, 0, vec![], vec![]);
        declare_trait(&mut index, tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        let need_a = trait_pred(&mut g, a_tr, &[p0]);
        let need_tr = trait_pred(&mut g, tr, &[p0]);
        add_impl(&mut g, &mut index, 100, tr, p0, &[], 1, vec![need_a], vec![]);
        add_impl(&mut g, &mut index, 101, a_tr, p0, &[], 1, vec![need_tr], vec![]);
        let s_ty = g.mk_adt(s, &[]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty]);
        assert!(!Solver::new().provably_false(&mut cx, &index, &[], obl));
    }
}
