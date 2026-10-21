// Closures in body checking (docs/ARCH.md 2.9 and 2.12).
//
// A closure body checks inline in its parent fn, so inference is
// shared with the parent, as in rustc. Right after the body, capture
// analysis follows the Rust 2021 precise-capture rules (rustc's
// `upvar.rs` over an `ExprUseVisitor` walk) and fixes the closure's
// kind (Fn, FnMut, or FnOnce) and its type `Closure(def, args)`,
// where args are the capture types in capture order: the closure
// value is exactly a tuple of its captures (ARCH 4.5).
//
// Rule zero first: every expression or pattern form the walk does not
// model rejects the closure (L0820) when it touches a captured
// variable. A wrong capture mode would change drop order or moves
// without any error, so the walk never guesses.
use super::*;
use crate::ir::Proj;

/// Which Fn trait a closure implements at most (its kind), or which
/// trait a call goes through. Ordered: a later kind is weaker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

/// How a closure captures one place. Ordered by rustc's merge
/// priority: when two uses meet, the later variant wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CaptureMode {
    /// A shared borrow: the env field is `&T`.
    Ref,
    /// A unique borrow of a place reached through `&mut` (rustc's
    /// unique immutable borrow): the env field is `&mut T`.
    UniqueRef,
    /// A mutable borrow: the env field is `&mut T`.
    MutRef,
    /// By value (moved or copied in): the env field is `T`.
    Value,
}

/// One captured place: a checker local plus IR projections (`Field`,
/// `Deref`, `Downcast`) below it, the capture mode, and the type of
/// the place itself (the env field type follows from the mode).
#[derive(Clone, Debug)]
pub struct Capture {
    pub root: u32,
    pub projs: Vec<Proj>,
    pub mode: CaptureMode,
    pub place_ty: Ty,
}

/// The checker's record of one closure expression. Lowering builds the
/// closure value and its body fn from it; mono registers it.
#[derive(Clone, Debug)]
pub struct ClosureInfo {
    pub def: DefId,
    pub expr: ExprId,
    pub kind: ClosureKind,
    pub inputs: Vec<Ty>,
    pub output: Ty,
    pub captures: Vec<Capture>,
    /// The closure's own type, `Closure(def, env field types)`.
    pub ty: Ty,
    /// W-BORROW: `Some` when an iterator method or a bound over a type
    /// param takes this closure, or it has no expected signature, so its
    /// argument regions are free (the items', the param's, inferred), not
    /// higher-ranked; per argument, true when it is `&item` (that outer
    /// reference is higher-ranked). `None`: every argument region is
    /// higher-ranked.
    pub free_args: Option<Vec<bool>>,
    /// W-THREADS: the closure is `thread::scope`'s argument, so its
    /// captured regions outlive its `Scope`'s `'scope` (rustc's implied
    /// `'env: 'scope`).
    pub scope_body: bool,
    /// W-BORROW: per argument, its annotation's regioned type when it
    /// names a lifetime (`|x: &'a T|`: the enclosing fn's `'a`, a free
    /// region the creator ties to that universal), or for any annotation
    /// of a closure with no expected signature (its elided lifetimes are
    /// `Region::Bound`: higher-ranked).
    pub input_regions: Vec<Option<Ty>>,
    /// W-BORROW: the return annotation's regioned type when it names a
    /// lifetime (only `'static` is supported there).
    pub output_region: Option<Ty>,
    /// W-BORROW: the output of the regioned `Fn` bound this closure is
    /// passed to, when it is higher-ranked over the bound's one elided
    /// input lifetime (`F: Fn(&T) -> &U`; rustc gives the closure `for<'r>
    /// fn(&'r T) -> &'r U`): the body may return borrows of that argument.
    pub bound_output: Option<Ty>,
    /// W-BORROW: the regioned inputs of the `Fn` bound this closure is
    /// passed to (empty when there is none): a slot the bound makes
    /// `'static` (`impl FnOnce(&RefCell<Vec<Box<dyn Fn()>>>)`) is
    /// `'static` in the body, not higher-ranked.
    pub bound_inputs: Vec<Ty>,
    /// W-BORROW: passed for a callee's `F: Fn*(..) -> O` bound whose `O`
    /// holds a callee type param (`Option::map`'s `-> U`): the output's
    /// regions are the call's to pick, so what the body needs of them
    /// (`'static`, an argument's region) is the creator's to prove
    /// (`closure_requirements`), not an error in the body.
    pub call_out: bool,
    /// W-BORROW: checked with no expected signature (a `let` closure), or
    /// for a bound whose output is a callee type param (`call_out`) and
    /// not its input's (`bound_output` None): each
    /// region of its output is one free inferred region, never an
    /// argument's, so it cannot meet `F: Fn(&T) -> &U` or `dyn Fn(&T) ->
    /// &U`, whose output is the input's (rustc E0308).
    pub free_sig: bool,
}

/// The env field type of one capture.
pub fn capture_field_ty(tys: &mut impl TyIntern, c: &Capture) -> Ty {
    match c.mode {
        CaptureMode::Value => c.place_ty,
        CaptureMode::Ref => tys.mk_ref(false, c.place_ty),
        CaptureMode::UniqueRef | CaptureMode::MutRef => tys.mk_ref(true, c.place_ty),
    }
}

/// One projection of a capture place while the analysis runs. `Index`
/// stands for any index or subslice step; analysis always truncates
/// before it (arrays are captured whole).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CProj {
    Deref,
    Field(u32),
    Downcast(u32),
    Index,
}

/// A place rooted at a checker local, with the type before each
/// projection (rustc's `ty_before_projection`) and the final type.
#[derive(Clone, Debug)]
struct CPlace {
    root: u32,
    projs: Vec<(CProj, Ty)>,
    ty: Ty,
}

impl CPlace {
    fn push(&mut self, pr: CProj, after: Ty) {
        let before = self.ty;
        self.projs.push((pr, before));
        self.ty = after;
    }
}

/// What an expression is, for capture purposes.
enum Cat {
    Place(CPlace),
    /// A value that is not a place: its uses capture nothing by themselves.
    Rvalue,
    /// A place form the analysis does not model (raw pointers,
    /// overloaded derefs): reject when it reaches a captured variable.
    Bad,
}

/// The state of one capture walk.
struct CapWalk {
    first_local: u32,
    uses: Vec<(CPlace, CaptureMode)>,
    /// Roots read only through `let _ =` style fake reads.
    fake_reads: Vec<u32>,
    bad: Option<Span>,
}

impl CapWalk {
    fn upvar(&self, root: u32) -> bool {
        root < self.first_local
    }
}

impl<'p> Ctx<'p> {
    /// The stable def of one closure expression in this body: the
    /// parent's def hash plus the closure's ordinal in token order
    /// (ARCH 1.7). Instances and abstract instances have their own
    /// parent defs, so their closures get their own types.
    fn closure_def(&mut self, e: ExprId) -> DefId {
        if self.closure_order.is_none() {
            let (lo, hi) = self.f.def(&self.p.ast).exprs;
            let mut order: Vec<ExprId> = (lo..hi).map(ExprId).filter(|&x| matches!(self.p.ast.expr(x), Expr::Closure { .. })).collect();
            order.sort_by_key(|&x| (self.p.ast.expr_span(x).lo, x.0));
            self.closure_order = Some(order);
        }
        let ordinal = self.closure_order.as_ref().unwrap().iter().position(|&x| x == e).unwrap_or(usize::MAX) as u32;
        let parent = self.p.def_id(self.fid);
        DefId { krate: parent.krate, hash: crate::def::child_hash(parent.hash, crate::def::DefKind::Closure, "{closure}", ordinal) }
    }

    /// The expected closure signature from the expected type (ARCH
    /// 2.9): a variable with a pending `Fn`-family obligation gives
    /// the input tuple, and a pending `Output` equality the return.
    fn expected_closure_sig(&mut self, expected: Option<Ty>) -> Option<(Ty, Option<Ty>)> {
        let want = self.resolve(expected?);
        let TyKind::Infer(v) = self.kind(want) else { return None };
        let lang = self.p.gx.lang;
        let out_def = lang.output_of(lang.fn_once)?;
        let mut inputs: Option<Ty> = None;
        let mut output: Option<Ty> = None;
        for ob in self.obl.pending().to_vec() {
            match ob {
                obligations::Obligation::Trait { trait_ref, .. } if lang.is_fn_family(trait_ref.def) => {
                    let args: Vec<GenericArg> = self.tys.args(trait_ref.args).to_vec();
                    let self_ty = args.first().and_then(|g| g.as_ty()).map(|t| self.resolve(t));
                    if self_ty.is_some_and(|s| matches!(self.kind(s), TyKind::Infer(w) if w == v)) && inputs.is_none() {
                        inputs = args.get(1).and_then(|g| g.as_ty());
                    }
                }
                obligations::Obligation::AssocEq { eq, .. } if eq.assoc == out_def => {
                    let self_ty = self.tys.args(eq.trait_args).first().and_then(|g| g.as_ty()).map(|t| self.resolve(t));
                    if self_ty.is_some_and(|s| matches!(self.kind(s), TyKind::Infer(w) if w == v)) && output.is_none() {
                        output = Some(eq.ty);
                    }
                }
                _ => {}
            }
        }
        inputs.map(|i| (i, output))
    }

    /// The strictest `Fn*` bound pending on a closure's expected type (an
    /// inference var): `Fn` before `FnMut` before `FnOnce`. None when no
    /// such bound names it.
    fn expected_closure_kind(&mut self, expected: Option<Ty>) -> Option<ClosureKind> {
        let want = self.resolve(expected?);
        let TyKind::Infer(v) = self.kind(want) else { return None };
        let lang = self.p.gx.lang;
        let mut kind: Option<ClosureKind> = None;
        for ob in self.obl.pending().to_vec() {
            let obligations::Obligation::Trait { trait_ref, .. } = ob else { continue };
            if !lang.is_fn_family(trait_ref.def) {
                continue;
            }
            let self_ty = self.tys.args(trait_ref.args).first().and_then(|g| g.as_ty()).map(|t| self.resolve(t));
            if !self_ty.is_some_and(|s| matches!(self.kind(s), TyKind::Infer(w) if w == v)) {
                continue;
            }
            let k = if trait_ref.def == lang.fn_ {
                ClosureKind::Fn
            } else if trait_ref.def == lang.fn_mut {
                ClosureKind::FnMut
            } else {
                ClosureKind::FnOnce
            };
            kind = Some(kind.map_or(k, |c| c.min(k)));
        }
        kind
    }

    /// `t` (an annotated closure parameter's type) with each inferred dyn
    /// object lifetime that is `'static` in `x` (the expected signature's
    /// input) made `'static`: rustc equates the annotation with the
    /// expected input, so `|p: Rc<dyn Tr>|` passed as `dyn FnMut(Rc<dyn
    /// Tr>)` takes the sugar's `'static` default. Other regions stay.
    fn static_objects_from(&mut self, t: Ty, x: Ty, depth: u32) -> Ty {
        let x = self.deep(x);
        if depth > crate::check::object::LIFETIME_WALK_LIMIT {
            return t;
        }
        match (self.kind(t), self.kind(x)) {
            (TyKind::Dyn(b, Region::Erased), TyKind::Dyn(_, Region::Static)) => self.tys.intern(TyKind::Dyn(b, Region::Static)),
            (TyKind::Ref(r, m, e), TyKind::Ref(_, _, xe)) => {
                let e2 = self.static_objects_from(e, xe, depth + 1);
                if e2 == e { t } else { self.tys.intern(TyKind::Ref(r, m, e2)) }
            }
            (TyKind::Tuple(ts), TyKind::Tuple(xs)) => {
                let (ts, xs) = (self.tys.tys_of(ts).to_vec(), self.tys.tys_of(xs).to_vec());
                if ts.len() != xs.len() {
                    return t;
                }
                let new: Vec<Ty> = ts.iter().zip(&xs).map(|(&a, &b)| self.static_objects_from(a, b, depth + 1)).collect();
                if new == ts { t } else {
                    let l = self.tys.intern_tys(&new);
                    self.tys.intern(TyKind::Tuple(l))
                }
            }
            (TyKind::Adt(d, a), TyKind::Adt(xd, xa)) if d == xd => {
                let (ga, gx) = (self.tys.args(a).to_vec(), self.tys.args(xa).to_vec());
                if ga.len() != gx.len() {
                    return t;
                }
                let mut changed = false;
                let mut new = Vec::with_capacity(ga.len());
                for (g, h) in ga.into_iter().zip(gx) {
                    match (g, h) {
                        (GenericArg::Ty(a), GenericArg::Ty(b)) => {
                            let n = self.static_objects_from(a, b, depth + 1);
                            changed |= n != a;
                            new.push(GenericArg::Ty(n));
                        }
                        (g, _) => new.push(g),
                    }
                }
                if !changed {
                    return t;
                }
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            _ => t,
        }
    }

    /// True when `t` has a `'static` reference region (kept only inside fn
    /// pointer types and `dyn Fn*` sugar, `Scope::static_refs`).
    fn has_static_region(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        let mut rs = Vec::new();
        crate::borrowck::regions_of(&self.tys, t, &mut rs);
        rs.contains(&Region::Static)
    }

    /// `t` with each late-bound region (`DYN_LATE`) `Region::Bound(0)`,
    /// Adt lifetime args included: the written output of a `dyn Fn`
    /// signature (`dyn_fn_written_out`), whose elided regions are the one
    /// input region's (`ClosureInfo::bound_output`). A written `'static`
    /// stays; a named lifetime (erased) is `Bound(1)`: the body may return
    /// an argument there as before, but it is no higher-ranked slot
    /// (`bound_hr_out_slots`). An Adt without lifetime args (erased)
    /// gets `Bound(0)` for each.
    fn rebind_bound(&mut self, t: Ty) -> Ty {
        let b = |r: Region| match r {
            crate::ty::DYN_LATE => Region::Bound(0),
            Region::Static => r,
            _ => Region::Bound(1),
        };
        match self.kind(t) {
            TyKind::Ref(r, m, e) => {
                let e = self.rebind_bound(e);
                self.tys.intern(TyKind::Ref(b(r), m, e))
            }
            TyKind::Tuple(ts) => {
                let es: Vec<Ty> = self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.rebind_bound(e)).collect();
                let ts = self.tys.intern_tys(&es);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Slice(e) => {
                let e = self.rebind_bound(e);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rebind_bound(e);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Adt(d, args) => {
                let n = self.p.gx.adt_lifetimes.get(&d).map_or(0, |v| v.len());
                let old = self.tys.args(args).to_vec();
                let lts: Vec<Region> = old.iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                let mut new: Vec<GenericArg> = (0..n).map(|i| GenericArg::Lifetime(b(lts.get(i).copied().unwrap_or(crate::ty::DYN_LATE)))).collect();
                for g in old {
                    match g {
                        GenericArg::Ty(e) => new.push(GenericArg::Ty(self.rebind_bound(e))),
                        GenericArg::Lifetime(_) => {}
                        c => new.push(c),
                    }
                }
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            _ => t,
        }
    }

    /// `t` with each `DYN_LATE` region `Erased`, Adt lifetime args kept
    /// (`ty::unbind` drops them): a dyn's written output as a closure's
    /// `output_region`, its `'static` slots pinned and the others free.
    fn late_erased(&mut self, t: Ty) -> Ty {
        let t = self.deep(t);
        let late = |r: Region| if r == crate::ty::DYN_LATE { Region::Erased } else { r };
        match self.kind(t) {
            TyKind::Ref(r, m, e) => {
                let e = self.late_erased(e);
                self.tys.intern(TyKind::Ref(late(r), m, e))
            }
            TyKind::Tuple(ts) => {
                let es: Vec<Ty> = self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.late_erased(e)).collect();
                let ts = self.tys.intern_tys(&es);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Slice(e) => {
                let e = self.late_erased(e);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.late_erased(e);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Adt(d, args) => {
                let new: Vec<GenericArg> = self
                    .tys
                    .args(args)
                    .to_vec()
                    .into_iter()
                    .map(|g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.late_erased(e)),
                        GenericArg::Lifetime(r) => GenericArg::Lifetime(late(r)),
                        c => c,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            _ => crate::ty::unbind(&mut self.tys, t),
        }
    }

    /// How the closure output `o` (before `deep`) holds a variable that
    /// only the outer call's expected type fixed (`expect_only_vars`):
    /// `Some(true)` when each such variable is the call's whole result
    /// (`fn ap<U>(f: impl FnOnce() -> U) -> U`), `Some(false)` when one
    /// sits inside it (`Option<U>`), None for neither.
    fn expect_only_output(&self, o: Ty) -> Option<bool> {
        if self.expect_only_vars.is_empty() || !self.tys.flags(o).contains_infer() {
            return None;
        }
        let mut vs = Vec::new();
        self.chain_vars(o, &mut vs);
        let hits: Vec<bool> = self.expect_only_vars.iter().filter(|(v, _)| vs.contains(v)).map(|&(_, whole)| whole).collect();
        (!hits.is_empty()).then(|| hits.iter().all(|&w| w))
    }

    /// Every variable on the binding chains inside `t`, bound ones too.
    fn chain_vars(&self, t: Ty, out: &mut Vec<u32>) {
        if !self.tys.flags(t).contains_infer() {
            return;
        }
        match self.tys.kind(t) {
            TyKind::Infer(v) => {
                out.push(v.index());
                if let Some(b) = self.vars[v.index() as usize].bound {
                    self.chain_vars(b, out);
                }
            }
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.chain_vars(e, out),
            TyKind::Tuple(ts) => {
                for &e in self.tys.tys_of(ts) {
                    self.chain_vars(e, out);
                }
            }
            TyKind::Adt(_, a) | TyKind::Projection(_, a) => {
                for g in self.tys.args(a) {
                    if let Some(e) = g.as_ty() {
                        self.chain_vars(e, out);
                    }
                }
            }
            _ => {}
        }
    }

    /// True when a value could coerce to `t` from another type: `t`
    /// holds a reference, raw or fn pointer, dyn, or smart pointer.
    fn coerce_target(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        match self.kind(t) {
            TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::FnPtr(_) | TyKind::Dyn(..) => true,
            TyKind::Slice(e) | TyKind::Array(e, _) => self.coerce_target(e),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).to_vec().into_iter().any(|e| self.coerce_target(e)),
            TyKind::Adt(_, a) => {
                self.tys.boxed_elem(t).is_some()
                    || self.tys.rc_elem(t).is_some()
                    || self.tys.args(a).to_vec().into_iter().any(|g| g.as_ty().is_some_and(|e| self.coerce_target(e)))
            }
            _ => false,
        }
    }

    /// The signature of the body's return-position `impl Fn*(..) -> R`
    /// (`OpaqueInfo::fn_outs`) for a closure with `n` params that is the
    /// body's result (`ret_exprs`), checked against that opaque's hidden
    /// type: the erased input tuple, `R` with
    /// regions (`ClosureInfo::bound_output`: only the output slots that are
    /// the one higher-ranked input region may hold the argument's borrow;
    /// `'static` ones are pinned, `output_region`), and `R` erased. None
    /// when the inputs have several higher-ranked regions and the output
    /// one. A named lifetime in `R` is L0203.
    fn rpit_bound(&mut self, expected: Option<Ty>, n: usize, span: Span) -> Option<(Ty, Ty, Ty)> {
        let TyKind::Infer(v) = self.kind(self.resolve(expected?)) else { return None };
        let &(od, args, h) = self.own_opaques.iter().find(|&&(_, _, h)| matches!(self.kind(self.resolve(h)), TyKind::Infer(w) if w == v))?;
        let p = self.p;
        let b = p.gx.opaques.get(&od)?.fn_outs.iter().find(|b| b.inputs.len() == n)?.clone();
        let out = b.output.unwrap_or(UNIT);
        let mut ins = Vec::new();
        for &t in &b.inputs {
            crate::borrowck::regions_of(&p.tys, t, &mut ins);
        }
        let mut outs = Vec::new();
        crate::borrowck::regions_of(&p.tys, out, &mut outs);
        if outs.iter().any(|r| matches!(r, Region::Param(_))) {
            self.err(
                "L0203",
                span,
                "a named lifetime in the output of a returned `impl Fn*` closure type is not supported yet",
                "Elide the lifetime, write `'static`, or return a `Box<dyn Fn..>`.",
            );
            return None;
        }
        if !(matches!(ins[..], [Region::Bound(_)]) || !outs.iter().any(|r| matches!(r, Region::Bound(_)))) {
            return None;
        }
        let mut full: Vec<GenericArg> = self.tys.args(args).to_vec();
        full.push(GenericArg::Ty(h));
        let mut es = Vec::new();
        for t in b.inputs {
            let t = crate::ty::subst(&mut self.tys, t, &full);
            es.push(crate::borrowck::erase(&mut self.tys, t));
        }
        let ts = self.tys.intern_tys(&es);
        let tuple = self.tys.intern(TyKind::Tuple(ts));
        let out = crate::ty::subst(&mut self.tys, out, &full);
        let erased = crate::borrowck::erase(&mut self.tys, out);
        Some((tuple, out, erased))
    }

    /// `t` with each `Region::Bound` `Erased` (an `output_region` from a
    /// regioned bound output, `rpit_bound_output`).
    fn bound_erased(&mut self, t: Ty) -> Ty {
        let e = |r: Region| if matches!(r, Region::Bound(_)) { Region::Erased } else { r };
        match self.kind(t) {
            TyKind::Ref(r, m, x) => {
                let x = self.bound_erased(x);
                self.tys.intern(TyKind::Ref(e(r), m, x))
            }
            TyKind::Tuple(ts) => {
                let es: Vec<Ty> = self.tys.tys_of(ts).to_vec().into_iter().map(|x| self.bound_erased(x)).collect();
                let ts = self.tys.intern_tys(&es);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Slice(x) => {
                let x = self.bound_erased(x);
                self.tys.intern(TyKind::Slice(x))
            }
            TyKind::Array(x, n) => {
                let x = self.bound_erased(x);
                self.tys.intern(TyKind::Array(x, n))
            }
            TyKind::Adt(d, args) => {
                let new: Vec<GenericArg> = self
                    .tys
                    .args(args)
                    .to_vec()
                    .into_iter()
                    .map(|g| match g {
                        GenericArg::Ty(x) => GenericArg::Ty(self.bound_erased(x)),
                        GenericArg::Lifetime(r) => GenericArg::Lifetime(e(r)),
                        c => c,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            _ => t,
        }
    }

    /// The output of fn pointer type `t` with each region slot of
    /// `FnSig::own_out` the one input region's (`ClosureInfo::bound_output`),
    /// when it has exactly one higher-ranked input slot (`for<'a> fn(&'a D)
    /// -> Option<L<'a>>`, or the elided form). None when no output slot is
    /// the input's, or when the output's slots no longer line up with the
    /// written ones (a type parameter substituted with `&'x u8` in `fn(&u8)
    /// -> T`): a closure body must not return its argument there. An infer
    /// var has no slot yet; what it later resolves to keeps erased regions
    /// (not the input's), so the rebound slots stay the written ones.
    fn fn_ptr_bound_output(&mut self, t: Ty) -> Option<Ty> {
        let TyKind::FnPtr(sig) = self.kind(t) else { return None };
        let s = self.tys.sig(sig).value;
        if s.own_out == 0 || s.free_slots != 0 {
            return None;
        }
        let out = self.deep(s.output);
        if self.tys.flags(out).contains_projection() {
            return None;
        }
        let al = &self.p.gx.adt_lifetimes;
        let mut ins = Vec::new();
        for &i in self.tys.tys_of(s.inputs) {
            crate::borrowck::paired_slot_regions(al, &self.tys, i, i, &mut ins);
        }
        let mut outs = Vec::new();
        crate::borrowck::paired_slot_regions(al, &self.tys, out, out, &mut outs);
        let hr = ins.iter().filter(|r| **r != Region::Static).count();
        (hr == 1 && outs.len() == s.out_slots as usize).then(|| self.rebind_own(out, s.own_out, &mut 0))
    }

    /// `t` with region slot `k` (counted from `*k`, in
    /// `paired_slot_regions` order) `Region::Bound(0)` when bit `k` of
    /// `mask` is set (`fn_ptr_bound_output`). Slots inside `dyn`, raw
    /// pointer and fn pointer types, and std types with regions of their
    /// own (`Chars`, slice iterators), are counted, never rebound.
    fn rebind_own(&mut self, t: Ty, mask: u32, k: &mut usize) -> Ty {
        let own = |k: usize| k < 32 && mask >> k & 1 == 1;
        let b = Region::Bound(0);
        match self.kind(t) {
            TyKind::Ref(r, m, e) => {
                let r = if own(*k) { b } else { r };
                *k += 1;
                let e = self.rebind_own(e, mask, k);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::Tuple(ts) => {
                let mut es = Vec::new();
                for e in self.tys.tys_of(ts).to_vec() {
                    es.push(self.rebind_own(e, mask, k));
                }
                let ts = self.tys.intern_tys(&es);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Slice(e) => {
                let e = self.rebind_own(e, mask, k);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rebind_own(e, mask, k);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Adt(d, args)
                if crate::borrowck::adt_region_count(&self.p.gx.adt_lifetimes, &self.tys, t) as usize
                    == self.p.gx.adt_lifetimes.get(&d).map_or(0, |v| v.len()) =>
            {
                let n = self.p.gx.adt_lifetimes.get(&d).map_or(0, |v| v.len());
                let old: Vec<GenericArg> = self.tys.args(args).to_vec();
                let lts: Vec<Region> = old.iter().filter_map(|g| if let GenericArg::Lifetime(x) = g { Some(*x) } else { None }).collect();
                let mut new: Vec<GenericArg> = Vec::new();
                for i in 0..n {
                    new.push(GenericArg::Lifetime(if own(*k + i) { b } else { lts.get(i).copied().unwrap_or(Region::Erased) }));
                }
                *k += n;
                for g in old {
                    match g {
                        GenericArg::Ty(e) => new.push(GenericArg::Ty(self.rebind_own(e, mask, k))),
                        GenericArg::Lifetime(_) => {}
                        c => new.push(c),
                    }
                }
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            _ => {
                let mut rs = Vec::new();
                crate::borrowck::paired_slot_regions(&self.p.gx.adt_lifetimes, &self.tys, t, t, &mut rs);
                *k += rs.len();
                t
            }
        }
    }

    /// The parts of a `dyn Fn(A, B) -> R` type (any of the Fn family):
    /// the trait, the input tuple `(A, B)`, and `R`, with the object's
    /// late-bound regions made plain (`ty::unbind`). None for another
    /// type.
    pub(super) fn dyn_fn_parts(&mut self, t: Ty) -> Option<(DefId, Ty, Ty)> {
        let (def, tuple, out) = self.dyn_fn_written(t)?;
        let (tuple, out) = (crate::ty::unbind(&mut self.tys, tuple), crate::ty::unbind(&mut self.tys, out));
        Some((def, tuple, out))
    }

    /// `dyn_fn_parts` before `ty::unbind`: the object's late-bound regions
    /// are `DYN_LATE`, and an Adt keeps its lifetime args, a written
    /// `'static` among them (R11), which `unbind` drops.
    fn dyn_fn_written(&mut self, t: Ty) -> Option<(DefId, Ty, Ty)> {
        let lang = self.p.gx.lang;
        let pr = crate::check::object::principal_of(&self.tys, self.resolve(t))?;
        if !lang.is_fn_family(pr.def) {
            return None;
        }
        let tuple = self.tys.args(pr.args).get(1).and_then(|g| g.as_ty())?;
        let out_def = lang.output_of(lang.fn_once)?;
        let out = self.tys.bindings(pr.bindings).iter().find(|(d, _)| *d == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
        Some((pr.def, tuple, out))
    }

    /// Checks one closure expression: parameters, body, capture
    /// analysis, kind, and the closure type.
    pub(super) fn closure_expr(
        &mut self,
        e: ExprId,
        is_move: bool,
        params: &[ast::ClosureParam],
        ret: Option<ast::TyId>,
        body: ExprId,
        expected: Option<Ty>,
    ) -> Ty {
        let span = self.span(e);
        // A closure checked against a fn pointer type takes the pointer's
        // signature and, capturing nothing, becomes a value of that type
        // (lowering materializes its body fn's trampoline).
        let mut to_fn_ptr: Option<(Ty, Ty, Ty)> = None;
        let mut dyn_sig: Option<(Ty, Option<Ty>)> = None;
        let mut dyn_out: Option<Ty> = None;
        let mut dyn_written_out: Option<Ty> = None;
        if let Some(t) = expected {
            let t = self.resolve(t);
            match self.kind(t) {
                TyKind::FnPtr(sig) => {
                    let s = self.tys.sig(sig).value;
                    if s.is_unsafe || s.extern_c {
                        self.err(
                            "L0820",
                            span,
                            "coercing a closure to an unsafe or extern fn pointer is not supported yet",
                            "Use a safe `fn(..)` type.",
                        );
                        return ERROR;
                    }
                    let ins: Vec<Ty> = self.tys.tys_of(s.inputs).to_vec();
                    let ts = self.tys.intern_tys(&ins);
                    let tuple = self.tys.intern(TyKind::Tuple(ts));
                    to_fn_ptr = Some((t, tuple, s.output));
                }
                // `dyn Fn(A) -> R` (behind `&` or a smart pointer) gives
                // the signature; the unsizing coercion checks the kind.
                TyKind::Dyn(..) => {
                    if let Some((_, tuple, out)) = self.dyn_fn_parts(t) {
                        dyn_sig = Some((tuple, Some(out)));
                        dyn_out = Some(out);
                        dyn_written_out = self.dyn_fn_written(t).map(|w| w.2);
                    }
                }
                _ => {}
            }
        }
        let def = self.closure_def(e);
        let free_args = expected.and_then(|t| match self.kind(self.resolve(t)) {
            TyKind::Infer(v) => self.iter_closure_args.get(&v.0).cloned(),
            _ => None,
        });
        let scope_body = expected.is_some_and(|t| matches!(self.kind(self.resolve(t)), TyKind::Infer(v) if self.scope_closure_vars.contains(&v.0)));
        let bound_output = expected.and_then(|t| match self.kind(self.resolve(t)) {
            TyKind::Infer(v) => self.closure_bound_outputs.get(&v.0).copied(),
            _ => None,
        });
        // W-BORROW: every region of a `dyn Fn` signature is elided, so an
        // output region is the one input region's (Fn sugar elision).
        let bound_inputs = expected
            .and_then(|t| match self.kind(self.resolve(t)) {
                TyKind::Infer(v) => self.closure_bound_inputs.get(&v.0).cloned(),
                _ => None,
            })
            .unwrap_or_default();
        let call_out = expected.is_some_and(|t| matches!(self.kind(self.resolve(t)), TyKind::Infer(v) if self.closure_call_outs.contains(&v.0)));
        let bound_output = bound_output.or_else(|| {
            let o = self.deep(dyn_written_out?);
            Some(self.rebind_bound(o))
        });
        let bound_output = bound_output.or_else(|| self.fn_ptr_bound_output(to_fn_ptr?.0));
        let rpit = if self.ret_exprs.contains(&e) { self.rpit_bound(expected, params.len(), span) } else { None };
        let rpit_out = rpit.map(|r| r.1);
        let bound_output = bound_output.or(rpit_out);
        // The bound's types normalize here: `F: Fn(A::Item)` gives a
        // projection over the call's impl args (check/project.rs).
        let mut expect_only = None;
        let sig = match to_fn_ptr {
            Some((_, tuple, out)) => Some((tuple, Some(out))),
            None => match dyn_sig.or_else(|| self.expected_closure_sig(expected)) {
                Some((ins, out)) => {
                    let ins = self.deep(ins);
                    let ins = self.normalize_use(ins, span);
                    expect_only = out.and_then(|o| self.expect_only_output(o));
                    let out = out.map(|o| {
                        let o = self.deep(o);
                        self.normalize_use(o, span)
                    });
                    Some((ins, out))
                }
                // A closure the body returns as its `impl Fn*(..) -> R`
                // takes the bound's signature, as rustc deduces it.
                None => rpit.map(|r| (r.0, Some(r.2))),
            },
        };
        // W-BORROW: with no expected signature (a `let` closure), rustc
        // infers unannotated parameters' regions as free regions of the
        // enclosing fn, one per slot for every call, while an elided
        // lifetime in an annotation is the closure's own (higher-ranked:
        // `Region::Bound` in `input_regions`).
        let no_sig = sig.is_none();
        if no_sig {
            self.free_sig_closures.push((def, params.iter().map(|prm| prm.ty.is_none()).collect()));
        }
        let free_args = free_args.or_else(|| (no_sig && !params.is_empty()).then(|| vec![false; params.len()]));
        let expected_inputs: Option<Vec<Ty>> = sig.and_then(|(tup, _)| {
            let tup = self.deep(tup);
            match self.kind(tup) {
                TyKind::Tuple(ts) => Some(self.tys.tys_of(ts).to_vec()),
                TyKind::Unit => Some(Vec::new()),
                _ => None,
            }
        });
        if let Some(ins) = &expected_inputs
            && ins.len() != params.len()
        {
            self.err(
                "L0105",
                span,
                format!("this closure takes {} argument(s) but {} are expected", params.len(), ins.len()),
                "Match the closure parameters to the expected Fn signature.",
            );
        }
        let first_local = self.out.locals.len() as u32;
        let scope_len = self.scopes.len();
        let mut inputs: Vec<Ty> = Vec::with_capacity(params.len());
        let mut input_regions: Vec<Option<Ty>> = Vec::with_capacity(params.len());
        for (i, prm) in params.iter().enumerate() {
            let exp = expected_inputs.as_ref().and_then(|v| v.get(i).copied());
            let named = prm.ty.is_some_and(|w| self.annotation_has_regions(w));
            // An unnamed annotation that does not resolve here (`Vec<_>`)
            // counts as unannotated: free, as rustc infers `_`.
            let elided = if no_sig { Region::Bound(0) } else { Region::Erased };
            // W-BORROW: a `&'static` the expected fn pointer or `dyn Fn` type
            // writes (`Scope::static_refs`) is that argument's, as if
            // annotated: free in the body, `'static` from the creator.
            let from_sig = exp.filter(|&x| (dyn_out.is_some() || to_fn_ptr.is_some()) && prm.ty.is_none() && self.has_static_region(x));
            input_regions.push(if named || no_sig { prm.ty.and_then(|w| self.regioned_annotation(w, elided, named)) } else { from_sig });
            let t = match (prm.ty, exp) {
                (Some(w), exp) => {
                    let t = if named { self.resolve_annotation(w) } else { self.resolve_written(w) };
                    // Closure params are values (rustc E0277).
                    self.require_sized(t, self.p.ast.ty_span(w));
                    if let Some(x) = exp
                        && !self.unify(t, x)
                    {
                        self.mismatch(prm.span, x, t);
                    }
                    match exp {
                        Some(x) => self.static_objects_from(t, x, 0),
                        None => t,
                    }
                }
                (None, Some(x)) => x,
                (None, None) => self.new_var(false),
            };
            self.pattern(prm.pat, t, false);
            if !self.pat_always_matches(prm.pat) {
                self.err("L0110", prm.span, "refutable pattern in closure argument", "Use a pattern that matches every value.");
            }
            inputs.push(t);
        }
        // W-BORROW: a return annotation may name `'static` (its slots are
        // `'static` in the body); another named lifetime there is L0203.
        let mut output_region: Option<Ty> = None;
        let output = match (ret, sig.and_then(|s| s.1)) {
            (Some(w), exp) => {
                let named = self.annotation_has_regions(w);
                if named {
                    output_region = self.regioned_annotation(w, Region::Erased, true);
                    let mut rs = Vec::new();
                    if let Some(r) = output_region {
                        crate::borrowck::regions_of(&self.tys, r, &mut rs);
                    }
                    if rs.iter().any(|r| matches!(r, Region::Param(_))) {
                        let s = self.p.ast.ty_span(w);
                        self.err(
                            "L0203",
                            s,
                            "a named lifetime in a closure's return type is not supported yet",
                            "Drop the return annotation, or use `'static`.",
                        );
                    }
                }
                let t = if named { self.resolve_annotation(w) } else { self.resolve_written(w) };
                self.require_sized(t, self.p.ast.ty_span(w));
                if let Some(x) = exp
                    && !self.unify(t, x)
                {
                    self.mismatch(span, x, t);
                }
                t
            }
            (None, Some(x)) => {
                // W-BORROW: a `&'static` the expected fn pointer or `dyn Fn`
                // output writes pins that slot, as a `'static` return
                // annotation does.
                // A written `'static` lifetime arg of an Adt (`W<'static,
                // &u8>`) is only in the dyn's written output.
                if let Some(o) = rpit_out.filter(|&o| self.has_static_region(o)) {
                    output_region = Some(self.bound_erased(o));
                } else if let Some(w) = dyn_written_out.filter(|&w| self.has_static_region(w)) {
                    output_region = Some(self.late_erased(w));
                } else if (dyn_out.is_some() || to_fn_ptr.is_some()) && self.has_static_region(x) {
                    output_region = Some(self.deep(x));
                }
                x
            }
            (None, None) => self.new_var(false),
        };
        // The body: a new frame for `return`, and no outer loop labels.
        // An output that only the outer call's expected type fixed, with
        // a type a body could coerce to, is open in the body, as in
        // rustc: the body's type must then be that output exactly
        // (`Some(1).map(|_| &v)` with `v: &Vec<u8>` is no
        // `Option<&Vec<u8>>`, E0308), or coerce to it when it is the
        // call's whole result (rustc coerces the call's result then).
        let ret = if expect_only.is_some() && ret.is_none() && self.coerce_target(output) { self.new_var(false) } else { output };
        let saved_loops = std::mem::take(&mut self.loops);
        let returns_before = self.returns_seen;
        self.closure_rets.push(ret);
        let bt = self.expr(body, (ret == output).then_some(ret));
        // Edition 2024 never-type fallback: a body that only diverges
        // (`|| { ..; panic!(); }`) leaves the return type open, and rustc
        // makes it `!`. Without this the closure's signature zonks to
        // the error type and no body is built for it.
        if matches!(self.kind(self.resolve(bt)), TyKind::Never) && matches!(self.kind(self.resolve(output)), TyKind::Infer(v) if !v.is_int() && !v.is_float()) {
            self.unify(output, NEVER);
        }
        self.coerce_expr(body, bt, ret);
        if ret != output {
            // A `return` in the body coerced to `ret` only, so the
            // result's own coercion is for a body without one.
            if expect_only == Some(true) && self.returns_seen == returns_before {
                let rt = self.resolve(ret);
                self.coerce_expr(body, rt, output);
            } else if !self.unify(ret, output) {
                let span = self.span(body);
                self.mismatch(span, output, ret);
            }
        }
        self.reject_unsized_value(body);
        self.closure_rets.pop();
        self.loops = saved_loops;
        self.scopes.truncate(scope_len);
        // A parameter type the body left open may still be fixed by
        // a later call, as in rustc (`let add = |a, b| a + b;
        // add(2i64, 3)`). Structural uses in the body already needed
        // a known type (ARCH 2.12); what stays open is an error at
        // body end (`finish_closures`).
        let summary = self.template_closure_summary(e);
        let (kind, captures) = match summary {
            Some(s) => s,
            None => self.capture_analysis(e, is_move, body, params, first_local),
        };
        // rustc takes the kind of a closure passed for `Fn*` bounds from
        // the strictest of them: one passed only for `FnOnce` is `FnOnce`,
        // so its body may return a reborrow of a `&mut` capture
        // (`ok.then(|| self.nodes.get_mut(i))`).
        let kind = if self.expected_closure_kind(expected) == Some(ClosureKind::FnOnce) { ClosureKind::FnOnce } else { kind };
        let mut fields: Vec<GenericArg> = Vec::with_capacity(captures.len());
        for c in &captures {
            fields.push(GenericArg::Ty(capture_field_ty(&mut self.tys, c)));
        }
        let ty = self.tys.intern_args(&fields);
        let ty = self.tys.intern(TyKind::Closure(def, ty));
        let captures_any = !captures.is_empty();
        self.closures.push(ClosureInfo { def, expr: e, kind, inputs, output, captures, ty, free_args, scope_body, input_regions, output_region, bound_output, bound_inputs, call_out, free_sig: no_sig || call_out && bound_output.is_none() });
        if let Some((fp, _, _)) = to_fn_ptr {
            if captures_any {
                self.err(
                    "L0110",
                    span,
                    "mismatched types: a closure that captures variables cannot become a fn pointer",
                    "Pass the captured values as arguments, or take a generic `F: Fn(..)` parameter instead.",
                );
                return ERROR;
            }
            return fp;
        }
        ty
    }

    /// For a concrete instance of a template, the capture analysis
    /// the template's abstract check made (places, modes, and kind),
    /// with this instance's types. rustc analyzes captures once, on
    /// the generic body; re-running it per instance could change a
    /// capture where Copy or Drop differ between a parameter and its
    /// concrete type.
    fn template_closure_summary(&mut self, e: ExprId) -> Option<(ClosureKind, Vec<Capture>)> {
        let p = self.p;
        if p.gx.fn_class.get(self.fid.0 as usize) != Some(&generics::FnClass::Instance) {
            return None;
        }
        let template = p.gx.instances.get(&self.fid)?.template_local?;
        let (kind, shapes) = p.gx.template_closures.get(&(template, e))?;
        let mut out = Vec::with_capacity(shapes.len());
        for (root, projs, mode) in shapes {
            let mut t = self.resolve(self.out.locals.get(*root as usize)?.ty);
            let mut variant = 0u32;
            for pr in projs {
                t = self.resolve(t);
                t = match *pr {
                    Proj::Deref => match self.kind(t) {
                        TyKind::Ref(_, _, inner) => inner,
                        _ => self.tys.boxed_elem(t)?,
                    },
                    Proj::Downcast(v) => {
                        variant = v;
                        continue;
                    }
                    Proj::Field(i) => {
                        let ft = self.field_ty_at(t, variant, i)?;
                        variant = 0;
                        ft
                    }
                    Proj::Index(_) => return None,
                };
            }
            out.push(Capture { root: *root, projs: projs.clone(), mode: *mode, place_ty: t });
        }
        Some((*kind, out))
    }

    /// The type of field `i` of variant `variant` of a resolved type.
    fn field_ty_at(&mut self, t: Ty, variant: u32, i: u32) -> Option<Ty> {
        match self.kind(t) {
            TyKind::Tuple(ts) => self.tys.tys_of(ts).get(i as usize).copied(),
            _ => {
                if let Some(e) = self.tys.option_elem(t) {
                    return (variant == 1 && i == 0).then_some(e);
                }
                if let Some((ok, err)) = self.tys.result_args(t) {
                    return match (variant, i) {
                        (0, 0) => Some(ok),
                        (1, 0) => Some(err),
                        _ => None,
                    };
                }
                let a = self.tys.local_adt(t)?;
                self.p.adt(a).variants.get(variant as usize)?.fields.get(i as usize).map(|f| f.ty)
            }
        }
    }

    // ---------- Capture analysis ----------

    /// Runs the Rust 2021 capture analysis over one closure body and
    /// returns the closure kind and its minimal capture list.
    fn capture_analysis(
        &mut self,
        e: ExprId,
        is_move: bool,
        body: ExprId,
        params: &[ast::ClosureParam],
        first_local: u32,
    ) -> (ClosureKind, Vec<Capture>) {
        let mut w = CapWalk { first_local, uses: Vec::new(), fake_reads: Vec::new(), bad: None };
        // Parameters bind from rvalues: nothing in them is captured,
        // but their patterns may name consts or variants only.
        let _ = params;
        self.cap_consume(body, &mut w);
        let span = self.span(e);
        if let Some(bad) = w.bad {
            // An earlier error in the body (an unresolved callee or type)
            // often leaves a capture's type unknown: that error is the cause.
            if !self.errs.iter().any(|d| d.code != "L0820") {
                self.err(
                    "L0820",
                    bad,
                    "this use of a captured variable is not supported in closures yet",
                    "Rewrite the use, or move the value into a local before the closure.",
                );
            }
            return (ClosureKind::FnOnce, Vec::new());
        }
        // process_collected_capture_information: restrict precision,
        // infer the kind, then adjust for `move` and Drop types.
        let mut kind = ClosureKind::Fn;
        let mut processed: Vec<(CPlace, CaptureMode)> = Vec::with_capacity(w.uses.len());
        for (place, mode) in std::mem::take(&mut w.uses) {
            let (place, mode) = restrict_capture_precision(place, mode, &self.tys);
            let (place, mode) = truncate_for_optimization(place, mode, &self.tys);
            kind = kind.max(match mode {
                CaptureMode::Value => ClosureKind::FnOnce,
                CaptureMode::MutRef | CaptureMode::UniqueRef => ClosureKind::FnMut,
                CaptureMode::Ref => ClosureKind::Fn,
            });
            let (mut place, mut mode) = (place, mode);
            let first_deref = place.projs.iter().position(|(pr, _)| *pr == CProj::Deref);
            if is_move {
                if let Some(i) = first_deref {
                    truncate_place(&mut place, &mut mode, i, &self.tys);
                }
                mode = CaptureMode::Value;
            } else if mode == CaptureMode::Value
                && let Some(i) = first_deref
            {
                truncate_place(&mut place, &mut mode, i, &self.tys);
            }
            if mode == CaptureMode::Value && !self.cap_is_copy(place.ty) {
                for i in 0..place.projs.len() {
                    if self.has_drop_impl(place.projs[i].1) {
                        truncate_place(&mut place, &mut mode, i, &self.tys);
                        break;
                    }
                }
            }
            processed.push((place, mode));
        }
        // compute_min_captures: merge ancestors and descendants per
        // root, keeping roots in first-use order.
        let mut roots: Vec<(u32, Vec<(CPlace, CaptureMode)>)> = Vec::new();
        for (mut place, mut mode) in processed {
            let Some(ri) = roots.iter().position(|(r, _)| *r == place.root) else {
                roots.push((place.root, vec![(place, mode)]));
                continue;
            };
            let list = &mut roots[ri].1;
            let mut descendant_found = false;
            let mut j = 0;
            while j < list.len() {
                if is_ancestor(&place, &list[j].0) && place.projs.len() < list[j].0.projs.len() {
                    let (mut d, mut dm) = list.remove(j);
                    truncate_place(&mut d, &mut dm, place.projs.len(), &self.tys);
                    mode = mode.max(dm);
                    descendant_found = true;
                } else {
                    j += 1;
                }
            }
            let mut ancestor_found = false;
            if !descendant_found {
                for (a, am) in list.iter_mut() {
                    if is_ancestor(a, &place) {
                        truncate_place(&mut place, &mut mode, a.projs.len(), &self.tys);
                        *am = (*am).max(mode);
                        ancestor_found = true;
                        break;
                    }
                }
            }
            if !ancestor_found {
                list.push((place, mode));
            }
        }
        // Sort each root's captures by their field projections, as
        // rustc does, so captured fields drop in declaration order.
        for (_, list) in &mut roots {
            list.sort_by(|a, b| {
                let fa = a.0.projs.iter().filter_map(|(p, _)| if let CProj::Field(i) = p { Some(*i) } else { None });
                let fb = b.0.projs.iter().filter_map(|(p, _)| if let CProj::Field(i) = p { Some(*i) } else { None });
                fa.cmp(fb)
            });
        }
        for root in std::mem::take(&mut w.fake_reads) {
            if !roots.iter().any(|(r, _)| *r == root) {
                self.err(
                    "L0820",
                    span,
                    "a closure that reads a captured variable only through `_` is not supported yet",
                    "Use the variable in the closure, or drop the `_` pattern.",
                );
            }
        }
        let mut out: Vec<Capture> = Vec::new();
        for (_, list) in roots {
            for (place, mode) in list {
                let mut projs = Vec::with_capacity(place.projs.len());
                for (pr, _) in &place.projs {
                    projs.push(match *pr {
                        CProj::Deref => Proj::Deref,
                        CProj::Field(i) => Proj::Field(i),
                        CProj::Downcast(v) => Proj::Downcast(v),
                        CProj::Index => unreachable!("index projections are truncated"),
                    });
                }
                out.push(Capture { root: place.root, projs, mode, place_ty: place.ty });
            }
        }
        (kind, out)
    }

    /// Copy, for capture purposes. An unresolved type variable cannot
    /// be decided yet; the walk records it as unsupported first.
    fn cap_is_copy(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        is_copy(self.p, &self.tys, t)
    }

    /// True for a user Adt with a `Drop` impl (rustc
    /// `restrict_precision_for_drop_types`: no field is moved out of it).
    fn has_drop_impl(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        if self.tys.local_adt(t).is_none() {
            return false;
        }
        let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: self.p.gx.lang.drop, args, bindings: EMPTY_BINDINGS };
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        let sel = self.select_obligation(tr);
        self.rollback_vars(snap);
        self.obl_truncate(obl_len);
        matches!(sel, Selection::Impl { .. })
    }

    /// The place an expression denotes, rooted at a local, if it is one.
    fn cap_cat(&mut self, e: ExprId) -> Cat {
        let p = self.p;
        let ety = self.out.expr_ty[self.ei(e)];
        // A place through a user `Deref` is the value of its `deref`
        // call, with the base borrowed (`cap_walk` records that borrow).
        if matches!(p.ast.expr(e), Expr::Field { .. } | Expr::TupleField { .. } | Expr::Deref(_) | Expr::Index { .. }) && self.out.deref_recv.iter().any(|(x, _)| *x == e) {
            return Cat::Rvalue;
        }
        match (p.ast.expr(e), self.out.expr_res[self.ei(e)]) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => Cat::Place(CPlace { root: l, projs: Vec::new(), ty: self.out.locals[l as usize].ty }),
            (Expr::Field { base, .. } | Expr::TupleField { base, .. }, Res::Field { derefs, index }) => match self.cap_cat(*base) {
                Cat::Place(mut pl) => {
                    for _ in 0..derefs {
                        // Through `Rc`, `Arc`, or a guard: an overloaded
                        // deref, a value of the call (`cap_walk` borrows
                        // the pointer).
                        if self.cap_smart(pl.ty).is_some() {
                            return Cat::Rvalue;
                        }
                        if !self.cap_deref(&mut pl) {
                            return Cat::Bad;
                        }
                    }
                    pl.push(CProj::Field(index), ety);
                    Cat::Place(pl)
                }
                other => other,
            },
            (Expr::Deref(inner), _) => match self.cap_cat(*inner) {
                Cat::Place(_) if let Cat::Place(pl) = self.cap_cat(*inner) && self.cap_smart(pl.ty).is_some() => Cat::Rvalue,
                Cat::Place(mut pl) => {
                    if self.cap_deref(&mut pl) {
                        Cat::Place(pl)
                    } else {
                        Cat::Bad
                    }
                }
                other => other,
            },
            // `map[&q]` (W-STD-B): the value behind `get`'s reference, a
            // call with the base borrowed (the walk records that borrow).
            (Expr::Index { .. }, Res::MapIndex { .. }) => Cat::Rvalue,
            (Expr::Index { base, .. }, Res::Index { derefs }) => {
                let bt = self.out.expr_ty[self.ei(*base)];
                let bt = self.cap_peel(bt, derefs);
                // `Vec` indexing is the overloaded `Index` trait: a
                // value of the call, with the base borrowed (the walk
                // records that borrow). Arrays and slices are places.
                if self.tys.vec_elem(bt).is_some() {
                    return Cat::Rvalue;
                }
                match self.cap_cat(*base) {
                    Cat::Place(mut pl) => {
                        for _ in 0..derefs {
                            // Through `Rc`, a guard, or a `Vec`: an overloaded
                            // deref, so the element is in a temporary's
                            // pointee (`cap_index_base` borrows the pointer).
                            if self.cap_smart(pl.ty).is_some() {
                                return Cat::Rvalue;
                            }
                            if !self.cap_deref(&mut pl) {
                                return Cat::Bad;
                            }
                        }
                        pl.push(CProj::Index, ety);
                        Cat::Place(pl)
                    }
                    other => other,
                }
            }
            _ => Cat::Rvalue,
        }
    }

    /// For a std type whose deref is an overloaded call (`Rc`, `Arc`, a
    /// `RefCell` or lock guard, `String`, `Vec`, `Cow`): whether it has
    /// `DerefMut`. None for references, `Box` (a builtin deref), and
    /// every other type.
    fn cap_smart(&mut self, t: Ty) -> Option<bool> {
        let t = self.resolve(t);
        if self.tys.rc_elem(t).is_some() || crate::check::collect::cow_arg(&self.tys, t).is_some() {
            return Some(false);
        }
        if self.tys.is_string_ty(t) || self.tys.vec_elem(t).is_some() {
            return Some(true);
        }
        self.tys.guard_elem(t).map(|g| g.1)
    }

    /// The place an overloaded std deref inside `e` (a field or deref
    /// expression) is called on, with its `DerefMut`-ness: the base
    /// place after the builtin derefs before it.
    fn cap_smart_base(&mut self, e: ExprId) -> Option<(CPlace, bool, ExprId)> {
        let (inner, derefs) = match (self.p.ast.expr(e), self.out.expr_res[self.ei(e)]) {
            (Expr::Field { base, .. } | Expr::TupleField { base, .. }, Res::Field { derefs, .. }) => (*base, derefs),
            (Expr::Deref(inner), _) => (*inner, 1),
            _ => return None,
        };
        let Cat::Place(mut pl) = self.cap_cat(inner) else { return None };
        for _ in 0..derefs {
            if let Some(m) = self.cap_smart(pl.ty) {
                return Some((pl, m, inner));
            }
            if !self.cap_deref(&mut pl) {
                return None;
            }
        }
        None
    }

    /// Peels `n` reference layers off a type.
    fn cap_peel(&mut self, mut t: Ty, n: u8) -> Ty {
        for _ in 0..n {
            t = self.resolve(t);
            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                t = inner;
            }
        }
        self.resolve(t)
    }

    /// Appends a builtin deref: of a reference, or of a `Box` (a place
    /// projection in rustc, so captures go through it precisely). False
    /// for any other type.
    fn cap_deref(&mut self, pl: &mut CPlace) -> bool {
        let t = self.resolve(pl.ty);
        let inner = match self.kind(t) {
            TyKind::Ref(_, _, inner) => inner,
            _ => match self.tys.boxed_elem(t) {
                Some(inner) => inner,
                None => return false,
            },
        };
        pl.ty = t;
        pl.push(CProj::Deref, inner);
        true
    }

    /// Records one use of a place reached from a captured variable.
    fn cap_use(&mut self, pl: CPlace, mode: CaptureMode, span: Span, w: &mut CapWalk) {
        if !w.upvar(pl.root) {
            return;
        }
        let mut pl = pl;
        let mut mode = mode;
        if mode != CaptureMode::Value {
            // Borrows stop at the first field of a packed struct (rustc
            // `restrict_repr_packed_field_ref_capture`).
            let packed = pl.projs.iter().position(|(pr, before)| {
                matches!(pr, CProj::Field(_))
                    && self.tys.local_adt(self.resolve(*before)).is_some_and(|a| self.p.adt(a).repr.pack.is_some())
            });
            if let Some(i) = packed {
                truncate_place(&mut pl, &mut mode, i, &self.tys);
            }
        }
        // A mutable use must be legal on the original place: the
        // binding is `mut`, or the place is reached through `&mut`
        // (rustc E0594/E0596 on the upvar).
        if matches!(mode, CaptureMode::MutRef) && !self.place_mutable(&pl) {
            let name = self.name(self.out.locals[pl.root as usize].name).to_string();
            self.err("L0308", span, format!("cannot borrow `{name}` as mutable in this closure"), "Declare the variable with `let mut`.");
        }
        w.uses.push((pl, mode));
    }

    /// rustc `determine_capture_mutability` for one use place.
    fn place_mutable(&mut self, pl: &CPlace) -> bool {
        let mut m = self.out.locals[pl.root as usize].mutable;
        for (pr, before) in &pl.projs {
            if *pr == CProj::Deref {
                let before = self.resolve(*before);
                match self.kind(before) {
                    TyKind::Ref(_, mm, _) if mm.is_mut() => m = true,
                    // A `Box` deref keeps the box place's mutability.
                    _ if self.tys.boxed_elem(before).is_some() => {}
                    _ => return false,
                }
            }
        }
        m
    }

    /// `consume_or_copy` of a place: a copy for Copy types is a shared
    /// borrow, anything else moves.
    fn cap_consume_place(&mut self, pl: CPlace, span: Span, w: &mut CapWalk) {
        if !w.upvar(pl.root) {
            return;
        }
        let Some(copy) = self.copy_known(pl.ty) else {
            w.bad.get_or_insert(span);
            return;
        };
        let mode = if copy { CaptureMode::Ref } else { CaptureMode::Value };
        self.cap_use(pl, mode, span, w);
    }

    /// Copy when inference already decides it: None while the answer
    /// hangs on an unbound type variable (rustc decides later, after
    /// the whole body; this subset rejects instead of guessing).
    fn copy_known(&mut self, t: Ty) -> Option<bool> {
        let t = self.resolve(t);
        match self.kind(t) {
            TyKind::Infer(v) => (v.is_int() || v.is_float()).then_some(true),
            TyKind::Ref(_, m, _) => Some(!m.is_mut()),
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let mut all = true;
                for e in elems {
                    all &= self.copy_known(e)?;
                }
                Some(all)
            }
            TyKind::Array(e, _) => self.copy_known(e),
            TyKind::Closure(_, a) => {
                let elems: Vec<Ty> = self.tys.args(a).iter().filter_map(|g| g.as_ty()).collect();
                let mut all = true;
                for e in elems {
                    all &= self.copy_known(e)?;
                }
                Some(all)
            }
            _ => {
                if self.tys.is_string_ty(t) || self.tys.vec_elem(t).is_some() {
                    return Some(false);
                }
                if let Some(e) = self.tys.option_elem(t) {
                    return self.copy_known(e);
                }
                if self.has_unbound_var(t) {
                    return None;
                }
                let d = self.deep(t);
                Some(is_copy(self.p, &self.tys, d))
            }
        }
    }

    /// `consume_expr`: the value of `e` is used (moved or copied).
    fn cap_consume(&mut self, e: ExprId, w: &mut CapWalk) {
        let span = self.span(e);
        if self.cap_coerced(e, w) {
            self.cap_walk(e, false, w);
            return;
        }
        match self.cap_cat(e) {
            Cat::Place(pl) => self.cap_consume_place(pl, span, w),
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(e, false, w);
    }

    /// An assignment target: every place inside a destructuring
    /// form is mutated, so it captures as a mutable borrow of that
    /// place. Discards and `..` rest elements capture nothing.
    fn cap_assign_target(&mut self, e: ExprId, w: &mut CapWalk) {
        match self.p.ast.expr(e) {
            Expr::Tuple(elems) | Expr::Array(elems) => {
                for &el in elems {
                    if !matches!(self.p.ast.expr(el), Expr::Range { lo: None, hi: None, inclusive: false }) {
                        self.cap_assign_target(el, w);
                    }
                }
            }
            Expr::StructLit { fields, .. } => {
                for &(_, _, fe) in fields {
                    self.cap_assign_target(fe, w);
                }
            }
            Expr::Call { args, .. } if matches!(self.out.expr_res[self.ei(e)], Res::Variant(..)) => {
                for &arg in args {
                    if !matches!(self.p.ast.expr(arg), Expr::Range { lo: None, hi: None, inclusive: false }) {
                        self.cap_assign_target(arg, w);
                    }
                }
            }
            Expr::Underscore | Expr::Unit => {}
            _ => self.cap_borrow(e, CaptureMode::MutRef, w),
        }
    }

    /// `borrow_expr`: `e` is borrowed (or mutated, for `MutRef`).
    fn cap_borrow(&mut self, e: ExprId, mode: CaptureMode, w: &mut CapWalk) {
        let span = self.span(e);
        match self.cap_cat(e) {
            Cat::Place(pl) => self.cap_use(pl, mode, span, w),
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(e, mode != CaptureMode::Ref, w);
    }

    /// A coercion on `e` (rustc adjustments at a coercion site): the
    /// reborrowing forms borrow a place below `e`. True when handled.
    fn cap_coerced(&mut self, e: ExprId, w: &mut CapWalk) -> bool {
        let c = self.out.coerce[self.ei(e)];
        let (derefs, mode) = match c {
            // A raw pointer coercion (w-cinterop) borrows nothing past
            // the coercion site: the plain walk sees the borrow inside.
            // A char pattern reads the char by value, like a plain use.
            Coerce::None | Coerce::ReifyFn(_) | Coerce::RefToPtr(_) | Coerce::CharPat => return false,
            Coerce::MutToShared => (1, CaptureMode::Ref),
            Coerce::Reborrow => (1, CaptureMode::MutRef),
            Coerce::Deref(n) => (n as usize + 1, CaptureMode::Ref),
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => (1, if m { CaptureMode::MutRef } else { CaptureMode::Ref }),
            Coerce::BoxToRef(n, m) => (n as usize, if m { CaptureMode::MutRef } else { CaptureMode::Ref }),
            // A deref coercion through user `Deref` impls borrows the
            // place below the reference for the first impl's call.
            Coerce::UserDeref(t) | Coerce::UserDerefTail(t) => {
                let before = self.out.deref_coerce.iter().find(|(x, _)| *x == e).map_or(1, |(_, d)| d.before);
                (before as usize, if matches!(self.kind(t), TyKind::Ref(_, m, _) if m.is_mut()) { CaptureMode::MutRef } else { CaptureMode::Ref })
            }
            // An owning unsizing (`Box<T>` to `Box<dyn Tr>`) moves the
            // value: the plain consume.
            Coerce::Unsize(t) if !matches!(self.kind(t), TyKind::Ref(..)) => return false,
            // Builtin derefs down to the Cow, whose `Deref` borrows it.
            Coerce::CowDeref(n, _) => (n as usize, CaptureMode::Ref),
            // A method receiver: `cap_receiver` covers it.
            Coerce::CowRecv(..) | Coerce::ByNext(_) | Coerce::IntoIterCall(_) => return false,
            // A dyn coercion reborrows the source at the target's
            // mutability before it builds the fat pointer.
            Coerce::Unsize(t) => (1, if matches!(self.kind(t), TyKind::Ref(_, m, _) if m.is_mut()) { CaptureMode::MutRef } else { CaptureMode::Ref }),
            Coerce::StrFromString => {
                // Builtin derefs down to the `String`, then its
                // overloaded deref borrows it.
                let mut t = self.resolve(self.out.expr_ty[self.ei(e)]);
                let mut n = 0;
                while let TyKind::Ref(_, _, inner) = self.kind(t) {
                    n += 1;
                    t = self.resolve(inner);
                    if self.tys.is_string_ty(t) {
                        break;
                    }
                }
                (n, CaptureMode::Ref)
            }
        };
        let span = self.span(e);
        match self.cap_cat(e) {
            Cat::Place(mut pl) => {
                for _ in 0..derefs {
                    // Through `Rc`, a guard, or a `String` (`&Rc<T>` to
                    // `&T`): the overloaded `deref` borrows the pointer.
                    if let Some(has_mut) = self.cap_smart(pl.ty) {
                        let m = if mode == CaptureMode::Ref || !has_mut { CaptureMode::Ref } else { mode };
                        self.cap_use(pl, m, span, w);
                        return true;
                    }
                    if !self.cap_deref(&mut pl) {
                        self.cap_bad_if_upvar(e, w);
                        return true;
                    }
                }
                self.cap_use(pl, mode, span, w);
            }
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        true
    }

    /// Marks the walk unsupported when `e` mentions a captured variable.
    fn cap_bad_if_upvar(&mut self, e: ExprId, w: &mut CapWalk) {
        if self.mentions_upvar(e, w.first_local) {
            w.bad.get_or_insert(self.span(e));
        }
    }

    /// True when any expression inside `e` resolves to a local below `first`.
    fn mentions_upvar(&self, e: ExprId, first: u32) -> bool {
        let (lo, hi) = (self.out.expr_base, self.out.expr_base + self.out.expr_res.len() as u32);
        let span = self.p.ast.expr_span(e);
        (lo..hi).any(|x| {
            matches!(self.out.expr_res[(x - lo) as usize], Res::Local(l) if l < first) && {
                let s = self.p.ast.expr_span(ExprId(x));
                s.file == span.file && s.lo >= span.lo && s.hi <= span.hi
            }
        })
    }

    /// `walk_block`: statements, then the tail is consumed.
    fn cap_block(&mut self, b: ast::BlockId, w: &mut CapWalk) {
        let p = self.p;
        let block = p.ast.block(b);
        for st in &block.stmts {
            match st {
                Stmt::Let { pat, init, els, .. } => {
                    if let Some(init) = init {
                        self.cap_local(*init, *pat, w);
                    }
                    if let Some(els) = els {
                        self.cap_block(*els, w);
                    }
                }
                Stmt::Expr { expr, .. } => self.cap_consume(*expr, w),
                Stmt::Item(..) => {}
                Stmt::Macro { .. } => w.bad = w.bad.or(Some(block.span)),
            }
        }
        if let Some(t) = block.tail {
            self.cap_consume(t, w);
        }
    }

    /// `walk_local`: the initializer is walked (not consumed), then the
    /// pattern binds from its place.
    fn cap_local(&mut self, init: ExprId, pat: PatId, w: &mut CapWalk) {
        if self.cap_coerced(init, w) {
            self.cap_walk(init, false, w);
            return;
        }
        // Any other coercion (an owning unsizing `let s: Arc<dyn Tr> =
        // upvar;`, a fn item to a fn pointer) makes a new value of the
        // pattern's type: the plain consume, not a binding from the place,
        // whose type the pattern's is not (the env field took `Arc<dyn Tr>`
        // and the creator stored `Arc<T>`: tcc errors, ts-rust hostimpl.rs
        // tests `FakeSpawner::spawn`).
        if !matches!(self.out.coerce[self.ei(init)], Coerce::None) {
            self.cap_consume(init, w);
            return;
        }
        self.cap_walk(init, false, w);
        match self.cap_cat(init) {
            Cat::Place(pl) => {
                if w.upvar(pl.root) {
                    w.fake_reads.push(pl.root);
                }
                self.cap_pat(pl, pat, false, w);
            }
            Cat::Bad => self.cap_bad_if_upvar(init, w),
            Cat::Rvalue => {}
        }
    }

    /// `walk_expr`: the uses inside `e` (its own place use is the caller's).
    fn cap_walk(&mut self, e: ExprId, mut_ctx: bool, w: &mut CapWalk) {
        let p = self.p;
        let res = self.out.expr_res[self.ei(e)];
        match p.ast.expr(e) {
            Expr::Int(..)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::ByteStr(_)
            | Expr::Char(_)
            | Expr::Unit
            | Expr::Path(_)
            | Expr::SelfValue
            | Expr::Continue(_)
            | Expr::ConstBlock(_)
            | Expr::QPath { .. }
            | Expr::OffsetOf { .. }
            | Expr::Underscore => {}
            Expr::Block(b) | Expr::UnsafeBlock(b) => self.cap_block(*b, w),
            Expr::LabeledBlock { body, .. } | Expr::Loop { body, .. } => self.cap_block(*body, w),
            Expr::If { cond, then, els } => {
                self.cap_consume(*cond, w);
                self.cap_block(*then, w);
                if let Some(x) = els {
                    self.cap_consume(*x, w);
                }
            }
            Expr::While { cond, body, .. } => {
                self.cap_consume(*cond, w);
                self.cap_block(*body, w);
            }
            Expr::For { iter, body, .. } => {
                self.cap_consume(*iter, w);
                self.cap_block(*body, w);
            }
            Expr::Let { pat, scrut } => self.cap_local(*scrut, *pat, w),
            Expr::Match { scrut, arms } => {
                self.cap_walk(*scrut, false, w);
                let place = self.cap_cat(*scrut);
                for arm in arms {
                    match &place {
                        Cat::Place(pl) => {
                            if w.upvar(pl.root) {
                                w.fake_reads.push(pl.root);
                            }
                            self.cap_pat(pl.clone(), arm.pat, arm.guard.is_some(), w);
                        }
                        Cat::Bad => self.cap_bad_if_upvar(*scrut, w),
                        Cat::Rvalue => {}
                    }
                    if let Some(g) = arm.guard {
                        self.cap_consume(g, w);
                    }
                    self.cap_consume(arm.body, w);
                }
            }
            Expr::Call { callee, args } => {
                match res {
                    Res::ClosureCall { kind, derefs, .. } => {
                        let span = self.span(*callee);
                        match self.cap_cat(*callee) {
                            Cat::Place(mut pl) => {
                                let mut ok = true;
                                for _ in 0..derefs {
                                    ok &= self.cap_deref(&mut pl);
                                }
                                if !ok {
                                    self.cap_bad_if_upvar(*callee, w);
                                } else {
                                    match kind {
                                        ClosureKind::Fn => self.cap_use(pl, CaptureMode::Ref, span, w),
                                        ClosureKind::FnMut => self.cap_use(pl, CaptureMode::MutRef, span, w),
                                        ClosureKind::FnOnce => self.cap_consume_place(pl, span, w),
                                    }
                                }
                            }
                            Cat::Bad => self.cap_bad_if_upvar(*callee, w),
                            Cat::Rvalue => {}
                        }
                        self.cap_walk(*callee, kind == ClosureKind::FnMut, w);
                    }
                    // A call through a type parameter's Fn bound (a
                    // template check) or a `dyn Fn` value's vtable: the
                    // callee is the receiver.
                    Res::Method { derefs, autoref, .. } | Res::DynMethod { derefs, autoref, .. } => {
                        self.cap_receiver(*callee, derefs, autoref, w)
                    }
                    // A fn item or pointer behind a smart pointer or a
                    // `&mut` (`w()` with `w: Box<&F>` or `&mut &F`): the
                    // call autoderefs through a borrow.
                    Res::Fn(_) | Res::Variant(..) | Res::Builtin(_) | Res::Intrinsic(_) | Res::Indirect
                        if {
                        let ct = self.out.expr_ty[self.ei(*callee)];
                        let ct = self.resolve(ct);
                        self.tys.smart_elem(ct).is_some() || matches!(self.kind(ct), TyKind::Ref(_, Mut::Mut, _))
                    } =>
                    {
                        self.cap_receiver(*callee, 0, Autoref::Ref, w)
                    }
                    _ => self.cap_consume(*callee, w),
                }
                for &a in args {
                    self.cap_consume(a, w);
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                // Through a Cow's `&B` view (W-STD-B): the Cow's `Deref`
                // borrows the Cow, whatever the method then does.
                let res = match self.out.coerce[self.ei(*recv)] {
                    Coerce::CowRecv(n, _) => Res::BuiltinMethod { b: crate::check::Builtin::CowDeref, derefs: n, autoref: Autoref::Ref },
                    _ => res,
                };
                match res {
                    // A dyn method call through the vtable borrows its
                    // receiver like any other method call.
                    // Through a user `Deref` impl, the receiver is borrowed
                    // for the `deref` call (its `Res` applies to the target).
                    Res::Method { .. } | Res::BuiltinMethod { .. } | Res::DynMethod { .. } | Res::Any { .. }
                        if let Some((before, mutable)) =
                            self.out.deref_recv.iter().filter(|(x, _)| *x == e).min_by_key(|(_, d)| d.depth).map(|(_, d)| (d.before, d.mutable)) =>
                    {
                        self.cap_receiver(*recv, before, if mutable { Autoref::RefMut } else { Autoref::Ref }, w);
                    }
                    Res::Method { derefs, autoref, .. }
                    | Res::BuiltinMethod { derefs, autoref, .. }
                    | Res::DynMethod { derefs, autoref, .. }
                    // `Any`'s methods (`is`, `downcast_ref`, `type_id`; R26)
                    // borrow their receiver, and `Box<dyn Any>::downcast`
                    // takes it by value (no autoref).
                    | Res::Any { derefs, autoref, .. } => {
                        self.cap_receiver(*recv, derefs, autoref, w);
                    }
                    // `cmp`, `partial_cmp`, `lt`, and kin take `&self`.
                    Res::PrimCmp { derefs, .. } => self.cap_receiver(*recv, derefs, Autoref::Ref, w),
                    // `Ordering`'s `then_with`, `then`, `reverse`, and `is_*`
                    // take `self` by value (`Ordering` is `Copy`).
                    Res::OrderingOp { derefs, .. } => self.cap_receiver(*recv, derefs, Autoref::None, w),
                    // `x.eq(y)` as the operator `Self == R` (check's
                    // `cmp_cross_eq`): borrows the receiver at depth `ld`.
                    Res::Bin { ld, .. } => self.cap_receiver(*recv, ld, Autoref::Ref, w),
                    // A call that failed to resolve already reported its error.
                    Res::None if !self.errs.is_empty() => {}
                    _ => self.cap_bad_if_upvar(*recv, w),
                }
                for &a in args {
                    self.cap_consume(a, w);
                }
            }
            // Through a user `Deref` impl: `deref(&base)`, or
            // `deref_mut(&mut base)` in a mutable use (an index then
            // reads its index as a value).
            Expr::Field { base: inner, .. } | Expr::TupleField { base: inner, .. } | Expr::Deref(inner) | Expr::Index { base: inner, .. }
                if let Some((before, has_mut)) =
                    self.out.deref_recv.iter().filter(|(x, _)| *x == e).min_by_key(|(_, d)| d.depth).map(|(_, d)| (d.before, d.f_mut.is_some())) =>
            {
                let mutable = mut_ctx && has_mut;
                let span = self.span(*inner);
                match self.cap_cat(*inner) {
                    Cat::Place(mut pl) => {
                        let mut ok = true;
                        for _ in 0..before {
                            ok &= self.cap_deref(&mut pl);
                        }
                        if ok {
                            let m = if mutable { CaptureMode::MutRef } else { CaptureMode::Ref };
                            self.cap_use(pl, m, span, w);
                        } else {
                            self.cap_bad_if_upvar(*inner, w);
                        }
                    }
                    Cat::Bad => self.cap_bad_if_upvar(*inner, w),
                    Cat::Rvalue => {}
                }
                self.cap_walk(*inner, mutable, w);
                if let Expr::Index { index, .. } = p.ast.expr(e) {
                    self.cap_consume(*index, w);
                }
            }
            // Through `Rc`, `Arc`, or a guard (W-THREADS): rustc's capture
            // stops at the overloaded deref and borrows the pointer
            // (uniquely for a guard's `deref_mut` in a mutable use).
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Deref(_) if let Some((pl, has_mut, inner)) = self.cap_smart_base(e) => {
                let mutable = mut_ctx && has_mut;
                let span = self.span(inner);
                let m = if mutable { CaptureMode::MutRef } else { CaptureMode::Ref };
                self.cap_use(pl, m, span, w);
                // Index operands inside the pointer's place (`*v[i]`).
                self.cap_walk(inner, mutable, w);
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => self.cap_walk(*base, mut_ctx, w),
            Expr::Deref(inner) => self.cap_walk(*inner, mut_ctx, w),
            Expr::Index { base, index } => {
                if let Res::Index { derefs } | Res::SliceIndex { derefs } | Res::MapIndex { derefs } | Res::TraitIndex { derefs } = res {
                    self.cap_index_base(*base, derefs, res, mut_ctx, w);
                } else {
                    self.cap_bad_if_upvar(*base, w);
                }
                self.cap_consume(*index, w);
            }
            Expr::Binary { op, lhs, rhs } => {
                use BinOp::*;
                if matches!(op, Eq | Ne | Lt | Le | Gt | Ge) {
                    self.cap_borrow(*lhs, CaptureMode::Ref, w);
                    self.cap_borrow(*rhs, CaptureMode::Ref, w);
                } else {
                    self.cap_consume(*lhs, w);
                    self.cap_consume(*rhs, w);
                }
            }
            Expr::Unary { expr, .. } | Expr::Cast { expr, .. } => self.cap_consume(*expr, w),
            Expr::Ref { mutable, raw, expr } => {
                if *raw {
                    self.cap_bad_if_upvar(*expr, w);
                } else {
                    self.cap_borrow(*expr, if *mutable { CaptureMode::MutRef } else { CaptureMode::Ref }, w);
                }
            }
            Expr::Assign { lhs, rhs } => {
                self.cap_assign_target(*lhs, w);
                self.cap_consume(*rhs, w);
            }
            Expr::AssignOp { lhs, rhs, .. } => {
                self.cap_borrow(*lhs, CaptureMode::MutRef, w);
                self.cap_consume(*rhs, w);
            }
            Expr::StructLit { fields, update, .. } => {
                for (_, _, x) in fields {
                    self.cap_consume(*x, w);
                }
                if let Some(base) = update {
                    let span = self.span(*base);
                    if let Cat::Place(pl) = self.cap_cat(*base) {
                        let bt = self.resolve(pl.ty);
                        let named: Vec<Sym> = fields.iter().map(|(n, _, _)| *n).collect();
                        if let Some(a) = self.tys.local_adt(bt) {
                            let fs: Vec<(Sym, Ty)> = self.p.adt(a).variants[0].fields.iter().map(|f| (f.name, f.ty)).collect();
                            for (i, (n, ft)) in fs.into_iter().enumerate() {
                                if !named.contains(&n) {
                                    let mut fp = pl.clone();
                                    fp.push(CProj::Field(i as u32), ft);
                                    self.cap_consume_place(fp, span, w);
                                }
                            }
                        } else {
                            self.cap_bad_if_upvar(*base, w);
                        }
                    }
                    self.cap_walk(*base, false, w);
                }
            }
            Expr::Range { lo, hi, .. } => {
                for x in [lo, hi].into_iter().flatten() {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Break { value, .. } => {
                if let Some(x) = value {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Return(v) => {
                if let Some(x) = v {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Tuple(xs) | Expr::Array(xs) => {
                for &x in xs {
                    self.cap_consume(x, w);
                }
            }
            Expr::ArrayRepeat { value, .. } => self.cap_consume(*value, w),
            Expr::Macro { kind, args, fmt, .. } => self.cap_macro(*kind, args, fmt, w),
            Expr::Closure { .. } => {
                // A nested closure: its captures that reach outside
                // this closure are uses here, with the same mode.
                let Some(inner) = self.closures.iter().find(|c| c.expr == e).cloned() else {
                    self.cap_bad_if_upvar(e, w);
                    return;
                };
                let span = self.span(e);
                for c in &inner.captures {
                    if !w.upvar(c.root) {
                        continue;
                    }
                    let mut pl = CPlace { root: c.root, projs: Vec::new(), ty: self.out.locals[c.root as usize].ty };
                    let mut variant = 0;
                    let mut ok = true;
                    for pr in &c.projs {
                        match *pr {
                            Proj::Deref => ok &= self.cap_deref(&mut pl),
                            Proj::Downcast(v) => {
                                variant = v;
                                let t = pl.ty;
                                pl.push(CProj::Downcast(v), t);
                            }
                            Proj::Field(i) => {
                                let t = self.resolve(pl.ty);
                                match self.field_ty_at(t, variant, i) {
                                    Some(ft) => pl.push(CProj::Field(i), ft),
                                    None => ok = false,
                                }
                                variant = 0;
                            }
                            Proj::Index(_) => ok = false,
                        }
                    }
                    if !ok {
                        w.bad.get_or_insert(span);
                        continue;
                    }
                    match c.mode {
                        CaptureMode::Value => self.cap_consume_place(pl, span, w),
                        m => self.cap_use(pl, m, span, w),
                    }
                }
            }
            // `x?` is `match Try::branch(x) { .. }`: the operand is consumed.
            Expr::Try(inner) => self.cap_consume(*inner, w),
            Expr::Await(_) | Expr::AsyncBlock { .. } | Expr::MacroCall(_) => self.cap_bad_if_upvar(e, w),
        }
    }

    /// The base of an index expression with `derefs` autoderef steps.
    /// Builtin derefs (references, `Box`) extend the place; the first
    /// overloaded deref (`Rc`, a guard, `Vec` to a slice) borrows the
    /// place before it, as `deref(&p)` or `deref_mut(&mut p)` in a
    /// mutable use, and ends it. An overloaded index (`Vec`, a range, a
    /// map, a written `Index` impl) borrows the place after the derefs.
    /// An array or slice index borrows nothing here: the place use is
    /// the caller's (`cap_cat`).
    fn cap_index_base(&mut self, base: ExprId, derefs: u8, res: Res, mut_ctx: bool, w: &mut CapWalk) {
        let span = self.span(base);
        let mode = |m: bool| if m { CaptureMode::MutRef } else { CaptureMode::Ref };
        match self.cap_cat(base) {
            Cat::Place(mut pl) => {
                let mut done = false;
                for _ in 0..derefs {
                    if let Some(has_mut) = self.cap_smart(pl.ty) {
                        self.cap_use(pl.clone(), mode(mut_ctx && has_mut), span, w);
                        done = true;
                        break;
                    }
                    if !self.cap_deref(&mut pl) {
                        self.cap_bad_if_upvar(base, w);
                        done = true;
                        break;
                    }
                }
                let t = self.resolve(pl.ty);
                let overloaded = !matches!(res, Res::Index { .. }) || self.tys.vec_elem(t).is_some();
                if !done && overloaded {
                    self.cap_use(pl, mode(mut_ctx), span, w);
                }
            }
            Cat::Bad => self.cap_bad_if_upvar(base, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(base, mut_ctx, w);
    }

    /// A method receiver: builtin derefs, then a borrow per the
    /// autoref, or a by-value use. A deref that is not a reference
    /// (`String` to `str`) is an overloaded deref: it borrows the
    /// place reached so far and the rest is a temporary.
    fn cap_receiver(&mut self, recv: ExprId, derefs: u8, autoref: Autoref, w: &mut CapWalk) {
        let span = self.span(recv);
        let mode = match autoref {
            Autoref::None => None,
            Autoref::Ref | Autoref::SliceRef => Some(CaptureMode::Ref),
            Autoref::RefMut | Autoref::SliceRefMut => Some(CaptureMode::MutRef),
        };
        match self.cap_cat(recv) {
            Cat::Place(mut pl) => {
                let mut overloaded = false;
                for _ in 0..derefs {
                    let t = self.resolve(pl.ty);
                    if matches!(self.kind(t), TyKind::Ref(..)) || self.tys.boxed_elem(t).is_some() {
                        self.cap_deref(&mut pl);
                    } else {
                        overloaded = true;
                        break;
                    }
                }
                match (overloaded, mode) {
                    (false, None) => self.cap_consume_place(pl, span, w),
                    (_, Some(m)) => self.cap_use(pl, m, span, w),
                    (true, None) => self.cap_bad_if_upvar(recv, w),
                }
            }
            Cat::Bad => self.cap_bad_if_upvar(recv, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(recv, matches!(autoref, Autoref::RefMut | Autoref::SliceRefMut), w);
    }

    /// Builtin macros: format arguments are borrowed, `vec!` and
    /// `assert!` consume, `assert_eq!` borrows both sides.
    fn cap_macro(&mut self, kind: MacroKind, args: &[ExprId], fmt: &[FmtPiece], w: &mut CapWalk) {
        let fixed = match kind {
            MacroKind::Vec => {
                for &a in args {
                    self.cap_consume(a, w);
                }
                return;
            }
            MacroKind::Assert => {
                if let Some(&c) = args.first() {
                    self.cap_consume(c, w);
                }
                1
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                for &a in args.iter().take(2) {
                    self.cap_borrow(a, CaptureMode::Ref, w);
                }
                2
            }
            _ => 0,
        };
        // Format arguments are borrowed in argument order, as the
        // `format_args!` expansion takes `(&a, &b, ..)`.
        let _ = fmt;
        for &a in args.iter().skip(fixed) {
            self.cap_borrow(a, CaptureMode::Ref, w);
        }
    }

    /// `walk_pat`: bindings use the matched place, refutable tests read it.
    fn cap_pat(&mut self, place: CPlace, pat: PatId, has_guard: bool, w: &mut CapWalk) {
        let p = self.p;
        let span = p.ast.pat_span(pat);
        let mut place = place;
        let pi = (pat.0 - self.out.pat_base) as usize;
        for _ in 0..self.out.pat_derefs[pi] {
            if !self.cap_deref(&mut place) {
                if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
                return;
            }
        }
        let pty = self.out.pat_ty[pi];
        let read = |cx: &mut Self, pl: &CPlace, w: &mut CapWalk| cx.cap_use(pl.clone(), CaptureMode::Ref, span, w);
        match (p.ast.pat(pat), self.out.pat_res[pi]) {
            (Pat::Wild | Pat::Rest, _) => {}
            (Pat::Binding { .. }, PatRes::Binding { mode, .. }) => {
                if has_guard {
                    read(self, &place, w);
                }
                match mode {
                    BindMode::Move => {
                        place.ty = pty;
                        self.cap_consume_place(place, span, w)
                    }
                    BindMode::Ref(m) => self.cap_use(place, if m { CaptureMode::MutRef } else { CaptureMode::Ref }, span, w),
                }
            }
            (Pat::Binding { .. }, res) => {
                // A const or unit variant pattern spelled as a name.
                if !matches!(res, PatRes::Variant(a, _) if !self.multivariant(a)) {
                    read(self, &place, w);
                }
            }
            (Pat::At { inner, .. }, PatRes::Binding { mode, .. }) => {
                if has_guard {
                    read(self, &place, w);
                }
                match mode {
                    BindMode::Move => {
                        let mut whole = place.clone();
                        whole.ty = pty;
                        self.cap_consume_place(whole, span, w)
                    }
                    BindMode::Ref(m) => self.cap_use(place.clone(), if m { CaptureMode::MutRef } else { CaptureMode::Ref }, span, w),
                }
                self.cap_pat(place, *inner, has_guard, w);
            }
            (Pat::Lit(_) | Pat::Range { .. }, _) => read(self, &place, w),
            (Pat::Path(_), res) => {
                if !matches!(res, PatRes::Variant(a, _) if !self.multivariant(a)) {
                    read(self, &place, w);
                }
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                read(self, &place, w);
                let elem = self.tys.option_elem(self.resolve(place.ty)).unwrap_or(ERROR);
                let mut sub = place.clone();
                let t = sub.ty;
                sub.push(CProj::Downcast(1), t);
                sub.push(CProj::Field(0), elem);
                if let Some(&s) = elems.first() {
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            // `Entry::Occupied(x)` / `Entry::Vacant(x)`: the payload is the
            // Entry itself, read as the variant's entry type.
            (Pat::TupleStruct { elems, .. }, PatRes::Entry(_)) => {
                read(self, &place, w);
                if let Some(&s) = elems.first() {
                    self.cap_pat(place.clone(), s, has_guard, w);
                }
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                // `Ok(x)` / `Err(e)`: variant 0 / 1, field 0 (as lowering).
                read(self, &place, w);
                if let Some(&s) = elems.first() {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    let t = sub.ty;
                    sub.push(CProj::Downcast((!is_ok) as u32), t);
                    sub.push(CProj::Field(0), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                if self.multivariant(a) {
                    read(self, &place, w);
                }
                let mut base = place.clone();
                if p.adt(a).is_enum {
                    let t = base.ty;
                    base.push(CProj::Downcast(v), t);
                }
                let subs: Vec<(u32, PatId)> = match p.ast.pat(pat) {
                    Pat::TupleStruct { elems, .. } => {
                        let n = p.adt(a).variants[v as usize].fields.len();
                        map_tuple_elems(&p.ast, elems, n).unwrap_or_default().into_iter().map(|(i, s)| (i as u32, s)).collect()
                    }
                    Pat::Struct { fields, .. } => {
                        let vf = &p.adt(a).variants[v as usize].fields;
                        fields.iter().filter_map(|&(n, s)| vf.iter().position(|f| f.name == n).map(|i| (i as u32, s))).collect()
                    }
                    _ => Vec::new(),
                };
                for (i, s) in subs {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = base.clone();
                    sub.push(CProj::Field(i), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Tuple(elems), _) => {
                let n = match self.kind(self.resolve(place.ty)) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                for (i, s) in map_tuple_elems(&p.ast, elems, n).unwrap_or_default() {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    sub.push(CProj::Field(i as u32), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Ref { inner, .. }, _) => {
                if self.cap_deref(&mut place) {
                    self.cap_pat(place, *inner, has_guard, w);
                } else if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
            }
            (Pat::Slice { prefix, middle, suffix }, _) => {
                let t = self.resolve(place.ty);
                let is_array = matches!(self.kind(t), TyKind::Array(..));
                let rest_only = prefix.is_empty() && suffix.is_empty() && middle.is_some();
                if !is_array && !rest_only {
                    read(self, &place, w);
                }
                for &s in prefix.iter().chain(suffix.iter()).chain(middle.iter()) {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    sub.push(CProj::Index, ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Or(alts), _) => {
                for &s in alts {
                    self.cap_pat(place.clone(), s, has_guard, w);
                }
            }
            (Pat::Paren(inner), _) => self.cap_pat(place, *inner, has_guard, w),
            _ => {
                if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
            }
        }
    }

    /// rustc `is_multivariant_adt`.
    fn multivariant(&self, a: AdtId) -> bool {
        let adt = self.p.adt(a);
        adt.is_enum && adt.variants.len() > 1
    }

    // ---------- Calls ----------

    /// Facts about a closure type for calls and selection: its kind,
    /// inputs, and output. Closures of this body answer from the
    /// checker's own record; others from the registered program table.
    pub(super) fn closure_facts(&mut self, ct: Ty) -> Option<(ClosureKind, Vec<Ty>, Ty)> {
        let TyKind::Closure(def, _) = self.kind(ct) else { return None };
        if let Some(c) = self.closures.iter().find(|c| c.def == def) {
            return Some((c.kind, c.inputs.clone(), c.output));
        }
        // Another body's closure (an `impl Trait` hidden type revealed
        // here) that no check registered yet, when the discovery walk
        // checks this body before its definer: check this body again
        // after it, as for a generic definer's closures.
        let Some(g) = self.p.gx.closures.get(&def) else {
            self.out.closure_kind_pending = true;
            return None;
        };
        let (kind, inputs, output) = (g.kind, g.inputs.clone(), g.output);
        // A generic definer's hidden closure, revealed at a call: its
        // signature names the definer's params, which the call's args
        // give (`opaque_closure_args`). Calls at different args (`mk(1)`
        // and `mk(2.5)`) reveal different closure types: the call whose
        // revealed type is `ct` wins.
        // A lost method probe also revealed the call, at vars nothing
        // decides: the args that resolve win.
        let want = self.deep(ct);
        let mut found: Option<Vec<GenericArg>> = None;
        for (d, a, rt) in self.opaque_closure_args.clone() {
            if d != def {
                continue;
            }
            let args: Vec<GenericArg> = self.tys.args(a).to_vec();
            if self.deep(rt) == want {
                found = Some(args);
                break;
            }
            let resolved = args.iter().filter_map(|g| g.as_ty()).all(|t| {
                let t = self.deep(t);
                !self.tys.flags(t).contains_infer()
            });
            if resolved || found.is_none() {
                found = Some(args);
            }
        }
        if let Some(args) = found {
            let inputs = inputs.into_iter().map(|t| subst(&mut self.tys, t, &args)).collect();
            let output = subst(&mut self.tys, output, &args);
            return Some((kind, inputs, output));
        }
        Some((kind, inputs, output))
    }

    /// A call whose callee is a value, not a fn path: a closure (through
    /// any number of references), or a value of a type with an Fn
    /// bound (an abstract parameter in a template check).
    pub(super) fn value_call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span) -> Ty {
        let ct = self.expr(callee, None);
        // Function pointers and fn or constructor items call through
        // the value directly (fx-method-res / next), through at most
        // one reference layer, as lowering expects for `Indirect`.
        let mut peeled = self.resolve(ct);
        if let TyKind::Ref(_, _, inner) = self.kind(peeled) {
            peeled = self.resolve(inner);
        }
        // Deeper layers (`&&f`, `Box<fn()>`, `&mut &f`) autoderef to the
        // fn too, as rustc's callee autoderef does; lowering loads the
        // pointer through them.
        let deep = self.peel_to_fn(peeled);
        // A call through a trait fn value (`Into::into` in a local,
        // check/traitpath.rs): typed by the trait method's
        // signature, selected at body end.
        if let TyKind::FnDef(def, fargs) = self.kind(peeled)
            && self.is_trait_method_def(def)
            && let Some(tdef) = self.p.gx.index.trait_of_method(def).or_else(|| (def == generics::to_string_defs().1).then_some(generics::to_string_defs().0))
        {
            let Some((params, ret)) = self.callable_sig(peeled) else { return ERROR };
            let rec = self.p.gx.index.trait_record(tdef);
            let (name, n_trait) = match rec {
                Some(r) => (r.methods.iter().find(|(d, _)| *d == def).map(|(_, n)| *n), r.generics.params.len()),
                None if def == generics::to_string_defs().1 => (Some(self.p.interner.intern("to_string")), 1),
                None => (None, 0),
            };
            let Some(name) = name else { return ERROR };
            let full: Vec<GenericArg> = self.tys.args(fargs).to_vec();
            let tr_args = self.tys.intern_args(&full[..n_trait.min(full.len())]);
            let tr = TraitRef { def: tdef, args: tr_args, bindings: EMPTY_BINDINGS };
            self.deferred_trait_fn_calls.push((e, tr, name, full[n_trait.min(full.len())..].to_vec(), span));
            self.check_args(&params, args, span);
            return ret;
        }
        if let Some((r, peeled)) = self.callable_res(peeled).map(|r| (r, peeled)).or_else(|| self.callable_res(deep).map(|r| (r, deep))) {
            if let Res::Variant(a, _) = r
                && !self.p.adt(a).is_enum
            {
                self.check_ctor_vis(a, span);
            }
            let Some((params, ret)) = self.callable_sig(peeled) else { return ERROR };
            // A generic fn item calls its instance: the call site
            // records the item's args, as a path call does.
            if let (Res::Fn(f), TyKind::FnDef(_, fargs)) = (r, self.kind(peeled))
                && !self.tys.args(fargs).is_empty()
            {
                let fargs = self.tys.args(fargs).to_vec();
                let ei = self.ei(e);
                self.generic_sites.push((ei, f, fargs));
            }
            self.set_res(e, r);
            self.note_fn_shim_call(e, ct, peeled);
            self.check_args(&params, args, span);
            return ret;
        }
        let mut t = self.resolve(ct);
        let mut derefs: u8 = 0;
        // Smart pointers peeled on the way (`Box<F>`, `Rc<F>`): calls
        // go through the pointee, as `impl Fn for Box<F>` and the
        // callee autoderef do in rustc.
        let (mut via_box, mut via_rc, mut box_by_value, mut via_ref, mut via_shared) = (false, false, false, false, false);
        loop {
            match self.kind(t) {
                TyKind::Closure(def, _) => {
                    let Some((kind, inputs, output)) = self.closure_facts(t) else {
                        self.err("L0820", span, "this closure call is not supported yet", "Call the closure where it is defined.");
                        return ERROR;
                    };
                    // Through a smart pointer only an `Fn` closure is called:
                    // rustc picks `Fn for Box<F>` first, so a boxed FnMut or
                    // FnOnce closure is E0525 (`(*b)()` works), and an `Rc`
                    // gives only shared access (E0596).
                    // In an instance the template's bound already holds
                    // (`impl FnMut for Box<F>`), so an owned box calls
                    // its FnMut or FnOnce closure.
                    let instance_box = via_box && !via_rc && !via_shared && self.template_call_mode(e).is_some();
                    if (via_box || via_rc) && kind != ClosureKind::Fn && !instance_box {
                        for &a in args {
                            self.expr(a, None);
                        }
                        self.err(
                            "L0110",
                            span,
                            "expected a closure that implements `Fn`: a boxed or shared `FnMut` or `FnOnce` closure is not called this way",
                            "Call it through the pointee instead: `(*b)()`, or keep the closure unboxed.",
                        );
                        return ERROR;
                    }
                    // In an instance, a call keeps the Fn trait the
                    // template resolved it through (FnOnce consumes the
                    // closure even when it is Fn), as rustc's generic body.
                    // Behind a reference (`F = Box<&C>`, `&&C`, `Box<&mut C>`)
                    // the closure is called in place by its own kind:
                    // `&C: FnOnce` calls `C` by `Fn`, `&mut C` by `FnMut`.
                    // A call the opaque view made behind the same `&` layers
                    // (`r()` on `r: &impl FnOnce()`) goes through the opaque's
                    // bound, as in rustc: `FnOnce` moves out of `*r` (E0507)
                    // and `FnMut` borrows it mutably (E0596), whatever the
                    // hidden closure's kind. A `Copy` opaque copies `*r`
                    // out: an `Fn` closure gives the same call in place.
                    let view = self.view_calls.get(&e).copied().filter(|v| via_ref && v.refs == derefs);
                    let mode = match view {
                        Some(v) if v.kind == ClosureKind::FnOnce && v.copy => {
                            if kind != ClosureKind::Fn {
                                self.err("L0820", span, "this closure call is not supported yet", "Call the closure where it is defined.");
                                return ERROR;
                            }
                            kind
                        }
                        Some(v) => v.kind,
                        None if via_ref => kind,
                        None => self.template_call_mode(e).or_else(|| self.view_calls.get(&e).map(|v| v.kind)).unwrap_or(kind),
                    };
                    self.out.closure_calls.push((e, mode));
                    self.set_res(e, Res::ClosureCall { kind: mode, derefs });
                    self.check_args(&inputs, args, span);
                    return output;
                }
                TyKind::Ref(_, m, inner) if derefs < 8 => {
                    derefs += 1;
                    via_ref = true;
                    via_shared |= m == Mut::Shared;
                    t = self.resolve(inner);
                }
                TyKind::Adt(..) if derefs < 8 && self.callee_smart_elem(t).is_some_and(|e| self.reaches_closure(e)) => {
                    if self.tys.rc_elem(t).is_some() || arc_elem(&self.tys, t).is_some() {
                        via_rc = true;
                    } else {
                        via_box = true;
                    }
                    // A `Box<dyn FnOnce>` called by value moves the box.
                    box_by_value = via_box && derefs == 0;
                    derefs += 1;
                    t = self.callee_smart_elem(t).map_or(ERROR, |e| self.resolve(e));
                }
                // A `dyn Fn`-family value calls its vtable's one entry
                // (ARCH 2.8, 2.9): through `&`/`Box`/`Rc` for `Fn`,
                // through `&mut` or an owned `Box` for `FnMut`, and only
                // by value through `Box` for `FnOnce` (the entry consumes
                // the value and frees the box).
                TyKind::Dyn(..) if self.dyn_fn_parts(t).is_some() => {
                    let (tdef, tuple, out) = self.dyn_fn_parts(t).unwrap();
                    let lang = self.p.gx.lang;
                    let tuple = self.resolve(tuple);
                    let inputs: Vec<Ty> = match self.kind(tuple) {
                        TyKind::Tuple(ts) => self.tys.tys_of(ts).to_vec(),
                        _ => Vec::new(),
                    };
                    let (kind, autoref) = if tdef == lang.fn_ {
                        (ClosureKind::Fn, Autoref::Ref)
                    } else if tdef == lang.fn_mut {
                        (ClosureKind::FnMut, Autoref::RefMut)
                    } else {
                        (ClosureKind::FnOnce, Autoref::None)
                    };
                    let bad = match kind {
                        ClosureKind::FnOnce if !(box_by_value && derefs == 1) => {
                            Some("a `dyn FnOnce` is called only by value, through a `Box<dyn FnOnce>` it consumes")
                        }
                        ClosureKind::FnMut if via_rc => Some("a `dyn FnMut` behind an `Rc` cannot be borrowed as mutable"),
                        _ => None,
                    };
                    if let Some(why) = bad {
                        for &a in args {
                            self.expr(a, None);
                        }
                        self.err("L0110", span, why, "Own the closure in a `Box`, or take `&mut dyn FnMut` for repeated calls.");
                        return ERROR;
                    }
                    let derefs = if kind == ClosureKind::FnOnce { 0 } else { derefs };
                    let slot = crate::check::object::VT_HEADER;
                    self.set_res(e, Res::DynMethod { owner: tdef, cand: 0, slot, derefs, autoref });
                    self.check_args(&inputs, args, span);
                    return out;
                }
                TyKind::Infer(v) if !v.is_int() && !v.is_float() => {
                    self.err("L0610", span, "type annotations needed: the type of this callee must be known here", "Annotate the callee's type.");
                    return ERROR;
                }
                TyKind::Error => return ERROR,
                // A type parameter or projection in a template check
                // calls through its Fn-family bound: Fn, else FnMut,
                // else FnOnce (rustc's order), lowered as a call of the
                // bound's method with the callee as receiver.
                TyKind::Param(_) | TyKind::Projection(..) | TyKind::Opaque(..) => {
                    let Some((stub, autoref, params, ret)) = self.fn_bound_call(t) else {
                        for &a in args {
                            self.expr(a, None);
                        }
                        let tn = self.tn(t);
                        self.err(
                            "L0114",
                            span,
                            format!("`{tn}` is not a function: its bounds have no `Fn`, `FnMut`, or `FnOnce`"),
                            "Add an `Fn` bound to the type parameter.",
                        );
                        return ERROR;
                    };
                    let kind = match autoref {
                        Autoref::Ref | Autoref::SliceRef => ClosureKind::Fn,
                        Autoref::RefMut | Autoref::SliceRefMut => ClosureKind::FnMut,
                        Autoref::None => ClosureKind::FnOnce,
                    };
                    self.out.closure_calls.push((e, kind));
                    self.check_args(&params, args, span);
                    self.set_res(e, Res::Method { f: stub, derefs, autoref });
                    return self.normalize_here(ret);
                }
                _ => {
                    for &a in args {
                        self.expr(a, None);
                    }
                    let tn = self.tn(t);
                    self.err("L0114", span, format!("`{tn}` is not callable"), "Call a function, a closure, or a value with an Fn bound.");
                    return ERROR;
                }
            }
        }
    }

    /// True when `t`, through references and smart pointers, is a
    /// closure or a trait object: what a smart pointer to it calls
    /// (`Box<F>`, `Box<&F>`, `Box<&mut F>`, and `Box<&Box<F>>` implement
    /// the Fn traits `F` gives them).
    fn reaches_closure(&self, mut t: Ty) -> bool {
        for _ in 0..8 {
            match self.kind(self.resolve(t)) {
                TyKind::Closure(..) | TyKind::Dyn(..) => return true,
                // A type parameter (or opaque) with an Fn bound behind a
                // smart pointer (`Arc<F>`): the loop calls it through
                // `fn_bound_call`.
                TyKind::Param(_) | TyKind::Projection(..) | TyKind::Opaque(..) => return true,
                TyKind::Ref(_, _, inner) => t = inner,
                _ => match self.callee_smart_elem(self.resolve(t)) {
                    Some(e) => t = e,
                    None => return false,
                },
            }
        }
        false
    }

    /// The pointee of a `Box`, `Rc`, guard, or `Arc` callee (autoderef
    /// to the callable).
    fn callee_smart_elem(&self, t: Ty) -> Option<Ty> {
        self.tys.smart_elem(t).or_else(|| arc_elem(&self.tys, t))
    }

    /// `t` through references and smart pointers down to a fn pointer
    /// or fn item; `t` itself when it does not reach one.
    fn peel_to_fn(&self, t: Ty) -> Ty {
        let mut d = t;
        for _ in 0..8 {
            d = match self.kind(d) {
                TyKind::FnPtr(_) | TyKind::FnDef(..) => return d,
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => match self.tys.smart_elem(d) {
                    Some(e) => self.resolve(e),
                    None => return t,
                },
            };
        }
        t
    }

    /// The call mode a template's abstract check recorded for this call.
    /// Records a call of a primitive method item (`u32::ilog2`) through
    /// an Fn-family bound in an instance (`fn_shim_calls`). rustc calls
    /// the item through its shim's Fn trait method: the template's, or
    /// `call` behind a `&` and `call_mut` behind a `&mut` (core's
    /// `impl Fn* for &F` and `&mut F` forward to those); a `Box` keeps
    /// the method. A direct call of the item value is not through a
    /// bound and keeps the call's own location.
    fn note_fn_shim_call(&mut self, e: ExprId, ct: Ty, item: Ty) {
        let Some(mut mode) = self.template_call_mode(e) else { return };
        if !self.is_prim_item(item) {
            return;
        }
        let mut t = self.resolve(ct);
        while t != item {
            match self.kind(t) {
                TyKind::Ref(_, m, inner) => {
                    mode = if m.is_mut() { ClosureKind::FnMut } else { ClosureKind::Fn };
                    t = self.resolve(inner);
                }
                _ => match self.tys.boxed_elem(t) {
                    Some(inner) => t = self.resolve(inner),
                    None => break,
                },
            }
        }
        let line = match mode {
            ClosureKind::Fn => 79,
            ClosureKind::FnMut => 166,
            ClosureKind::FnOnce => 250,
        };
        self.out.fn_shim_calls.push((e, line));
    }

    fn template_call_mode(&self, e: ExprId) -> Option<ClosureKind> {
        let p = self.p;
        if p.gx.fn_class.get(self.fid.0 as usize) != Some(&generics::FnClass::Instance) {
            return None;
        }
        let template = p.gx.instances.get(&self.fid)?.template_local?;
        p.gx.template_calls.get(&(template, e)).copied()
    }

    /// Builtin Fn-family selection for a closure Self type (the
    /// `SolveCx::closure_select` hook). An input that is still an open
    /// projection (`<X as TryInto<?T>>::Error` before a later use binds
    /// `?T`) is ambiguous: the queued obligation asks again once it is
    /// known, instead of a no against a type it cannot compare yet.
    pub(super) fn closure_select_impl(&mut self, obl: TraitRef) -> Option<Selection> {
        let lang = self.p.gx.lang;
        if !lang.is_fn_family(obl.def) {
            return None;
        }
        let args: Vec<GenericArg> = self.tys.args(obl.args).to_vec();
        let self_ty = self.deep(args.first()?.as_ty()?);
        let (kind, inputs) = match self.fn_like_facts(self_ty, 0) {
            Some((kind, inputs, _)) => (kind, inputs),
            // An unsafe or `extern "C"` fn implements no Fn trait.
            None if matches!(self.kind(self_ty), TyKind::FnPtr(_) | TyKind::FnDef(..)) => return Some(Selection::NoImpl),
            None => return None,
        };
        let need = if obl.def == lang.fn_ {
            ClosureKind::Fn
        } else if obl.def == lang.fn_mut {
            ClosureKind::FnMut
        } else {
            ClosureKind::FnOnce
        };
        if kind > need {
            return Some(Selection::NoImpl);
        }
        let want = args.get(1).and_then(|g| g.as_ty()).unwrap_or(UNIT);
        let want = self.resolve(want);
        // `Fn()` sugar builds an empty tuple; `()` is the same type.
        if inputs.is_empty() {
            let ok = match self.kind(want) {
                TyKind::Unit => true,
                TyKind::Tuple(ts) => self.tys.tys_of(ts).is_empty(),
                _ => {
                    let ts = self.tys.intern_tys(&[]);
                    let empty = self.tys.intern(TyKind::Tuple(ts));
                    self.unify(want, empty)
                }
            };
            return Some(if ok { Selection::Builtin } else { Selection::NoImpl });
        }
        let ts = self.tys.intern_tys(&inputs);
        let tuple = self.tys.intern(TyKind::Tuple(ts));
        let snap = self.snapshot_vars();
        if self.unify(want, tuple) {
            return Some(Selection::Builtin);
        }
        self.rollback_vars(snap);
        // Either side may be the open one: the fn value's own input too
        // (`Cow::Owned` takes `<?B as ToOwned>::Owned` until the output
        // type binds `?B`).
        let open = |cx: &mut Self, t: Ty| {
            let t = cx.deep(t);
            let flags = cx.tys.flags(t);
            flags.contains_projection() && flags.contains_infer()
        };
        Some(if open(self, want) || open(self, tuple) { Selection::Ambiguous } else { Selection::NoImpl })
    }

    /// The fn pointer two branch types join as when each is a closure
    /// that captures nothing (or one of them is a plain fn item or
    /// already a fn pointer) and the signatures agree: rustc's LUB
    /// special case. None otherwise, or for one closure type.
    pub(super) fn closure_lub(&mut self, a: Ty, b: Ty) -> Option<Ty> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return None;
        }
        let sig = |cx: &mut Self, t: Ty| -> Option<(Vec<Ty>, Ty)> {
            match cx.kind(t) {
                TyKind::Closure(_, caps) if cx.tys.args(caps).is_empty() => cx.closure_facts(t).map(|(_, i, o)| (i, o)),
                TyKind::FnPtr(_) => cx.callable_sig(t),
                TyKind::FnDef(..) if cx.reifies(t) => cx.callable_sig(t),
                _ => None,
            }
        };
        if !matches!(self.kind(a), TyKind::Closure(..)) && !matches!(self.kind(b), TyKind::Closure(..)) {
            return None;
        }
        let ((ia, oa), (ib, ob)) = (sig(self, a)?, sig(self, b)?);
        if ia.len() != ib.len() {
            return None;
        }
        let snap = self.snapshot_vars();
        let ok = ia.iter().zip(&ib).all(|(&x, &y)| self.unify(x, y))
            && self.unify(oa, ob)
            && !self.closure_has_free_ref_arg(a)
            && !self.closure_has_free_ref_arg(b);
        if !ok {
            self.rollback_vars(snap);
            return None;
        }
        // A closure whose output is not the input's (`bound_output`
        // None: no expected signature, or one over a type param) has a
        // free output region in rustc, which a closure that captures
        // nothing can only fill with `'static` borrows. rustc's join
        // keeps the first side's signature and needs the second to be a
        // subtype of it (`lub_out`): a free or `'static` output then a
        // tied one is E0308; a free join returns `'static` there, so it
        // meets no bound whose output is the input's.
        let out = self.deep(oa);
        if holds_region_slots(&self.p.gx.adt_lifetimes, &self.tys, out) {
            match self.lub_out(a, b) {
                Some(true) => {}
                Some(false) => {
                    if let Some(st) = static_output(&self.p.gx.adt_lifetimes, &mut self.tys, out) {
                        return Some(self.fn_ptr_ty(&ia, st));
                    }
                    self.rollback_vars(snap);
                    return None;
                }
                None => {
                    self.rollback_vars(snap);
                    return None;
                }
            }
        }
        Some(self.fn_ptr_ty(&ia, oa))
    }

    /// rustc's join of two callables whose outputs hold regions, as fn
    /// pointers: it keeps the earlier side's signature `a`, and the later
    /// side `b` must be a subtype of it. Some(true): the joined output is
    /// the input's (`a` tied); Some(false): it is not (`a` free or
    /// `'static`, `b` too); None: `b` ties where `a` does not (rustc
    /// E0308), or a side's output is a mix or unknown.
    pub(super) fn lub_out(&self, a: Ty, b: Ty) -> Option<bool> {
        match (self.out_tied(a)?, self.out_tied(b)?) {
            (true, _) => Some(true),
            (false, false) => Some(false),
            (false, true) => None,
        }
    }

    /// Whether callable `t`'s output regions are its input's: Some(true)
    /// for a closure with a tied `bound_output`, an elided fn pointer, a
    /// fn item whose output lifetimes are late-bound input ones;
    /// Some(false) for a closure with a free output, a fn item or pointer
    /// returning `'static` or an early-bound or output-only lifetime.
    /// None for a mix, or no signature.
    pub(super) fn out_tied(&self, t: Ty) -> Option<bool> {
        let p = self.p;
        let all = |v: &[bool]| if v.iter().all(|&x| x) { Some(true) } else if v.iter().all(|&x| !x) { Some(false) } else { None };
        match self.kind(self.resolve(t)) {
            TyKind::Closure(def, _) => Some(match self.closures.iter().find(|c| c.def == def) {
                Some(c) => c.bound_output.is_some(),
                None => p.gx.closures.get(&def)?.bound_output.is_some(),
            }),
            TyKind::FnPtr(s) => {
                let s = self.tys.sig(s).value;
                if s.free_slots != 0 {
                    return None;
                }
                let mut rs = Vec::new();
                crate::borrowck::regions_of(&self.tys, s.output, &mut rs);
                all(&rs.iter().map(|r| *r != Region::Static).collect::<Vec<bool>>())
            }
            TyKind::FnDef(def, _) => {
                let sig = p.local_def(def.hash).and_then(|l| p.regions.body_sig(p, l))?;
                let mut ins = Vec::new();
                for &t in &sig.params {
                    crate::borrowck::regions_of(&p.tys, t, &mut ins);
                }
                let mut outs = Vec::new();
                crate::borrowck::regions_of(&p.tys, sig.ret, &mut outs);
                let tied = |r: &Region| match *r {
                    Region::Param(k) => !sig.early.get(k as usize).copied().unwrap_or(false) && ins.contains(r),
                    _ => false,
                };
                all(&outs.iter().map(tied).collect::<Vec<bool>>())
            }
            _ => None,
        }
    }

    /// rustc's LUB of closures to a fn pointer at the coercion sites of
    /// an `if`, `match`, or labeled block: `prev` are the sites that
    /// joined to `a` so far and `be` is the site of `b`. Each site that
    /// is not a fn pointer yet gets the reify coercion. None (no join)
    /// when a side that needs the coercion has no known site, as for
    /// earlier `break` values, so the caller reports the mismatch.
    pub(super) fn closure_lub_sites(&mut self, a: Ty, b: Ty, prev: &[ExprId], be: Option<ExprId>) -> Option<Ty> {
        let needs = |cx: &Self, t: Ty| !matches!(cx.kind(cx.resolve(t)), TyKind::FnPtr(_));
        if (needs(self, a) && prev.is_empty()) || (needs(self, b) && be.is_none()) {
            return None;
        }
        let fp = self.closure_lub(a, b)?;
        for &s in prev {
            let t = self.out.expr_ty[self.ei(s)];
            if self.out.coerce[self.ei(s)] == Coerce::None && !matches!(self.kind(self.resolve(t)), TyKind::FnPtr(_) | TyKind::Never) {
                self.coerce_expr(s, t, fp);
            }
        }
        if let Some(be) = be {
            self.coerce_expr(be, b, fp);
        }
        Some(fp)
    }

    /// True when a closure argument may hold a free (inferred, not
    /// higher-ranked) region: an unannotated argument of a closure whose
    /// argument regions are free (`ClosureInfo::free_args`, `|x| x` in a
    /// `let`), or one annotated with a named lifetime. rustc cannot make
    /// such a closure a higher-ranked `fn(&T)` pointer, and lust does not
    /// track which fn pointer slots are higher-ranked, so it never turns
    /// one into a fn pointer. An instance trusts its template check,
    /// where a type param holds no region.
    fn closure_has_free_ref_arg(&mut self, ct: Ty) -> bool {
        let TyKind::Closure(def, _) = self.kind(self.resolve(ct)) else { return false };
        if matches!(self.p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance)) {
            return false;
        }
        let (inputs, free_args, input_regions) = match self.closures.iter().find(|c| c.def == def) {
            Some(c) => (c.inputs.clone(), c.free_args.clone(), c.input_regions.clone()),
            None => match self.p.gx.closures.get(&def) {
                Some(g) => (g.inputs.clone(), g.free_args.clone(), g.input_regions.clone()),
                None => return false,
            },
        };
        let Some(free_args) = free_args else { return false };
        (0..inputs.len()).any(|i| {
            let free = !free_args.get(i).copied().unwrap_or(false);
            match input_regions.get(i).copied().flatten() {
                Some(r) => free && names_param_region(&self.tys, r),
                None => free && {
                    let t = self.deep(inputs[i]);
                    may_hold_region(&self.tys, t)
                },
            }
        })
    }

    /// True when a closure that captures nothing has a signature that
    /// unifies with the safe fn pointer type `ptr` (rustc's
    /// ClosureFnPointer coercion). A failed probe rolls back.
    pub(super) fn closure_ptr_unifies(&mut self, found: Ty, ptr: Ty) -> bool {
        let TyKind::Closure(_, caps) = self.kind(self.resolve(found)) else { return false };
        let TyKind::FnPtr(sig) = self.kind(self.resolve(ptr)) else { return false };
        let s = self.tys.sig(sig).value;
        if !self.tys.args(caps).is_empty() || s.is_unsafe || s.extern_c {
            return false;
        }
        let Some((_, inputs, output)) = self.closure_facts(found) else { return false };
        let fp = self.fn_ptr_ty(&inputs, output);
        let snap = self.snapshot_vars();
        // The free-region test runs after unification, which gives an
        // unannotated argument the pointer's type.
        if self.unify(fp, ptr) && !self.closure_has_free_ref_arg(found) {
            return true;
        }
        self.rollback_vars(snap);
        false
    }

    /// The output of a closure for `<C as FnOnce<A>>::Output`.
    pub(super) fn closure_output_impl(&mut self, assoc: DefId, self_ty: Ty) -> Option<Ty> {
        let lang = self.p.gx.lang;
        if Some(assoc) != lang.output_of(lang.fn_once) {
            return None;
        }
        self.fn_like_facts(self_ty, 0).map(|f| f.2)
    }

    /// The Fn-family facts of a callable type for selection: the
    /// strongest Fn trait it implements (as a closure kind), its inputs,
    /// and its output. Closures, safe fn items and pointers (ARCH 2.9),
    /// `dyn Fn`-family types, and core's forwarding impls: `&F` is `Fn`
    /// when `F: Fn`, `&mut F` is `FnMut` when `F: FnMut`, and `Box<F>`
    /// is what `F` is.
    fn fn_like_facts(&mut self, t: Ty, depth: u8) -> Option<(ClosureKind, Vec<Ty>, Ty)> {
        let lang = self.p.gx.lang;
        let t = self.deep(t);
        match self.kind(t) {
            TyKind::Closure(..) => self.closure_facts(t),
            TyKind::FnPtr(_) | TyKind::FnDef(..) => self.fn_value_sig(t).map(|(params, ret)| (ClosureKind::Fn, params, ret)),
            TyKind::Dyn(..) => {
                let (tdef, tuple, out) = self.dyn_fn_parts(t)?;
                let kind = if tdef == lang.fn_ {
                    ClosureKind::Fn
                } else if tdef == lang.fn_mut {
                    ClosureKind::FnMut
                } else {
                    ClosureKind::FnOnce
                };
                let inputs = match self.kind(self.resolve(tuple)) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).to_vec(),
                    _ => Vec::new(),
                };
                Some((kind, inputs, out))
            }
            TyKind::Ref(_, m, inner) if depth < 4 => {
                let (k, inputs, out) = self.fn_like_facts(inner, depth + 1)?;
                if m.is_mut() {
                    (k <= ClosureKind::FnMut).then_some((ClosureKind::FnMut, inputs, out))
                } else {
                    (k == ClosureKind::Fn).then_some((ClosureKind::Fn, inputs, out))
                }
            }
            // std's `impl<R, F: FnOnce() -> R> FnOnce<()> for
            // AssertUnwindSafe<F>` (check/unwind.rs).
            TyKind::Adt(..)
                if depth < 4 && self.tys.local_adt(t).is_some_and(|a| crate::check::unwind::is_assert_unwind_safe(self.p, a)) =>
            {
                let inner = self.tys.adt_first_ty_arg(t)?;
                let inner = self.deep(inner);
                let (_, inputs, out) = match self.kind(inner) {
                    // A type param with an Fn-family bound
                    // (`f: impl FnOnce() -> R` wrapped in `AssertUnwindSafe`).
                    // Not through `&F` or `Box<F>`: codegen calls only a
                    // direct param there.
                    TyKind::Param(_) | TyKind::Projection(..) | TyKind::Opaque(..) => {
                        let (_, _, inputs, out) = self.fn_bound_call(inner)?;
                        (ClosureKind::FnOnce, inputs, out)
                    }
                    _ => self.fn_like_facts(inner, depth + 1)?,
                };
                inputs.is_empty().then_some((ClosureKind::FnOnce, inputs, out))
            }
            TyKind::Adt(..) if depth < 4 => {
                let elem = self.tys.boxed_elem(t)?;
                self.fn_like_facts(elem, depth + 1)
            }
            _ => None,
        }
    }

    /// The signature a fn pointer, fn item, or tuple constructor value
    /// has as an `Fn` implementor: None for an unsafe or `extern "C"` fn
    /// (those implement no Fn trait).
    fn fn_value_sig(&mut self, t: Ty) -> Option<(Vec<Ty>, Ty)> {
        if let TyKind::FnPtr(sig) = self.kind(t) {
            let s = self.tys.sig(sig).value;
            if s.is_unsafe || s.extern_c {
                return None;
            }
        }
        if let TyKind::FnDef(def, _) = self.kind(t)
            && self.is_fn_item(t)
            && self.p.local_def(def.hash).is_some_and(|f| self.p.fn_def(f).qual.is_unsafe)
        {
            return None;
        }
        self.callable_sig(t)
    }
}

/// True when `a` is `b` or an ancestor of `b` (same root, `a`'s
/// projections a prefix of `b`'s).
fn is_ancestor(a: &CPlace, b: &CPlace) -> bool {
    a.root == b.root && a.projs.len() <= b.projs.len() && a.projs.iter().zip(&b.projs).all(|(x, y)| x.0 == y.0)
}

/// rustc `truncate_place_to_len_and_update_capture_kind`: a mutable
/// borrow whose dropped part dereferenced a `&mut` becomes unique.
fn truncate_place(pl: &mut CPlace, mode: &mut CaptureMode, len: usize, tys: &impl TyIntern) {
    if len >= pl.projs.len() {
        return;
    }
    if *mode == CaptureMode::MutRef
        && pl.projs[len..].iter().any(|(pr, before)| *pr == CProj::Deref && matches!(tys.kind(*before), TyKind::Ref(_, m, _) if m.is_mut()))
    {
        *mode = CaptureMode::UniqueRef;
    }
    pl.ty = pl.projs.get(len).map(|(_, before)| *before).unwrap_or(pl.ty);
    pl.projs.truncate(len);
}

/// rustc `restrict_capture_precision`: arrays and slices are captured
/// whole (truncate before any index).
fn restrict_capture_precision(mut pl: CPlace, mut mode: CaptureMode, tys: &impl TyIntern) -> (CPlace, CaptureMode) {
    if let Some(i) = pl.projs.iter().position(|(pr, _)| *pr == CProj::Index) {
        truncate_place(&mut pl, &mut mode, i, tys);
    }
    (pl, mode)
}

/// rustc `truncate_capture_for_optimization`: a place read through a
/// shared reference is captured as that reference's target.
fn truncate_for_optimization(mut pl: CPlace, mut mode: CaptureMode, tys: &impl TyIntern) -> (CPlace, CaptureMode) {
    if let Some(i) = pl.projs.iter().rposition(|(pr, _)| *pr == CProj::Deref)
        && matches!(tys.kind(pl.projs[i].1), TyKind::Ref(_, m, _) if !m.is_mut())
    {
        truncate_place(&mut pl, &mut mode, i + 1, tys);
    }
    (pl, mode)
}

/// True when a closure argument type may hold a region (see
/// `closure_has_free_ref_arg`): a reference, a dyn or opaque type, an
/// unresolved type (not a numeric literal's), or an Adt with a lifetime
/// argument, at any depth.
/// A type param holds none in a template.
/// `t` with every region `'static` (references, dyn object lifetimes,
/// Adt lifetime args): the output of a joined pointer of closures with
/// free outputs (`closure_lub`). None for a part that may hold a region
/// it cannot rewrite (a fn pointer, an opaque or param type).
pub(crate) fn static_output(lts: &crate::intern::FxMap<DefId, Vec<crate::intern::Sym>>, tys: &mut impl TyIntern, t: Ty) -> Option<Ty> {
    Some(match tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            let i = static_output(lts, tys, inner)?;
            tys.intern(TyKind::Ref(crate::ty::Region::Static, m, i))
        }
        TyKind::Dyn(b, _) => tys.intern(TyKind::Dyn(b, crate::ty::Region::Static)),
        TyKind::Tuple(ts) => {
            let elems = tys.tys_of(ts).to_vec().into_iter().map(|e| static_output(lts, tys, e)).collect::<Option<Vec<Ty>>>()?;
            let id = tys.intern_tys(&elems);
            tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let e = static_output(lts, tys, e)?;
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = static_output(lts, tys, e)?;
            tys.intern(TyKind::Slice(e))
        }
        // An Adt's lifetime args are not in check's types: no way to
        // write `'static` there.
        TyKind::Adt(_, a) if crate::borrowck::adt_region_count(lts, tys, t) > 0 && !tys.args(a).iter().any(|g| matches!(g, GenericArg::Lifetime(_))) => return None,
        TyKind::Adt(d, a) => {
            let args = tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => static_output(lts, tys, e).map(GenericArg::Ty),
                    GenericArg::Lifetime(_) => Some(GenericArg::Lifetime(crate::ty::Region::Static)),
                    x => Some(x),
                })
                .collect::<Option<Vec<GenericArg>>>()?;
            tys.mk_adt(d, &args)
        }
        _ if may_hold_region(tys, t) => return None,
        _ => t,
    })
}

/// True when `t` has region slots in borrowck's layout: `may_hold_region`,
/// or an Adt with lifetime params (check's types do not write those).
pub(crate) fn holds_region_slots(lts: &crate::intern::FxMap<DefId, Vec<crate::intern::Sym>>, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| holds_region_slots(lts, tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => holds_region_slots(lts, tys, e),
        TyKind::Adt(_, a) => {
            crate::borrowck::adt_region_count(lts, tys, t) > 0 || tys.args(a).iter().any(|g| matches!(g, GenericArg::Lifetime(_)) || g.as_ty().is_some_and(|e| holds_region_slots(lts, tys, e)))
        }
        _ => may_hold_region(tys, t),
    }
}

pub(crate) fn may_hold_region(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Infer(v) => !v.is_int() && !v.is_float(),
        TyKind::Ref(..) | TyKind::Dyn(..) | TyKind::Opaque(..) => true,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| may_hold_region(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => may_hold_region(tys, e),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| match *g {
            GenericArg::Lifetime(_) => true,
            GenericArg::Ty(e) => may_hold_region(tys, e),
            GenericArg::Const(_) => false,
        }),
        _ => false,
    }
}

/// True when an annotation's regioned type names a lifetime of the
/// enclosing fn (`|x: &'a T|`), which is a free region.
fn names_param_region(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(r, _, e) => matches!(r, crate::ty::Region::Param(_)) || names_param_region(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| names_param_region(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => names_param_region(tys, e),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| match *g {
            GenericArg::Lifetime(r) => matches!(r, crate::ty::Region::Param(_)),
            GenericArg::Ty(e) => names_param_region(tys, e),
            GenericArg::Const(_) => false,
        }),
        _ => false,
    }
}

/// The `T` of an `Arc<T>`.
fn arc_elem(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    (crate::ty::sync::sync_kind(tys, t) == Some(crate::ty::sync::SyncTy::Arc)).then(|| tys.adt_first_ty_arg(t)).flatten()
}
