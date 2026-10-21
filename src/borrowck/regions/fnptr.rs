// Fn pointer regions (W-BORROW3, docs/ARCH.md 5.6).
//
// A fn pointer type is elided (each input lifetime its own binder, an
// elided output the one input's), may write `&'static`, may share one
// `for<..>` binder lifetime among several slots (`FnSig::binders`:
// `for<'s> fn(&mut Ctx<'s>, &'s [u8]) -> Cow<'s, [u8]>`, one binder at
// all its slots), and may name one lifetime of the enclosing item
// (`fn(&mut Parser<'a>) -> Node`): `FnSig::free_slots` marks the
// signature slots that region fills, and a value of such a type has one
// region slot, that free region.
//
// One check proves a signature against another wherever a fn item, a fn
// pointer, a `dyn Fn*` type, or an `Fn*` bound meet (`sub_sigs`): the
// target's binders are placeholders (each its own unknown region), the
// source's binders (a fn's late-bound lifetimes, a fn pointer's elided
// ones) are existential, everything else is a region var of this body.
// Each slot relates by its variance (coercions) or both ways (trait
// matching: `dyn Fn*` and bounds). A placeholder may only outlive itself;
// a body region that must outlive a placeholder must be `'static`; the
// rest become edges of the body (rustc's higher-ranked subtyping with
// universes, on the elided shapes lust allows).
use super::*;

/// One region of a signature in a proof (`sub_sigs`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum Node {
    /// A region var of this body (`'static` is 0).
    Var(u32),
    /// A source binder: some region the proof may pick.
    Late(u32),
    /// A target binder: any region at all.
    Ph(u32),
}

/// The free region of fn pointer type `t` (`FnSig::free_region`) when it
/// names one.
pub(crate) fn ptr_free(tys: &impl TyIntern, t: Ty) -> Option<Region> {
    match tys.kind(t) {
        TyKind::FnPtr(s) => {
            let s = tys.sig(s).value;
            (s.free_slots != 0).then_some(s.free_region)
        }
        _ => None,
    }
}

/// The region slots `adt_lifetimes`-aware counting gives an erased type,
/// paired with the regions regioned type `r` writes there (`Erased` where
/// it writes none), in the borrow checker's slot order. Check uses it to
/// find the free slots of a fn pointer type. False when the shapes differ.
pub(crate) fn paired_slot_regions(
    adt_lifetimes: &FxMap<DefId, Vec<crate::intern::Sym>>,
    tys: &impl TyIntern,
    r: Ty,
    e: Ty,
    out: &mut Vec<Region>,
) -> bool {
    match (tys.kind(r), tys.kind(e)) {
        (TyKind::Ref(rr, rm, ri), TyKind::Ref(er, em, ei)) if rm == em => {
            if bound(rr) != bound(er) {
                return false;
            }
            if !bound(er) {
                out.push(rr);
            }
            paired_slot_regions(adt_lifetimes, tys, ri, ei, out)
        }
        (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
            let lts: Vec<Region> =
                tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g && *x != crate::ty::DYN_LATE { Some(*x) } else { None }).collect();
            for k in 0..adt_region_count(adt_lifetimes, tys, e) as usize {
                out.push(lts.get(k).copied().unwrap_or(Region::Erased));
            }
            let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
            let eargs: Vec<Ty> = tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
            rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| paired_slot_regions(adt_lifetimes, tys, x, y, out))
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (xs, ys) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
            xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| paired_slot_regions(adt_lifetimes, tys, x, y, out))
        }
        (TyKind::Array(a, _), TyKind::Array(b, _))
        | (TyKind::Slice(a), TyKind::Slice(b))
        | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => paired_slot_regions(adt_lifetimes, tys, a, b, out),
        (TyKind::Dyn(_, rr), TyKind::Dyn(_, er)) => {
            if bound(rr) != bound(er) {
                return false;
            }
            if !bound(er) {
                out.push(rr);
            }
            let (ra, ea) = (dyn_arg_tys(tys, r), dyn_arg_tys(tys, e));
            ra.len() == ea.len() && ra.into_iter().zip(ea).all(|(x, y)| paired_slot_regions(adt_lifetimes, tys, x, y, out))
        }
        (_, TyKind::FnPtr(_)) => {
            if let Some(f) = ptr_free(tys, e) {
                out.push(ptr_free(tys, r).unwrap_or(f));
            }
            matches!(tys.kind(r), TyKind::FnPtr(_))
        }
        _ => r == e || !has_slot_kinds(adt_lifetimes, tys, e),
    }
}

/// True when erased type `e` may have region slots (a conservative test
/// for `paired_slot_regions`' fallback).
fn has_slot_kinds(adt_lifetimes: &FxMap<DefId, Vec<crate::intern::Sym>>, tys: &impl TyIntern, e: Ty) -> bool {
    match tys.kind(e) {
        TyKind::Ref(..) | TyKind::Dyn(..) | TyKind::Closure(..) => true,
        TyKind::Adt(_, a) => {
            adt_region_count(adt_lifetimes, tys, e) > 0
                || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|t| has_slot_kinds(adt_lifetimes, tys, t)))
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&t| has_slot_kinds(adt_lifetimes, tys, t)),
        TyKind::Array(x, _) | TyKind::Slice(x) | TyKind::RawPtr(_, x) => has_slot_kinds(adt_lifetimes, tys, x),
        TyKind::FnPtr(_) => ptr_free(tys, e).is_some(),
        _ => false,
    }
}

/// The vars `fn_nodes` gives one use of a fn's signature: one per
/// early-bound lifetime, and the slot vars of each type param.
struct SigNodes {
    early: FxMap<u32, u32>,
    tparams: FxMap<u32, Vec<u32>>,
}

/// True when regioned type `t` mentions a type param.
fn contains_param(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) => true,
        TyKind::Ref(_, _, x) | TyKind::Array(x, _) | TyKind::Slice(x) | TyKind::RawPtr(_, x) => contains_param(tys, x),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&x| contains_param(tys, x)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) | TyKind::Opaque(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|x| contains_param(tys, x)))
        }
        TyKind::FnPtr(s) => {
            let s = tys.sig(s).value;
            tys.tys_of(s.inputs).iter().any(|&x| contains_param(tys, x)) || contains_param(tys, s.output)
        }
        _ => false,
    }
}

/// Why a signature proof failed.
pub(super) enum SubFail {
    /// A target binder would have to outlive another region.
    NotGeneral,
}

impl Builder<'_, '_> {
    /// The nodes of fn pointer type `t` (this body's types), one per
    /// slot of the inputs and of the output: its free slots are `free`
    /// (a var), written `'static` is var 0, each other input slot a
    /// binder of its own (`Ph` for a target, `Late` for a source; ids
    /// from `base`), and each other output slot the one input slot's,
    /// except slots a type argument filled (`FnSig::out_substituted`, an
    /// output with no own slot written): a var each. None when an output
    /// slot has no one input to take.
    pub(super) fn ptr_nodes(&mut self, t: Ty, free: Option<u32>, target: bool, base: u32) -> Option<(Vec<Node>, Vec<Node>)> {
        let TyKind::FnPtr(s) = self.body.tys.kind(t) else { return None };
        let s = self.body.tys.sig(s).value;
        let ins_t: Vec<Ty> = self.body.tys.tys_of(s.inputs).to_vec();
        let free_node = |this: &mut Self| Node::Var(free.unwrap_or_else(|| this.fresh()));
        let in_rs: Vec<Vec<Region>> = ins_t.iter().map(|&it| self.sig_slot_regions(it)).collect();
        let out_rs = self.sig_slot_regions(s.output);
        // A shared binder lifetime (`FnSig::binders`) is one binder at all
        // its slots: the node of its first slot.
        let n_slots = in_rs.iter().map(Vec::len).sum::<usize>() + out_rs.len();
        let groups = s.binder_groups(n_slots);
        if s.binders != 0 && groups.is_none() {
            return None;
        }
        let group_of = |j: u32| groups.as_ref().map_or(0, |g| g[j as usize]);
        let mut group_nodes: FxMap<u8, Node> = FxMap::default();
        let mut j = 0u32;
        let mut ins = Vec::new();
        for rs in in_rs {
            for r in rs {
                let g = group_of(j);
                ins.push(if s.free_slots >> j & 1 == 1 {
                    free_node(self)
                } else if r == Region::Static {
                    Node::Var(0)
                } else if let Some(&n) = group_nodes.get(&g).filter(|_| g != 0) {
                    n
                } else {
                    let n = if target { Node::Ph(base + j) } else { Node::Late(base + j) };
                    if g != 0 {
                        group_nodes.insert(g, n);
                    }
                    n
                });
                j += 1;
            }
        }
        let mut outs = Vec::new();
        // Where a substitution moved written own slots (`fn(&u8) -> (T,
        // &u8)`) their places are unknown: the one input's, as before.
        let substituted = s.out_substituted(out_rs.len()) && s.own_out == 0;
        for r in out_rs {
            let g = group_of(j);
            outs.push(if s.free_slots >> j & 1 == 1 {
                free_node(self)
            } else if r == Region::Static {
                Node::Var(0)
            } else if g != 0 {
                *group_nodes.get(&g)?
            } else if substituted || ins.is_empty() {
                // With no input slot an output slot is no binder's either
                // (`fn() -> T` with `T = Vec<&'static str>`).
                Node::Var(self.fresh())
            } else if let [one] = ins[..] {
                one
            } else {
                return None;
            });
            j += 1;
        }
        Some((ins, outs))
    }

    /// The nodes of a fn's region signature as a source, one per slot of
    /// its params and of its return (paired with erased types `ins` and
    /// `out`): `'static` is var 0, an early-bound lifetime a fresh var of
    /// this use (one per lifetime; the fn's own `'a: 'b` facts become
    /// edges), a late-bound one a source binder, and the slots a type
    /// param of the fn fills (`id::<&u8>`) vars of this use, one set per
    /// param: a type param is fixed outside the pointer's binder, so it
    /// cannot take a binder's region (rustc E0308, "one type is more
    /// general than the other"). None when the shapes do not pair.
    pub(super) fn fn_nodes(&mut self, sig: &RegionSig, ins: &[Ty], out: Ty) -> Option<(Vec<Node>, Vec<Node>)> {
        if sig.params.len() != ins.len() {
            return None;
        }
        let mut cx = SigNodes { early: FxMap::default(), tparams: FxMap::default() };
        let mut in_nodes = Vec::new();
        for (&r, &e) in sig.params.iter().zip(ins) {
            if !self.sig_side_nodes(sig, &mut cx, r, e, &mut in_nodes) {
                return None;
            }
        }
        let mut out_nodes = Vec::new();
        if !self.sig_side_nodes(sig, &mut cx, sig.ret, out, &mut out_nodes) {
            return None;
        }
        let early = cx.early;
        for &(a, b) in &sig.facts {
            if let (Region::Param(x), y) = (a, b) {
                let (Some(&vx), vy) = (
                    early.get(&x),
                    match y {
                        Region::Static => Some(0),
                        Region::Param(k) => early.get(&k).copied(),
                        _ => None,
                    },
                ) else {
                    continue;
                };
                if let Some(vy) = vy {
                    self.edge(vx, vy);
                }
            }
        }
        Some((in_nodes, out_nodes))
    }

    /// One param or the return of `fn_nodes`: regioned type `r` of the
    /// fn's signature walked with erased type `e` of this use, pushing one
    /// node per slot of `e`. False when the shapes do not pair.
    fn sig_side_nodes(&mut self, sig: &RegionSig, cx: &mut SigNodes, r: Ty, e: Ty, out: &mut Vec<Node>) -> bool {
        let p = self.p;
        let (tys, et) = (&p.tys, &self.body.tys);
        match (tys.kind(r), et.kind(e)) {
            (TyKind::Param(j), _) => {
                let n = self.sc.slots(e) as usize;
                let vs = match cx.tparams.get(&j.0) {
                    Some(vs) => vs.clone(),
                    None => {
                        let vs: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                        cx.tparams.insert(j.0, vs.clone());
                        vs
                    }
                };
                out.extend(vs.iter().map(|&v| Node::Var(v)));
                vs.len() == n
            }
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(_, em, ei)) if rm == em => {
                let n = self.sig_region_node(sig, cx, rr);
                out.push(n);
                self.sig_side_nodes(sig, cx, ri, ei, out)
            }
            (TyKind::Adt(..), _) if !contains_param(tys, r) => self.sig_side_flat(sig, cx, r, e, out),
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g { Some(*x) } else { None }).collect();
                for k in 0..adt_regions(p, et, e) as usize {
                    let n = match lts.get(k) {
                        Some(&x) => self.sig_region_node(sig, cx, x),
                        None => return false,
                    };
                    out.push(n);
                }
                let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = self.body.tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| self.sig_side_nodes(sig, cx, x, y, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (tys.tys_of(a).to_vec(), et.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.sig_side_nodes(sig, cx, x, y, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.sig_side_nodes(sig, cx, a, b, out)
            }
            _ => self.sig_side_flat(sig, cx, r, e, out),
        }
    }

    /// `sig_side_nodes` for a type without type params of the fn: its
    /// written regions, one per slot of `e`.
    fn sig_side_flat(&mut self, sig: &RegionSig, cx: &mut SigNodes, r: Ty, e: Ty, out: &mut Vec<Node>) -> bool {
        let mut rs = Vec::new();
        regions_of(&self.p.tys, r, &mut rs);
        if rs.len() != self.sc.slots(e) as usize {
            return false;
        }
        for r in rs {
            let n = self.sig_region_node(sig, cx, r);
            out.push(n);
        }
        true
    }

    /// The node of region `r` of a fn's signature (`fn_nodes`).
    fn sig_region_node(&mut self, sig: &RegionSig, cx: &mut SigNodes, r: Region) -> Node {
        match r {
            Region::Static => Node::Var(0),
            Region::Param(k) if sig.early.get(k as usize) == Some(&true) => match cx.early.get(&k) {
                Some(&v) => Node::Var(v),
                None => {
                    let v = self.fresh();
                    cx.early.insert(k, v);
                    Node::Var(v)
                }
            },
            Region::Param(k) => Node::Late(k),
            _ => Node::Late(10_000 + self.fresh()),
        }
    }

    /// The variance of each slot of the inputs (contravariant) and the
    /// output (covariant) of erased signature `ins -> out`.
    pub(super) fn sig_variances(&mut self, ins: &[Ty], out: Ty) -> (Vec<Variance>, Vec<Variance>) {
        let (mut vi, mut vo) = (Vec::new(), Vec::new());
        for &t in ins {
            self.sc.each_slot(t, Variance::Contra, 0, &mut |_, v| vi.push(v));
        }
        self.sc.each_slot(out, Variance::Co, 0, &mut |_, v| vo.push(v));
        (vi, vo)
    }

    /// Proves `src <: dst` for two signatures given as nodes per slot (or
    /// their equality under `invariant`: trait matching), adding the edges
    /// it needs between this body's vars. See the file comment.
    pub(super) fn sub_sigs(
        &mut self,
        src: &(Vec<Node>, Vec<Node>),
        dst: &(Vec<Node>, Vec<Node>),
        var: &(Vec<Variance>, Vec<Variance>),
        invariant: bool,
    ) -> Result<(), SubFail> {
        if src.0.len() != dst.0.len() || src.1.len() != dst.1.len() || var.0.len() != src.0.len() || var.1.len() != src.1.len() {
            return Err(SubFail::NotGeneral);
        }
        // `x: y` (x outlives y) for each slot by its variance.
        let mut cons: Vec<(Node, Node)> = Vec::new();
        let pairs = src.0.iter().zip(&dst.0).zip(&var.0).chain(src.1.iter().zip(&dst.1).zip(&var.1));
        for ((&s, &d), &v) in pairs {
            match if invariant { Variance::Inv } else { v } {
                Variance::Co => cons.push((s, d)),
                Variance::Contra => cons.push((d, s)),
                Variance::Inv => {
                    cons.push((s, d));
                    cons.push((d, s));
                }
                Variance::Bi => {}
            }
        }
        // Close over the source binders: a binder is the least region its
        // lower bounds allow, so whatever must outlive it must outlive them.
        let mut implied: Vec<(Node, Node)> = Vec::new();
        for &(x, _) in &cons {
            if matches!(x, Node::Late(_)) {
                continue;
            }
            let mut seen: Vec<Node> = vec![x];
            let mut work: Vec<Node> = vec![x];
            while let Some(n) = work.pop() {
                for &(a, b) in &cons {
                    if a == n && !seen.contains(&b) {
                        seen.push(b);
                        if matches!(b, Node::Late(_)) {
                            work.push(b);
                        } else {
                            implied.push((x, b));
                        }
                    }
                }
            }
        }
        for (x, y) in implied {
            match (x, y) {
                _ if x == y => {}
                (Node::Var(0), _) => {}
                (Node::Ph(_), _) => return Err(SubFail::NotGeneral),
                (Node::Var(a), Node::Ph(_)) => self.edge(a, 0),
                (Node::Var(a), Node::Var(b)) => self.edge(a, b),
                _ => {}
            }
        }
        Ok(())
    }

    /// L0110 (rustc E0308): a fn item or fn pointer coerced to a fn pointer
    /// type that is more general than it.
    pub(super) fn ptr_not_general(&mut self) {
        self.errs.push(Diag::new(
            "L0110",
            self.span,
            "this fn is not as general as the fn pointer type it becomes: their lifetimes differ",
            "Write the same lifetimes in both signatures, or elide them in the fn.",
        ));
    }

    /// A fn item `f` coerced to fn pointer type `ptr` (`Rvalue::FnValue`),
    /// stored to a place whose slots are `dv`: the fn's signature must
    /// prove the pointer's (`sub_sigs`), and the pointer's free region is
    /// the place's slot.
    pub(super) fn fn_item_to_ptr(&mut self, f: LocalDefId, ptr: Ty, dv: &[u32]) {
        let TyKind::FnPtr(s) = self.body.tys.kind(ptr) else { return };
        let s = self.body.tys.sig(s).value;
        let ins: Vec<Ty> = self.body.tys.tys_of(s.inputs).to_vec();
        let free = if s.free_slots != 0 { dv.first().copied() } else { None };
        let sig = match self.callee(f) {
            Callee::Sig(sig) => sig.clone(),
            _ => {
                if s.free_slots != 0 {
                    self.ptr_no_sig();
                }
                return;
            }
        };
        let Some(dst) = self.ptr_nodes(ptr, free, true, 0) else { return };
        let Some(src) = self.fn_nodes(&sig, &ins, s.output) else {
            if s.free_slots != 0 {
                self.ptr_no_sig();
            }
            return;
        };
        let var = self.sig_variances(&ins, s.output);
        if self.sub_sigs(&src, &dst, &var, false).is_err() {
            self.ptr_not_general();
        }
    }

    /// L0203: a fn without a region signature (a constructor, a std fn)
    /// coerced to a fn pointer type that names a lifetime.
    fn ptr_no_sig(&mut self) {
        self.errs.push(Diag::new(
            "L0203",
            self.span,
            "this fn cannot become a fn pointer type that names a lifetime yet",
            "Wrap it in a fn with written lifetimes, or elide the lifetime in the fn pointer type.",
        ));
    }

    /// A fn pointer value of type `a` (free slot var `fa`) flowing into one
    /// of type `b` (`fb`) at variance `v` (`walk`): the coercion proof, in
    /// the direction the variance gives. Invariant means a subtype both
    /// ways: `for<'r> fn(&'r u8)` and `fn(&'b u8)` are two types there
    /// (rustc E0308 "one type is more general than the other").
    pub(super) fn ptr_to_ptr(&mut self, a: Ty, fa: Option<u32>, b: Ty, fb: Option<u32>, v: Variance) {
        let dirs: &[(bool, bool)] = match v {
            Variance::Co => &[(false, false)],
            Variance::Contra => &[(true, false)],
            Variance::Inv => &[(false, true), (true, true)],
            Variance::Bi => &[],
        };
        for &(swap, invariant) in dirs {
            let ((s, fs), (d, fd)) = if swap { ((b, fb), (a, fa)) } else { ((a, fa), (b, fb)) };
            let (Some(src), Some(dst)) = (self.ptr_nodes(s, fs, false, 0), self.ptr_nodes(d, fd, true, 0)) else {
                self.ptr_not_general();
                return;
            };
            let TyKind::FnPtr(sig) = self.body.tys.kind(d) else { return };
            let sig = self.body.tys.sig(sig).value;
            let ins: Vec<Ty> = self.body.tys.tys_of(sig.inputs).to_vec();
            let var = self.sig_variances(&ins, sig.output);
            if self.sub_sigs(&src, &dst, &var, invariant).is_err() {
                self.ptr_not_general();
                return;
            }
        }
    }

    /// A fn pointer value of type `src` (free slot var `free`) where a `dyn
    /// Fn*` type or a bound wants signature `dst` (nodes, from `base` on):
    /// trait matching, so the two must agree slot by slot once the
    /// pointer's binders are picked (rustc "not general enough").
    pub(super) fn ptr_matches(&mut self, src: Ty, free: Option<u32>, dst: &(Vec<Node>, Vec<Node>)) -> bool {
        let Some(s) = self.ptr_nodes(src, free, false, 1_000) else { return false };
        let var = (vec![Variance::Inv; s.0.len()], vec![Variance::Inv; s.1.len()]);
        self.sub_sigs(&s, dst, &var, true).is_ok()
    }

    /// The nodes of a `dyn Fn*(I..) -> O` target with places `pin` and
    /// `pout` (`dyn_positions`, R11): each late-bound input place a
    /// placeholder, each other place its var, each late-bound output place
    /// the one late-bound input's.
    pub(super) fn dyn_nodes(&mut self, pin: &[Pos], pout: &[Pos]) -> Option<(Vec<Node>, Vec<Node>)> {
        let t_in: Vec<Node> = pin
            .iter()
            .enumerate()
            .map(|(j, p)| match *p {
                Pos::Var(v) => Node::Var(v),
                Pos::Late => Node::Ph(j as u32),
            })
            .collect();
        let lates: Vec<Node> = t_in.iter().copied().filter(|n| matches!(n, Node::Ph(_))).collect();
        let mut t_out = Vec::new();
        for p in pout {
            t_out.push(match (*p, &lates[..]) {
                (Pos::Var(v), _) => Node::Var(v),
                (Pos::Late, [one]) => *one,
                _ => return None,
            });
        }
        Some((t_in, t_out))
    }

    /// The nodes of a callee's regioned `Fn*` bound `g` as a target, paired
    /// with the erased types `ins -> out` of the source: an elided input
    /// lifetime (`Region::Bound`) is a placeholder, an elided output the
    /// one elided input's, `'static` var 0, the callee's lifetime `k` the
    /// call's `univ[k]`. None when the shapes do not pair (type params).
    pub(super) fn bound_nodes(&mut self, g: &FnBound, ins: &[Ty], out: Ty, univ: &[u32]) -> Option<(Vec<Node>, Vec<Node>)> {
        let p = self.p;
        if g.inputs.len() != ins.len() {
            return None;
        }
        let node = |r: Region, j: u32, one: Option<Node>| match r {
            Region::Static => Some(Node::Var(0)),
            Region::Param(k) => univ.get(k as usize).map(|&u| Node::Var(u)),
            Region::Bound(_) => Some(one.unwrap_or(Node::Ph(j))),
            _ => None,
        };
        let mut t_in = Vec::new();
        let mut j = 0u32;
        for (&r, &e) in g.inputs.iter().zip(ins) {
            let mut rs = Vec::new();
            regions_of(&p.tys, r, &mut rs);
            if rs.len() != self.sc.slots(e) as usize {
                return None;
            }
            for r in rs {
                t_in.push(node(r, j, None)?);
                j += 1;
            }
        }
        let binders: Vec<Node> = t_in.iter().copied().filter(|n| matches!(n, Node::Ph(_))).collect();
        let mut rs = Vec::new();
        if let Some(o) = g.output {
            regions_of(&p.tys, o, &mut rs);
            // An output type param (`F: Fn(&u8) -> T`): the call fixes its
            // slots outside the bound's binder, a var each.
            if matches!(p.tys.kind(o), TyKind::Param(_)) {
                let n = self.sc.slots(out);
                return Some((t_in, (0..n).map(|_| Node::Var(self.fresh())).collect()));
            }
        }
        if rs.len() != self.sc.slots(out) as usize {
            return None;
        }
        let mut t_out = Vec::new();
        for r in rs {
            let one = if matches!(r, Region::Bound(_)) {
                match binders[..] {
                    [b] => Some(b),
                    _ => return None,
                }
            } else {
                None
            };
            t_out.push(node(r, j, one)?);
        }
        Some((t_in, t_out))
    }
}

/// A region place of a fn signature for `lub_shapes_fit`: `'static`, a
/// region that may become any other (an early-bound lifetime, a free
/// one), or a binder (by first-use order).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Shape {
    Static,
    Var,
    Bound(u32),
}

/// Renumbers binders by first use, so two shapes compare up to renaming.
fn canon(shapes: Vec<Shape>) -> Vec<Shape> {
    let mut seen: Vec<u32> = Vec::new();
    shapes
        .into_iter()
        .map(|s| match s {
            Shape::Bound(b) => Shape::Bound(match seen.iter().position(|&x| x == b) {
                Some(i) => i as u32,
                None => {
                    seen.push(b);
                    seen.len() as u32 - 1
                }
            }),
            s => s,
        })
        .collect()
}

/// The shape of fn pointer type `ptr` (check's erased form), slot by slot:
/// its free slots and early ones are `Var`, written `'static` is
/// `Static`, each other input slot its own binder, and each other output
/// slot the one input slot's.
fn ptr_shape(p: &Program, tys: &impl TyIntern, ptr: Ty) -> Option<Vec<Shape>> {
    let TyKind::FnPtr(s) = tys.kind(ptr) else { return None };
    let s = tys.sig(s).value;
    let mut sc = SlotCx::new(tys, p);
    let mut j = 0u32;
    let mut ins = Vec::new();
    for &it in tys.tys_of(s.inputs) {
        let mut rs = Vec::new();
        regioned_slots(&mut sc, it, it, &mut rs);
        for r in rs {
            ins.push(if s.free_slots >> j & 1 == 1 {
                Shape::Var
            } else if r == Region::Static {
                Shape::Static
            } else {
                Shape::Bound(j)
            });
            j += 1;
        }
    }
    let mut outs = Vec::new();
    let mut rs = Vec::new();
    regioned_slots(&mut sc, s.output, s.output, &mut rs);
    for r in rs {
        outs.push(if s.free_slots >> j & 1 == 1 {
            Shape::Var
        } else if r == Region::Static {
            Shape::Static
        } else {
            match ins[..] {
                [one] => one,
                _ => return None,
            }
        });
        j += 1;
    }
    ins.extend(outs);
    Some(canon(ins))
}

/// The shape of fn `f`'s region signature, paired with the erased fn
/// pointer type `ptr` it becomes: early-bound lifetimes are `Var`,
/// late-bound ones binders.
fn fn_shape(p: &Program, tys: &impl TyIntern, f: LocalDefId, ptr: Ty) -> Option<Vec<Shape>> {
    let sig = p.regions.body_sig(p, f)?;
    let TyKind::FnPtr(s) = tys.kind(ptr) else { return None };
    let s = tys.sig(s).value;
    let ins: Vec<Ty> = tys.tys_of(s.inputs).to_vec();
    if sig.params.len() != ins.len() {
        return None;
    }
    let mut sc = SlotCx::new(tys, p);
    let mut out = Vec::new();
    for (&r, e) in sig.params.iter().zip(ins).chain(std::iter::once((&sig.ret, s.output))) {
        let mut rs = Vec::new();
        regions_of(&p.tys, r, &mut rs);
        if rs.len() != sc.slots(e) as usize {
            return None;
        }
        for r in rs {
            let s = match r {
                Region::Static => Shape::Static,
                Region::Param(k) if sig.early.get(k as usize) == Some(&true) => Shape::Var,
                Region::Param(k) => Shape::Bound(k),
                _ => Shape::Bound(u32::MAX - out.len() as u32),
            };
            out.push(s);
        }
    }
    Some(canon(out))
}

/// rustc's LUB of a fn item with the fn pointer type an array or `vec!`
/// literal's earlier elements gave (W-BORROW3): when either has a
/// higher-ranked region, the two must be the same type up to renaming
/// binders (rustc relates them invariantly there); an early-bound region
/// may become `'static` or a free one. False when they differ, or when
/// lust cannot pair them.
pub(crate) fn lub_shapes_fit(p: &Program, tys: &impl TyIntern, f: LocalDefId, ptr: Ty) -> bool {
    let (Some(a), Some(b)) = (fn_shape(p, tys, f, ptr), ptr_shape(p, tys, ptr)) else { return false };
    shapes_fit(&a, &b)
}

/// rustc's join of two fn items with no element type given (`[a, b]`):
/// the later one, `b`, must be a subtype of the first, `a` (both reified;
/// rustc coerces `b` to `a`'s pointer type). `a`'s binders are
/// placeholders, `b`'s are picked, early-bound regions are free; a
/// placeholder may outlive only itself and never `'static`. False when
/// lust cannot pair the signatures with `ptr`.
pub(crate) fn lub_items_fit(p: &Program, tys: &impl TyIntern, a: LocalDefId, b: LocalDefId, ptr: Ty) -> bool {
    let (Some(x), Some(y)) = (fn_shape(p, tys, a, ptr), fn_shape(p, tys, b, ptr)) else { return false };
    let TyKind::FnPtr(s) = tys.kind(ptr) else { return false };
    let s = tys.sig(s).value;
    let mut sc = SlotCx::new(tys, p);
    let mut var: Vec<Variance> = Vec::new();
    for &t in tys.tys_of(s.inputs) {
        sc.each_slot(t, Variance::Contra, 0, &mut |_, v| var.push(v));
    }
    sc.each_slot(s.output, Variance::Co, 0, &mut |_, v| var.push(v));
    if x.len() != y.len() || var.len() != x.len() {
        return false;
    }
    // `y <: x` slot by slot: (sup, sub) pairs, over target placeholders,
    // source binders, `'static`, and free regions.
    let node = |sh: Shape, target: bool| match sh {
        Shape::Static => Node::Var(0),
        Shape::Var => Node::Var(1),
        Shape::Bound(i) if target => Node::Ph(i),
        Shape::Bound(i) => Node::Late(i),
    };
    let mut cons: Vec<(Node, Node)> = Vec::new();
    for ((&sy, &sx), &v) in y.iter().zip(&x).zip(&var) {
        let (src, dst) = (node(sy, false), node(sx, true));
        match v {
            Variance::Co => cons.push((src, dst)),
            Variance::Contra => cons.push((dst, src)),
            Variance::Inv => {
                cons.push((src, dst));
                cons.push((dst, src));
            }
            Variance::Bi => {}
        }
    }
    // Each free region is its own var: they may become anything, so only
    // placeholders and `'static` can fail.
    for &(x0, _) in &cons {
        if matches!(x0, Node::Late(_)) {
            continue;
        }
        let mut seen = vec![x0];
        let mut work = vec![x0];
        while let Some(n) = work.pop() {
            for &(a0, b0) in &cons {
                if a0 == n && !seen.contains(&b0) {
                    seen.push(b0);
                    match (x0, b0) {
                        (_, Node::Late(_)) => work.push(b0),
                        (Node::Ph(i), Node::Ph(j)) if i != j => return false,
                        (Node::Ph(_), Node::Var(0)) => return false,
                        _ => {}
                    }
                }
            }
        }
    }
    true
}

/// Two canonical shapes LUB to one type (`lub_shapes_fit`).
fn shapes_fit(a: &[Shape], b: &[Shape]) -> bool {
    let bound = |s: &[Shape]| s.iter().any(|x| matches!(x, Shape::Bound(_)));
    if !bound(a) && !bound(b) {
        return true;
    }
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| match (x, y) {
            (Shape::Bound(i), Shape::Bound(j)) => i == j,
            (Shape::Var, Shape::Var | Shape::Static) | (Shape::Static, Shape::Var | Shape::Static) => true,
            _ => false,
        })
}
