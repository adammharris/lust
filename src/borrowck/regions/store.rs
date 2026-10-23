// Values a builtin stores in a container (tf-borrow round 7).
//
// The opaque call rule lets every argument region flow into the slots
// behind a `&mut` argument (`v.push(x)`, `v.insert(0, x)`,
// `v.extend([x])`, `map.extend(..)`). A flow is one way, which is right
// only for covariant slots: an element type with a `Cell`, a `&mut`, a fn
// pointer, or an invariant user type needs the stored regions equal to
// the container's (rustc E0621, E0308). `store_into` relates each part of
// the stored value whose type is a part of the container at its variance
// (`x <: T`), and every other slot of the value by the variance of each
// container slot it may reach.
use super::*;

/// One part of a type (`SlotCx::parts`): the part's type, its first slot
/// in the whole type's slots, its slot count, its position variance, and
/// the index of its last part (itself when it has none inside).
#[derive(Clone, Copy)]
pub(super) struct Part {
    pub ty: Ty,
    pub at: u32,
    pub n: u32,
    pub var: Variance,
    pub last: usize,
}

impl<T: TyIntern> SlotCx<'_, '_, T> {
    /// Pushes `t` (at variance `v`, first slot `at`) and then each part
    /// inside it, in the slot order `each_slot` walks. Returns the next
    /// slot index.
    pub(super) fn parts(&mut self, t: Ty, v: Variance, at: u32, out: &mut Vec<Part>) -> u32 {
        let n = self.slots(t);
        let me = out.len();
        out.push(Part { ty: t, at, n, var: v, last: me });
        let mut k = at;
        match self.tys.kind(t) {
            TyKind::Ref(r, m, inner) => {
                k += u32::from(!bound(r));
                self.parts(inner, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }), k, out);
            }
            TyKind::Adt(def, args) => {
                k += adt_regions(self.p, self.tys, t);
                for (j, g) in self.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                        k = self.parts(e, v.then(pv), k, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.tys.tys_of(ts).to_vec() {
                    k = self.parts(e, v, k, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => {
                self.parts(e, v, k, out);
            }
            TyKind::RawPtr(m, e) => {
                self.parts(e, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }), k, out);
            }
            // Closures, dyn objects and fn pointers: whole parts only.
            _ => {}
        }
        out[me].last = out.len() - 1;
        at + n
    }
}

impl Builder<'_, '_> {
    /// A value of type `at` (vars `av`) that a call may store in a place of
    /// type `pt` (vars `pv`, the pointee of a `&mut` argument): each
    /// largest part of the value whose type is a part of `pt` relates to
    /// every such part at its own position variance (`v.push(x)`: `x <:
    /// T`; `v.append(&mut w)`: `w`'s `T` equal). The references on the path
    /// to such a part are only borrowed by the call. Every other slot of
    /// the value may sit at any slot of `pt`: covariant ones outlive it,
    /// invariant ones equal it, contravariant ones are outlived by it.
    /// Returns the slots of `pv` a stored part fills (`store_covered`: the
    /// slots of `av` it related exactly). Callers keep their
    /// own one-way flows (into the other slots, for the adapter and item
    /// rules); this only adds edges.
    pub(super) fn store_into(&mut self, at: Ty, av: &[u32], pt: Ty, pv: &[u32]) -> Vec<bool> {
        self.store_parts(at, av, pt, pv, true)
    }

    /// `store_into`; with `flat` false only the matched parts relate (the
    /// caller relates the other slots itself) and the filled slots return.
    pub(super) fn store_parts(&mut self, at: Ty, av: &[u32], pt: Ty, pv: &[u32], flat: bool) -> Vec<bool> {
        let tys = &self.body.tys;
        let mut filled = vec![false; pv.len()];
        self.store_covered = vec![false; av.len()];
        if (pv.is_empty() || av.is_empty()) && !(has_fn_ptr(tys, at) && has_fn_ptr(tys, pt)) {
            return filled;
        }
        let (mut ap, mut pp) = (Vec::new(), Vec::new());
        let whole = self.sc.parts(at, Variance::Co, 0, &mut ap) as usize == av.len() && self.sc.parts(pt, Variance::Co, 0, &mut pp) as usize == pv.len();
        let mut covered = vec![false; av.len()];
        if whole {
            let mut skip = 0usize;
            for (k, a) in ap.iter().enumerate() {
                // A part with no slots still proves a fn pointer against
                // the container's (`fn(&'static u8)` stored as `fn(&'b u8)`).
                if (k != 0 && k <= skip) || (a.n == 0 && !has_fn_ptr(&self.body.tys, a.ty)) {
                    continue;
                }
                let mut hit = false;
                let tys = &self.body.tys;
                let hits: Vec<(usize, Part)> = pp.iter().enumerate().filter(|(_, q)| same_shape(tys, q.ty, a.ty)).map(|(i, q)| (i, *q)).collect();
                for (qi, q) in hits {
                    let (x, y) = (av[a.at as usize..(a.at + a.n) as usize].to_vec(), pv[q.at as usize..(q.at + q.n) as usize].to_vec());
                    // Only the whole argument stored as a part of the
                    // container is a coercion site (`v.push(x)`); a part
                    // inside it (`v.extend([x])`), or a whole container
                    // (`v.extend(vec![x])`), has the binders of its own
                    // type, so a fn pointer there may not trade a
                    // higher-ranked input for a free one (rustc E0308).
                    let site = k == 0 && qi != 0;
                    if !site && ptr_binders_differ(tys, a.ty, q.ty) {
                        self.ptr_not_general();
                    }
                    // `v.push(c)` coerces `c` to `T`: the object lifetime
                    // of a `&mut dyn` (or a `RefMut<dyn>`) may shorten there.
                    self.dyn_coerce = site;
                    self.guard_coerce = site;
                    self.relate(a.ty, &x, q.ty, &y, a.var);
                    self.dyn_coerce = false;
                    self.guard_coerce = false;
                    filled[q.at as usize..(q.at + q.n) as usize].fill(true);
                    hit = true;
                }
                if hit {
                    covered[a.at as usize..(a.at + a.n) as usize].fill(true);
                    skip = a.last;
                    if k == 0 {
                        break;
                    }
                }
            }
            // A reference whose pointee holds a stored part.
            for a in &ap {
                if let TyKind::Ref(r, _, _) = self.body.tys.kind(a.ty)
                    && !bound(r)
                    && covered[(a.at + 1) as usize..(a.at + a.n) as usize].iter().any(|&c| c)
                {
                    covered[a.at as usize] = true;
                }
            }
        }
        // The rest reaches only the slots no stored part fills (an
        // iterator's own borrow is not the `&'static str` its items hold).
        if flat {
            let rest: Vec<u32> = av.iter().zip(&covered).filter(|(_, c)| !**c).map(|(&x, _)| x).collect();
            self.store_flat_in(&rest, pt, pv, &filled);
        }
        self.store_covered = covered;
        filled
    }

    /// The item slots `items` stored into the leading slots `ev` of a
    /// place of type `pt` (`table.extend(..)`, one item slot per element
    /// slot, in order): an invariant element slot equals its item slot, a
    /// contravariant one outlives it (callers add the covariant flows).
    /// Any other count relates by variance only (`store_flat`).
    pub(super) fn store_slots(&mut self, items: &[u32], pt: Ty, ev: &[u32]) {
        let mut var = Vec::new();
        self.sc.each_slot(pt, Variance::Co, 0, &mut |_, w| var.push(w));
        if items.len() != ev.len() || var.len() < ev.len() {
            return self.store_flat(items, pt, ev);
        }
        for ((&x, &y), &w) in items.iter().zip(ev).zip(&var) {
            if matches!(w, Variance::Inv | Variance::Contra) {
                self.edge(y, x);
            }
        }
    }

    /// Regions `srcs` that may sit at any slot of a place of type `pt`
    /// (vars `pv`): each relates to each slot by that slot's variance.
    pub(super) fn store_flat(&mut self, srcs: &[u32], pt: Ty, pv: &[u32]) {
        self.store_flat_in(srcs, pt, pv, &[]);
    }

    /// `store_flat` over the slots of `pv` that `skip` does not mark.
    pub(super) fn store_flat_in(&mut self, srcs: &[u32], pt: Ty, pv: &[u32], skip: &[bool]) {
        if srcs.is_empty() || pv.is_empty() {
            return;
        }
        let mut var = Vec::with_capacity(pv.len());
        self.sc.each_slot(pt, Variance::Co, 0, &mut |_, w| var.push(w));
        if var.len() != pv.len() {
            return self.equate_all(srcs, pv);
        }
        for (k, &f) in skip.iter().enumerate() {
            if f && k < var.len() {
                var[k] = Variance::Bi;
            }
        }
        // A closure's captures are no place a call stores into.
        let mut pp = Vec::new();
        self.sc.parts(pt, Variance::Co, 0, &mut pp);
        for q in pp.iter().filter(|q| matches!(self.body.tys.kind(q.ty), TyKind::Closure(..))) {
            for w in var.iter_mut().skip(q.at as usize).take(q.n as usize) {
                *w = Variance::Bi;
            }
        }
        // `x: h: y` for covariant and invariant slots, `y: g: x` for
        // invariant and contravariant ones.
        let (h, g) = (self.fresh(), self.fresh());
        for &x in srcs {
            self.edge(x, h);
            self.edge(g, x);
        }
        for (&y, &w) in pv.iter().zip(&var) {
            if matches!(w, Variance::Co | Variance::Inv) {
                self.edge(h, y);
            }
            if matches!(w, Variance::Inv | Variance::Contra) {
                self.edge(y, g);
            }
        }
    }
}

/// True when `a` and `b` are one type up to regions and fn pointer binders
/// (check proved the stored value has the container part's type).
fn same_shape(tys: &impl TyIntern, a: Ty, b: Ty) -> bool {
    if a == b {
        return true;
    }
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Ref(_, ma, x), TyKind::Ref(_, mb, y)) => ma == mb && same_shape(tys, x, y),
        (TyKind::RawPtr(ma, x), TyKind::RawPtr(mb, y)) => ma == mb && same_shape(tys, x, y),
        (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => same_shape(tys, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (xs, ys) = (tys.tys_of(x), tys.tys_of(y));
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(&x, &y)| same_shape(tys, x, y))
        }
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
            let (xs, ys): (Vec<Ty>, Vec<Ty>) = (tys.args(xa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(xb).iter().filter_map(|g| g.as_ty()).collect());
            xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| same_shape(tys, x, y))
        }
        // One trait (and args), any object lifetime.
        (TyKind::Dyn(x, _), TyKind::Dyn(y, _)) => x == y,
        (TyKind::FnPtr(x), TyKind::FnPtr(y)) => {
            let (sx, sy) = (tys.sig(x).value, tys.sig(y).value);
            let (ix, iy) = (tys.tys_of(sx.inputs), tys.tys_of(sy.inputs));
            ix.len() == iy.len() && ix.iter().zip(iy).all(|(&x, &y)| same_shape(tys, x, y)) && same_shape(tys, sx.output, sy.output)
        }
        _ => false,
    }
}

/// True when two types of one shape (`same_shape`) hold a fn pointer pair
/// where one has a free region and the other none (`for<'r> fn(&'r u8)`
/// against `fn(&'b u8)`).
fn ptr_binders_differ(tys: &impl TyIntern, a: Ty, b: Ty) -> bool {
    if a == b {
        return false;
    }
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Ref(_, _, x), TyKind::Ref(_, _, y)) | (TyKind::RawPtr(_, x), TyKind::RawPtr(_, y)) => ptr_binders_differ(tys, x, y),
        (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => ptr_binders_differ(tys, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => tys.tys_of(x).iter().zip(tys.tys_of(y)).any(|(&x, &y)| ptr_binders_differ(tys, x, y)),
        (TyKind::Adt(_, xa), TyKind::Adt(_, xb)) => {
            let (xs, ys): (Vec<Ty>, Vec<Ty>) = (tys.args(xa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(xb).iter().filter_map(|g| g.as_ty()).collect());
            xs.into_iter().zip(ys).any(|(x, y)| ptr_binders_differ(tys, x, y))
        }
        (TyKind::FnPtr(x), TyKind::FnPtr(y)) => {
            let (kx, ky) = (sig_binders(tys, x), sig_binders(tys, y));
            tys.sig(x).value.binders != tys.sig(y).value.binders || kx.len() == ky.len() && kx.iter().zip(&ky).any(|(p, q)| p != q)
        }
        _ => false,
    }
}

/// Per region place of a fn pointer signature (inputs, then output, in
/// `FnSig::free_slots` order): true where it is a binder of the pointer
/// (`for<'r> fn(&'r u8)`), false where it is the free region or `'static`.
fn sig_binders(tys: &impl TyIntern, s: crate::ty::SigId) -> Vec<bool> {
    let sig = tys.sig(s).value;
    let mut rs = Vec::new();
    for &t in tys.tys_of(sig.inputs).iter().chain(std::iter::once(&sig.output)) {
        regions_of(tys, t, &mut rs);
    }
    rs.iter().enumerate().map(|(k, &r)| r != Region::Static && (k >= 32 || sig.free_slots & (1 << k) == 0)).collect()
}

impl Builder<'_, '_> {
    /// A callee's `I: Iterator<Item = X>` and `I: IntoIterator<Item = X>`
    /// (also `DoubleEndedIterator`, `ExactSizeIterator`) bounds at a call (`call_sig_with`, after its params and return are
    /// instantiated): trait matching makes the items of the type bound to
    /// `I` equal to `X` (`fn add<'b, I: IntoIterator<Item = &'b u8>>(v:
    /// &mut Vec<&'b u8>, it: I)` with `[&local]` needs the borrow to last
    /// `'b`; `BTreeMap::extend`, `VecDeque::extend`). When lust cannot read
    /// the items, every region of the bound type may reach `X`, at the
    /// variance of each slot of `X` (`store_flat`'s rule). A bound whose `X`
    /// names a param nothing bound adds nothing. True when there was at
    /// least one bound and each one paired exactly (fixed or read items),
    /// so the caller's every-argument rule (`item_bound`) is not needed.
    pub(super) fn item_bound_equate(&mut self, sig: &RegionSig, binds: &FxMap<u32, Vec<u32>>, univ: &[u32]) -> bool {
        let lang = self.p.gx.lang;
        let iter_trait = |d: DefId| [lang.iterator, lang.into_iterator, lang.double_ended_iterator, lang.exact_size_iterator].contains(&d);
        let pairs: Vec<(u32, Ty)> = sig.item_bounds.iter().filter(|b| iter_trait(b.1)).map(|b| (b.0, b.2)).collect();
        let mut exact = !pairs.is_empty();
        for (ji, x) in pairs {
            let (Some(&it), Some(iv)) = (self.bind_tys.get(&ji), binds.get(&ji).cloned()) else {
                exact = false;
                continue;
            };
            let mut xs = Vec::new();
            if !self.callee_slots(x, Variance::Co, univ, binds, &mut xs) {
                exact = false;
                continue;
            }
            let xv: Vec<u32> = xs.iter().map(|s| s.0).collect();
            // Items a type param's bound fixes are `X` exactly, through any
            // adapter (`fixed_items`).
            let fixed = match self.fixed_items(it) {
                Some(fx) if fx.len() == xv.len() => {
                    self.tie_fixed(&fx, &xv);
                    true
                }
                _ => false,
            };
            // A fn pointer in the items has no slot to equate: prove it
            // against the type each param of `X` is bound to.
            if has_fn_ptr(&self.body.tys, it) {
                exact = false;
                let mut ps = Vec::new();
                params_in(&self.p.tys, x, &mut ps);
                for j in ps {
                    if let (Some(&bt), Some(bv)) = (self.bind_tys.get(&j), binds.get(&j).cloned())
                        && has_fn_ptr(&self.body.tys, bt)
                    {
                        self.store_into(it, &iv, bt, &bv);
                    }
                }
            }
            let mut cands = Vec::new();
            let mut known = if crate::ty::iter::iter_parts(&self.body.tys, it).is_some() || self.body.tys.builtin_of(it).is_some_and(|b| matches!(b, BuiltinTy::Chars)) {
                self.iter_items(it, &iv, &mut cands)
            } else if let Some(c) = self.into_iter_items(it, &iv) {
                cands.push(c);
                true
            } else {
                self.iter_items(it, &iv, &mut cands)
            };
            // A chain after fixed items whose other side `iter_items` does
            // not name (`chain(None)`): each side's `item_slots`, so the
            // conservative rule below does not reach `X` from the wrapped
            // iterator's own borrow.
            if fixed && !known {
                cands.clear();
                known = self.chain_sides(it, &iv, &mut cands);
            }
            if known && !cands.is_empty() && cands.iter().all(|c| c.len() == xv.len()) {
                for c in cands {
                    for (&a, &b) in c.iter().zip(&xv) {
                        self.edge(a, b);
                        self.edge(b, a);
                    }
                }
                continue;
            }
            exact &= fixed;
            // Unknown items: any region of the bound type, at `X`'s variance.
            let (h, g) = (self.fresh(), self.fresh());
            for &a in &iv {
                self.edge(a, h);
                self.edge(g, a);
            }
            for &(y, w) in &xs {
                if matches!(w, Variance::Co | Variance::Inv) {
                    self.edge(h, y);
                }
                if matches!(w, Variance::Inv | Variance::Contra) {
                    self.edge(y, g);
                }
            }
        }
        exact
    }

    /// The items of each side of a `Chain` (its slots `iv`), by
    /// `item_slots`, else `iter_items`. False for another type or a side
    /// neither names.
    pub(super) fn chain_sides(&mut self, it: Ty, iv: &[u32], out: &mut Vec<Vec<u32>>) -> bool {
        let Some((crate::ty::iter::IterKind::Chain, a)) = crate::ty::iter::iter_parts(&self.body.tys, it) else { return false };
        let (Some(&a0), Some(&a1)) = (a.first(), a.get(1)) else { return false };
        let n0 = self.sc.slots(a0) as usize;
        let n1 = self.sc.slots(a1) as usize;
        let (Some(v0), Some(v1)) = (iv.get(..n0).map(<[u32]>::to_vec), iv.get(n0..n0 + n1).map(<[u32]>::to_vec)) else { return false };
        for (t, v) in [(a0, v0), (a1, v1)] {
            match self.item_slots(t, &v) {
                Some(x) => out.push(x),
                None if self.iter_items(t, &v, out) => {}
                None => return false,
            }
        }
        true
    }

    /// The slot vars of a callee's regioned type `r` at a call, with each
    /// slot's variance (from `v`): its params' vars from `binds` (and
    /// their bound types' variances), its regions instantiated. False when
    /// a param is unbound or a part has no slot reading (a dyn, a fn
    /// pointer, a projection).
    fn callee_slots(&mut self, r: Ty, v: Variance, univ: &[u32], binds: &FxMap<u32, Vec<u32>>, out: &mut Vec<(u32, Variance)>) -> bool {
        let p = self.p;
        match p.tys.kind(r) {
            TyKind::Param(j) => {
                let (Some(vs), Some(&bt)) = (binds.get(&j.0), self.bind_tys.get(&j.0)) else { return false };
                let mut var = Vec::new();
                self.sc.each_slot(bt, v, 0, &mut |_, w| var.push(w));
                if var.len() != vs.len() {
                    return false;
                }
                out.extend(vs.iter().copied().zip(var));
                true
            }
            TyKind::Ref(rr, m, inner) => {
                if bound(rr) {
                    return false;
                }
                let x = self.inst_region(rr, univ);
                out.push((x, v));
                self.callee_slots(inner, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }), univ, binds, out)
            }
            TyKind::Tuple(ts) => p.tys.tys_of(ts).to_vec().into_iter().all(|e| self.callee_slots(e, v, univ, binds, out)),
            TyKind::Array(e, _) | TyKind::Slice(e) => self.callee_slots(e, v, univ, binds, out),
            TyKind::Adt(def, args) => {
                let lts: Vec<Region> = p.tys.args(args).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g && *x != crate::ty::DYN_LATE { Some(*x) } else { None }).collect();
                let n = adt_regions(p, &p.tys, r) as usize;
                if lts.len() != n {
                    return false;
                }
                for (k, &lt) in lts.iter().enumerate() {
                    let rv = if p.tys.builtin_of(r).is_some() { builtin_region_variance(&p.tys, r) } else { p.regions.adts(p).region_modes(def, k).0 };
                    let x = self.inst_region(lt, univ);
                    out.push((x, v.then(rv)));
                }
                for (j, g) in p.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, _) = p.regions.adts(p).arg_modes(p, def, j);
                        if !self.callee_slots(e, v.then(pv), univ, binds, out) {
                            return false;
                        }
                    }
                }
                true
            }
            _ => self.sc.slots(r) == 0 && !p.tys.flags(r).contains_param(),
        }
    }

    /// The item slots of a value of type `t` (vars `vars`) passed for an
    /// `IntoIterator` param that is no iterator: an array, a `Vec`, a
    /// `VecDeque`, an `Option` or a set by value (the element's own slots),
    /// a map by value (`(K, V)`), or `&`/`&mut` of an array, slice or Vec
    /// (`&E`: the borrow, then the element's slots). None for the rest.
    fn into_iter_items(&mut self, t: Ty, vars: &[u32]) -> Option<Vec<u32>> {
        let tys = &self.body.tys;
        let elem_like = |tys: &crate::ty::Tys<'_>, t: Ty| match tys.kind(t) {
            TyKind::Array(..) | TyKind::Slice(_) => true,
            TyKind::Adt(..) => tys.vec_elem(t).is_some(),
            _ => false,
        };
        match tys.kind(t) {
            TyKind::Array(..) => Some(vars.to_vec()),
            TyKind::Ref(r, _, inner) if !bound(r) && elem_like(tys, inner) => Some(vars.to_vec()),
            TyKind::Adt(..) if tys.vec_elem(t).is_some() || tys.option_elem(t).is_some() => Some(vars.to_vec()),
            TyKind::Adt(..) if matches!(crate::ty::hash::hash_parts(tys, t), Some((crate::ty::hash::HashTy::HashMap | crate::ty::hash::HashTy::HashSet, _))) => {
                Some(vars.to_vec())
            }
            _ => None,
        }
    }
}

/// True when a type holds a fn pointer type.
/// True when a value of type `t` can only hand on the values it holds, as
/// they are: it holds no callable (closure, fn item, fn pointer, dyn or
/// opaque value) that could move a region into a part of another shape
/// (`it.map(|r| (r, Cell::new(r)))`), and no type param.
pub(super) fn plain_store(tys: &impl TyIntern, t: Ty) -> bool {
    !holds_closure(tys, t) && !has_fn_ptr(tys, t) && !has_fn_def(tys, t)
}

fn has_fn_def(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::FnDef(..) => true,
        TyKind::Ref(_, _, x) | TyKind::RawPtr(_, x) | TyKind::Array(x, _) | TyKind::Slice(x) => has_fn_def(tys, x),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_fn_def(tys, e)),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_fn_def(tys, e))),
        _ => false,
    }
}

pub(super) fn has_fn_ptr(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::FnPtr(_) => true,
        TyKind::Ref(_, _, x) | TyKind::RawPtr(_, x) | TyKind::Array(x, _) | TyKind::Slice(x) => has_fn_ptr(tys, x),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_fn_ptr(tys, e)),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_fn_ptr(tys, e))),
        _ => false,
    }
}
