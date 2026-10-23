// Outlives requirements of written types (rustc E0309, E0310, E0491; L0617).
//
// A type is well-formed only when what it borrows outlives the borrow:
// `&'a T` needs `T: 'a`, `&'a &'b ()` needs `'b: 'a`, `S<'a, T>` needs what
// the fields of `S` need (rustc's inferred outlives, `infer_adts`). An item
// may assume these requirements for the types it takes and gives (implied
// bounds): a fn's params and return, an impl's header, an Adt's fields.
// The types its bounds name (where clauses, param bounds, assoc bindings,
// `impl Trait` args), an impl's assoc type values, and the bounds of a
// trait or an Adt get no such help: their requirements must follow from
// the implied ones, the declared `'a: 'b` facts, and `T: 'static` bounds.
// lust rejects a written `T: 'a` bound (L0203), so a type param outlives a
// named lifetime only through implied bounds or `'static`.
//
// Collect records each item (`wanted`) with its types resolved in
// `RegionMode::Keep` (`Region::Param` for the item's lifetimes, `'static`
// as `Region::Static`). A region bound by a `for<..>` or `Fn` sugar
// (`Region::Bound`) and an erased one put no requirement.

use crate::check::collect::Program;
use crate::check::generics::STATIC_FACT;
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::intern::FxMap;
use crate::ty::*;

/// What the walks read from the program: the Adt tables and the traits.
struct Cx<'a> {
    regions: &'a crate::borrowck::RegionTables,
    index: &'a crate::traits::index::ImplIndex,
}

/// One requirement `subject: region`; the subject is a type or a region.
type Req = (GenericArg, Region);

/// What a type's outlives requirement splits into (rustc's outlives
/// components): its regions, its type params, its projections.
#[derive(Clone, Copy, PartialEq)]
enum Comp {
    Re(Region),
    Param(Ty),
    Proj(Ty),
}

/// The known outlives facts of one item: `x: r` between regions, and a
/// type param or projection that outlives a region.
#[derive(Default)]
struct Env {
    re: Vec<(Region, Region)>,
    ty: Vec<(Ty, Region)>,
    statics: Vec<Ty>,
    /// Equality bounds `<P as Tr>::A == X` (assoc, trait args, X): a
    /// projection they fix outlives what X outlives (rustc normalizes).
    eqs: Vec<(DefId, ArgsId, Ty)>,
}

/// One item's types for the check (see the file comment), recorded at
/// collect (`wanted`) and checked once every Adt has its fields
/// (`check_all`). `facts` are the declared `'a: 'b` facts by universal
/// index (`STATIC_FACT` is `'static`), `preds` the item's bounds (its
/// `T: 'static` and equality bounds count).
#[derive(Clone, Debug)]
pub struct Item {
    pub implied: Vec<Ty>,
    pub required: Vec<Ty>,
    pub facts: Vec<(u32, u32)>,
    pub preds: Vec<Predicate>,
    pub span: Span,
}

/// Whether to record an item in `RegionTables::outlives_items`: not when
/// it requires nothing or is shipped source (std, core, alloc, and the
/// platform crate are valid as written). Callers push it themselves, so
/// a borrow of the AST may stay live.
pub fn wanted(p: &Program, item: &Item) -> bool {
    !item.required.is_empty() && !p.in_lang_methods(item.span) && p.shipped_crate_at(item.span).is_none()
}

/// The type params with a `T: 'static` bound among `preds`.
pub fn statics_of(preds: &[Predicate]) -> Vec<Ty> {
    preds.iter().filter_map(|q| if let Predicate::TypeOutlives(x, Region::Static) = q { Some(*x) } else { None }).collect()
}

/// Infers the Adt tables, then checks every recorded item. The first
/// requirement of an item that does not hold is its error.
pub fn check_all(p: &mut Program, errs: &mut Vec<Diag>) {
    let items = std::mem::take(&mut p.regions.outlives_items);
    // Body annotations read the Adt tables too (`check_body_ty`).
    infer_adts(p);
    check_adt_statics(p, errs);
    for it in items {
        if let Some(d) = check_item(p, &it) {
            errs.push(d);
        }
    }
}

/// Checks the items queued since `check_all` (a signature delta's) with
/// the Adt tables it inferred, and drops them.
pub(crate) fn check_queued(p: &mut Program, errs: &mut Vec<Diag>) {
    for it in std::mem::take(&mut p.regions.outlives_items) {
        if let Some(d) = check_item(p, &it) {
            errs.push(d);
        }
    }
}

fn check_item(p: &mut Program, it: &Item) -> Option<Diag> {
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, &mut p.tys, &it.implied, &it.facts, &it.preds);
    let bad = unmet(&cx, &mut p.tys, &env, &it.required);
    bad.map(|(g, r)| diag(&cx, &p.tys, &env, g, r, it.span))
}

/// The facts an item knows: declared ones, `T: 'static` bounds, and the
/// requirements of its implied types.
fn implied_env(cx: &Cx, tys: &mut impl TyIntern, implied: &[Ty], facts: &[(u32, u32)], preds: &[Predicate]) -> Env {
    let mut env = Env { statics: statics_of(preds), ..Env::default() };
    for q in preds {
        match q {
            Predicate::AssocEq(b) if b.count == 0 => env.eqs.push((b.value.assoc, b.value.trait_args, b.value.ty)),
            // A written `T: 'a` bound (fns and inherent methods).
            Predicate::TypeOutlives(x, r @ Region::Param(_)) => env.ty.push((*x, *r)),
            Predicate::Trait(b) if b.count == 0 => {
                for &(d, g) in tys.bindings(b.value.bindings) {
                    if let GenericArg::Ty(x) = g {
                        env.eqs.push((d, b.value.args, x));
                    }
                }
                // `T: Tr` where `Tr: 'static` (or a supertrait of it):
                // `T: 'static` is implied (`trait Flags: Sized + 'static`).
                if let Some(GenericArg::Ty(x)) = tys.args(b.value.args).first().copied()
                    && trait_implies_static(cx, tys, b.value.def, 0)
                    && !env.statics.contains(&x)
                {
                    env.statics.push(x);
                }
            }
            _ => {}
        }
    }
    for &(a, b) in facts {
        env.re.push((Region::Param(a), if b == STATIC_FACT { Region::Static } else { Region::Param(b) }));
    }
    for &t in implied {
        let t = expand_free(tys, t);
        let mut reqs = Vec::new();
        wf_in(cx, tys, t, true, &mut reqs);
        for (g, r) in reqs {
            assume(tys, &mut env, g, r);
        }
    }
    env
}

/// Whether trait `def` or one of its supertraits declares `Self: 'static`.
fn trait_implies_static(cx: &Cx, tys: &impl TyIntern, def: DefId, depth: u32) -> bool {
    trait_is_static(cx.index, tys, def, depth)
}

/// Whether trait `def` or one of its supertraits declares `Self:
/// 'static` (`trait Flags: Sized + 'static`), so `T: def` implies
/// `T: 'static`.
pub(crate) fn trait_is_static(index: &crate::traits::index::ImplIndex, tys: &impl TyIntern, def: DefId, depth: u32) -> bool {
    let Some(rec) = index.trait_record(def) else { return false };
    if depth > 16 {
        return false;
    }
    let is_self = |t: Ty| matches!(tys.kind(t), TyKind::Param(ParamId(0)));
    rec.generics.predicates.iter().any(|q| match q {
        Predicate::TypeOutlives(x, Region::Static) => is_self(*x),
        Predicate::Trait(b) if b.count == 0 => {
            b.value.def != def
                && tys.args(b.value.args).first().and_then(|g| g.as_ty()).is_some_and(is_self)
                && trait_is_static(index, tys, b.value.def, depth + 1)
        }
        _ => false,
    })
}

/// Whether associated type `assoc`'s declared bounds imply `'static`:
/// `type A: 'static`, or `type A: Tr` with `Tr` static.
pub(crate) fn assoc_bounds_static(index: &crate::traits::index::ImplIndex, tys: &impl TyIntern, assoc: DefId) -> bool {
    let Some(rec) = index.trait_of_assoc(assoc).and_then(|d| index.trait_record(d)) else { return false };
    let is_assoc = |t: Ty| matches!(tys.kind(t), TyKind::Projection(a, _) if a.0 == assoc);
    rec.generics.predicates.iter().any(|q| match q {
        Predicate::TypeOutlives(x, Region::Static) => is_assoc(*x),
        Predicate::Trait(b) if b.count == 0 => {
            tys.args(b.value.args).first().and_then(|g| g.as_ty()).is_some_and(is_assoc) && trait_is_static(index, tys, b.value.def, 0)
        }
        _ => false,
    })
}

/// The first requirement of the `required` types that `env` does not prove.
fn unmet(cx: &Cx, tys: &mut impl TyIntern, env: &Env, required: &[Ty]) -> Option<Req> {
    for &t in required {
        let t = expand_free(tys, t);
        let mut reqs = Vec::new();
        wf(cx, tys, t, &mut reqs);
        if let Some(bad) = reqs.into_iter().find(|&(g, r)| !holds(cx, tys, env, g, r)) {
            return Some(bad);
        }
    }
    None
}

/// Checks a type written in the body of a fn with region signature
/// `sig` (a `let` annotation) under the fn's implied bounds and its
/// `T: 'static` bounds in `preds`. The error, if a requirement fails.
pub fn check_body_ty(
    p: &Program,
    tys: &mut impl TyIntern,
    sig: &crate::borrowck::RegionSig,
    preds: &[Predicate],
    t: Ty,
    span: Span,
) -> Option<Diag> {
    let mut implied: Vec<Ty> = sig.params.iter().copied().chain([sig.ret]).collect();
    implied.extend(sig.header.iter().copied());
    let facts: Vec<(u32, u32)> = sig
        .facts
        .iter()
        .filter_map(|&(a, b)| match (a, b) {
            (Region::Param(x), Region::Param(y)) => Some((x, y)),
            (Region::Param(x), Region::Static) => Some((x, STATIC_FACT)),
            _ => None,
        })
        .collect();
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, tys, &implied, &facts, preds);
    unmet(&cx, tys, &env, &[t]).map(|(g, r)| diag(&cx, tys, &env, g, r, span))
}

/// The diagnostic for a requirement `g: r` that does not hold.
/// What a fn knows of its type params' lifetimes: `(param index,
/// region)` for each bound its signature implies (region signature
/// `sig`) or its env `preds` states (`T: 'static`, `T: 'a`). Borrowck's dyn
/// coercions read it (`OwnSig::param_univs`).
pub fn param_bounds(p: &Program, sig: Option<&crate::borrowck::RegionSig>, preds: &[Predicate]) -> Vec<(u32, Region)> {
    let mut out: Vec<(u32, Region)> = Vec::new();
    let mut tys = crate::ty::Tys::new(&p.tys);
    for t in statics_of(preds) {
        if let TyKind::Param(j) = tys.kind(t) {
            out.push((j.0, Region::Static));
        }
    }
    // Written `T: 'a` bounds (fns and inherent methods).
    for q in preds {
        if let Predicate::TypeOutlives(x, r @ Region::Param(_)) = q
            && let TyKind::Param(j) = tys.kind(*x)
        {
            out.push((j.0, *r));
        }
    }
    let Some(sig) = sig else { return out };
    let mut implied: Vec<Ty> = sig.params.iter().copied().chain([sig.ret]).collect();
    implied.extend(sig.header.iter().copied());
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, &mut tys, &implied, &[], &[]);
    for (t, r) in env.ty {
        if let TyKind::Param(j) = tys.kind(t) {
            out.push((j.0, r));
        }
    }
    out
}

/// The diagnostic for a requirement `g: r` that does not hold, naming
/// the part of `g` that fails (`'static` needs E0310 wording).
fn diag(cx: &Cx, tys: &impl TyIntern, env: &Env, g: GenericArg, r: Region, span: Span) -> Diag {
    let mut cs = Vec::new();
    match g {
        GenericArg::Ty(t) => components(tys, t, &mut cs),
        GenericArg::Lifetime(x) => cs.push(Comp::Re(x)),
        GenericArg::Const(_) => {}
    }
    let bad = cs.into_iter().find(|&c| match c {
        Comp::Re(x) => !region_holds(env, x, r),
        Comp::Param(x) | Comp::Proj(x) => !ty_holds(cx, tys, env, x, r),
    });
    let what = match bad {
        Some(Comp::Param(_)) => "a type parameter",
        Some(Comp::Proj(_)) => "an associated type",
        _ => "a lifetime",
    };
    let life = if r == Region::Static { "`'static`" } else { "a lifetime this item names" };
    let fix = match bad {
        Some(Comp::Re(_)) | None => "Add the `'b: 'a` bound the type needs, or take a parameter of this type (an implied bound).",
        _ if r == Region::Static => "Add a `'static` bound to the type parameter, or change the type.",
        _ => "Take a parameter of the type that needs the bound (`&'a T` gives `T: 'a`), or change the type.",
    };
    Diag::new("L0617", span, format!("{what} may not live long enough: a type here needs it to outlive {life}"), fix)
}

/// Records the requirements of an implied type as facts. Only named
/// regions make facts: an elided or bound one is no region a bound names
/// (and `region_holds` takes any unnamed region as holding).
fn assume(tys: &impl TyIntern, env: &mut Env, g: GenericArg, r: Region) {
    if !named(r) {
        return;
    }
    match g {
        GenericArg::Lifetime(x) if named(x) => env.re.push((x, r)),
        GenericArg::Lifetime(_) => {}
        GenericArg::Ty(t) => {
            let mut cs = Vec::new();
            components(tys, t, &mut cs);
            for c in cs {
                match c {
                    Comp::Re(x) if named(x) => env.re.push((x, r)),
                    Comp::Re(_) => {}
                    Comp::Param(x) | Comp::Proj(x) => env.ty.push((x, r)),
                }
            }
        }
        GenericArg::Const(_) => {}
    }
}

/// True when `r` is a region the item names: a lifetime param or `'static`.
fn named(r: Region) -> bool {
    matches!(r, Region::Param(_) | Region::Static)
}

/// Whether `g: r` follows from the env.
fn holds(cx: &Cx, tys: &impl TyIntern, env: &Env, g: GenericArg, r: Region) -> bool {
    if !named(r) {
        return true;
    }
    match g {
        GenericArg::Lifetime(x) => region_holds(env, x, r),
        GenericArg::Ty(t) => ty_holds(cx, tys, env, t, r),
        GenericArg::Const(_) => true,
    }
}

fn ty_holds(cx: &Cx, tys: &impl TyIntern, env: &Env, t: Ty, r: Region) -> bool {
    let mut cs = Vec::new();
    components(tys, t, &mut cs);
    cs.into_iter().all(|c| match c {
        Comp::Re(x) => region_holds(env, x, r),
        Comp::Param(x) => env.statics.contains(&x) || env.ty.iter().any(|&(y, s)| y == x && region_holds(env, s, r)),
        Comp::Proj(x) => {
            if let Some(eq) = fixed_by(tys, env, x) {
                return ty_holds(cx, tys, env, eq, r);
            }
            env.ty.iter().any(|&(y, s)| y == x && region_holds(env, s, r))
                || assoc_is_static(cx, tys, x)
                || match tys.kind(x) {
                    TyKind::Projection(_, a) => tys.args(a).to_vec().into_iter().all(|g| holds(cx, tys, env, g, r)),
                    _ => true,
                }
        }
    })
}

/// The type an equality bound fixes projection `t` to, if any.
fn fixed_by(tys: &impl TyIntern, env: &Env, t: Ty) -> Option<Ty> {
    let TyKind::Projection(assoc, a) = tys.kind(t) else { return None };
    env.eqs.iter().find(|&&(d, b, _)| d == assoc.0 && (a == b || tys.args(a) == tys.args(b))).map(|&(_, _, x)| x)
}

/// `<T as Tr>::A` where the trait declares `type A: 'static`.
fn assoc_is_static(cx: &Cx, tys: &impl TyIntern, t: Ty) -> bool {
    let TyKind::Projection(assoc, _) = tys.kind(t) else { return false };
    let Some(rec) = cx.index.trait_of_assoc(assoc.0).and_then(|d| cx.index.trait_record(d)) else { return false };
    rec.generics.predicates.iter().any(|q| match q {
        Predicate::TypeOutlives(x, Region::Static) => matches!(tys.kind(*x), TyKind::Projection(b, _) if b == assoc),
        _ => false,
    })
}

/// `x: r` for regions, through the facts (reflexive and transitive;
/// `'static` outlives every region, and an unnamed region is not checked).
fn region_holds(env: &Env, x: Region, r: Region) -> bool {
    if x == r || x == Region::Static || !named(x) || !named(r) {
        return true;
    }
    let mut seen = vec![x];
    let mut i = 0;
    while i < seen.len() {
        let a = seen[i];
        i += 1;
        for &(u, v) in &env.re {
            if u == a && !seen.contains(&v) {
                if v == r || v == Region::Static {
                    return true;
                }
                seen.push(v);
            }
        }
    }
    false
}

/// `t` with the free region of every fn pointer type in it written into
/// the slots it fills (`FnSig::free_slots`, W-BORROW3), in borrowck's slot
/// order: a reference's region, then its pointee; an Adt's lifetime args,
/// then its type args; a dyn type's object lifetime. The walks then read
/// a fn pointer's regions from its inputs and output alone.
fn expand_free(tys: &mut impl TyIntern, t: Ty) -> Ty {
    if !has_free_ptr(tys, t) {
        return t;
    }
    expand_in(tys, t, &mut |_: Region| None)
}

/// Whether `t` holds a fn pointer type with a free region.
fn has_free_ptr(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::FnPtr(sig) => tys.sig(sig).value.free_slots != 0,
        TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => has_free_ptr(tys, e),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_free_ptr(tys, e))),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_free_ptr(tys, e)),
        _ => false,
    }
}

/// `expand_free`, where `slot` gives the region of the next slot of an
/// enclosing fn pointer (None: keep the written one).
fn expand_in(tys: &mut impl TyIntern, t: Ty, slot: &mut dyn FnMut(Region) -> Option<Region>) -> Ty {
    match tys.kind(t) {
        TyKind::Ref(r, m, e) => {
            let r = slot(r).unwrap_or(r);
            let e = expand_in(tys, e, slot);
            tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::Adt(d, a) => {
            let argv: Vec<GenericArg> = tys.args(a).to_vec();
            let mut out = Vec::with_capacity(argv.len());
            for g in argv {
                out.push(match g {
                    GenericArg::Lifetime(r) => GenericArg::Lifetime(slot(r).unwrap_or(r)),
                    GenericArg::Ty(e) => GenericArg::Ty(expand_in(tys, e, slot)),
                    c => c,
                });
            }
            let a = tys.intern_args(&out);
            tys.intern(TyKind::Adt(d, a))
        }
        TyKind::Tuple(ts) => {
            let parts: Vec<Ty> = tys.tys_of(ts).to_vec().into_iter().map(|e| expand_in(tys, e, slot)).collect();
            let ts = tys.intern_tys(&parts);
            tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Array(e, n) => {
            let e = expand_in(tys, e, slot);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = expand_in(tys, e, slot);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::RawPtr(m, e) => {
            let e = expand_in(tys, e, slot);
            tys.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Dyn(b, r) => {
            let r = slot(r).unwrap_or(r);
            tys.intern(TyKind::Dyn(b, r))
        }
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            let s = b.value;
            // A nested fn pointer with a free region is one slot of ours.
            if s.free_slots != 0 {
                let _ = slot(s.free_region);
            }
            let (bits, free) = (s.free_slots, s.free_region);
            let mut j = 0u32;
            let mut own = |r: Region| {
                let k = j;
                j += 1;
                (bits >> k & 1 == 1).then_some(free).or(Some(r))
            };
            let ins: Vec<Ty> = tys.tys_of(s.inputs).to_vec().into_iter().map(|e| expand_in(tys, e, &mut own)).collect();
            let output = expand_in(tys, s.output, &mut own);
            let inputs = tys.intern_tys(&ins);
            let sig = tys.intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..s } });
            tys.intern(TyKind::FnPtr(sig))
        }
        _ => t,
    }
}

/// The outlives components of `t` (rustc's `compute_components`): every
/// region, type param, and projection in it. A projection is one
/// component; `ty_holds` splits it further when no fact names it.
fn components(tys: &impl TyIntern, t: Ty, out: &mut Vec<Comp>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, e) => {
            out.push(Comp::Re(r));
            components(tys, e, out);
        }
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) => args_components(tys, a, out),
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                components(tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => components(tys, e, out),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for e in tys.tys_of(b.value.inputs).to_vec() {
                components(tys, e, out);
            }
            components(tys, b.value.output, out);
        }
        TyKind::Dyn(b, r) => {
            out.push(Comp::Re(r));
            for tr in dyn_refs(tys, b) {
                trait_ref_components(tys, tr, out);
            }
        }
        TyKind::Param(_) => out.push(Comp::Param(t)),
        TyKind::Projection(..) => out.push(Comp::Proj(t)),
        _ => {}
    }
}

fn args_components(tys: &impl TyIntern, a: ArgsId, out: &mut Vec<Comp>) {
    for g in tys.args(a).to_vec() {
        match g {
            GenericArg::Ty(e) => components(tys, e, out),
            GenericArg::Lifetime(r) => out.push(Comp::Re(r)),
            GenericArg::Const(_) => {}
        }
    }
}

/// A trait ref's parts past `Self`: its args and bound types.
fn trait_ref_components(tys: &impl TyIntern, tr: TraitRef, out: &mut Vec<Comp>) {
    for g in tys.args(tr.args).iter().skip(1).copied().collect::<Vec<_>>() {
        match g {
            GenericArg::Ty(e) => components(tys, e, out),
            GenericArg::Lifetime(r) => out.push(Comp::Re(r)),
            GenericArg::Const(_) => {}
        }
    }
    for (_, g) in tys.bindings(tr.bindings).to_vec() {
        if let GenericArg::Ty(e) = g {
            components(tys, e, out);
        }
    }
}

/// The trait refs of a `dyn` type: its principal and written supertraits.
fn dyn_refs(tys: &impl TyIntern, b: BoundsId) -> Vec<TraitRef> {
    let d = tys.dyn_bounds(b);
    d.principal.iter().chain(d.supertraits.iter()).map(|tr| tr.value).collect()
}

/// The outlives requirements of `t` being well-formed (rustc's WF
/// obligations, outlives part): `&'r X` needs `X: 'r`, an Adt needs
/// its inferred outlives under its args, and so on into every part.
fn wf(cx: &Cx, tys: &mut impl TyIntern, t: Ty, out: &mut Vec<Req>) {
    wf_in(cx, tys, t, false, out);
}

/// `wf`; with `implied`, for an implied type (`implied_env`): rustc
/// assumes what a projection normalizes to, not what its args need, and
/// a `Copied` / `Cloned` item drops the `'a` that its impl's `T: 'a`
/// bound needs (`<Cloned<slice::Iter<'a, T>> as Iterator>::Item` is
/// `T`), so such a projection gives no facts.
fn wf_in(cx: &Cx, tys: &mut impl TyIntern, t: Ty, implied: bool, out: &mut Vec<Req>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, e) => {
            out.push((GenericArg::Ty(e), r));
            wf_in(cx, tys, e, implied, out);
        }
        TyKind::Adt(d, a) => {
            let argv: Vec<GenericArg> = tys.args(a).to_vec();
            adt_reqs(cx, tys, d, &argv, out);
            for g in argv {
                if let GenericArg::Ty(e) = g {
                    wf_in(cx, tys, e, implied, out);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                wf_in(cx, tys, e, implied, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => wf_in(cx, tys, e, implied, out),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for e in tys.tys_of(b.value.inputs).to_vec() {
                wf_in(cx, tys, e, implied, out);
            }
            wf_in(cx, tys, b.value.output, implied, out);
        }
        TyKind::Dyn(b, _) => {
            for tr in dyn_refs(tys, b) {
                trait_ref_wf(cx, tys, tr, out);
            }
        }
        TyKind::Projection(_, a) => {
            if implied && tys.args(a).first().and_then(|g| g.as_ty()).is_some_and(|s| has_copied_layer(tys, s)) {
                return;
            }
            for g in tys.args(a).to_vec() {
                if let GenericArg::Ty(e) = g {
                    wf_in(cx, tys, e, implied, out);
                }
            }
        }
        _ => {}
    }
}

/// The self types of the projections over a `Copied` / `Cloned` layer in
/// signature types `ts`: normalizing one proves its impl's `T: 'a`, which
/// the signature does not imply (`wf_in`), so a fn requires each self
/// type well-formed. Empty for most fns (`has_copied_projection` gates it).
pub fn copied_projection_selves(tys: &impl TyIntern, ts: &[Ty]) -> Vec<Ty> {
    let mut out = Vec::new();
    for &t in ts {
        visit_projections(tys, t, &mut |s| {
            if has_copied_layer(tys, s) {
                out.push(s);
            }
        });
    }
    out
}

/// True when `t` holds a projection over a `Copied` / `Cloned` layer.
pub fn has_copied_projection(tys: &impl TyIntern, t: Ty) -> bool {
    let mut any = false;
    visit_projections(tys, t, &mut |s| any |= has_copied_layer(tys, s));
    any
}

/// Calls `f` with the self type of every projection in `t`.
fn visit_projections(tys: &impl TyIntern, t: Ty, f: &mut dyn FnMut(Ty)) {
    match tys.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => visit_projections(tys, e, f),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().for_each(|&e| visit_projections(tys, e, f)),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            tys.tys_of(s.inputs).iter().chain([&s.output]).for_each(|&e| visit_projections(tys, e, f));
        }
        TyKind::Adt(_, a) | TyKind::Projection(_, a) => {
            if let TyKind::Projection(..) = tys.kind(t)
                && let Some(s) = tys.args(a).first().and_then(|g| g.as_ty())
            {
                f(s);
            }
            tys.args(a).iter().filter_map(|g| g.as_ty()).for_each(|e| visit_projections(tys, e, f));
        }
        _ => {}
    }
}

/// True when builtin iterator `t` has a `Copied` or `Cloned` layer.
fn has_copied_layer(tys: &impl TyIntern, t: Ty) -> bool {
    use crate::ty::iter::{IterKind, iter_parts};
    match iter_parts(tys, t) {
        Some((IterKind::Copied | IterKind::Cloned, _)) => true,
        Some((_, a)) => a.iter().any(|&x| has_copied_layer(tys, x)),
        None => false,
    }
}

/// `wf` of a trait ref's types (a bound, or a `dyn` principal): its
/// args and bound types.
pub(crate) fn trait_ref_wf_tys(tys: &impl TyIntern, tr: TraitRef, out: &mut Vec<Ty>) {
    for g in tys.args(tr.args).to_vec() {
        if let GenericArg::Ty(e) = g {
            out.push(e);
        }
    }
    for (_, g) in tys.bindings(tr.bindings).to_vec() {
        if let GenericArg::Ty(e) = g {
            out.push(e);
        }
    }
}

fn trait_ref_wf(cx: &Cx, tys: &mut impl TyIntern, tr: TraitRef, out: &mut Vec<Req>) {
    let mut ts = Vec::new();
    trait_ref_wf_tys(tys, tr, &mut ts);
    // `Self` of a `dyn` principal is a placeholder.
    for e in ts.into_iter().filter(|&e| e != DYN_SELF) {
        wf(cx, tys, e, out);
    }
}

/// The requirements of one Adt use with region-kept args (lifetimes
/// first, then types and consts): its inferred outlives table under
/// these args; a builtin Adt with no table needs each type arg to
/// outlive each lifetime arg (`slice::Iter<'a, T>`, `Ref<'b, T>`).
fn adt_reqs(cx: &Cx, tys: &mut impl TyIntern, d: DefId, argv: &[GenericArg], out: &mut Vec<Req>) {
    let lts: Vec<Region> = argv.iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
    let rest: Vec<GenericArg> = argv.iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
    let Some(table) = cx.regions.adt_outlives.get(&d).cloned() else {
        if cx.regions.adt_fields.contains_key(&d) {
            return;
        }
        for &r in &lts {
            for g in &rest {
                if let GenericArg::Ty(e) = g {
                    out.push((GenericArg::Ty(*e), r));
                }
            }
        }
        return;
    };
    let re = |r: Region| match r {
        Region::Param(k) => lts.get(k as usize).copied().unwrap_or(Region::Erased),
        r => r,
    };
    for (g, r) in table {
        let g = match g {
            GenericArg::Lifetime(x) => GenericArg::Lifetime(re(x)),
            GenericArg::Ty(t) => GenericArg::Ty(subst(tys, t, &rest)),
            c => c,
        };
        out.push((g, re(r)));
    }
}

/// Fills `RegionTables::adt_outlives`: per user Adt, the requirements
/// over its own params that its fields put (rustc's inferred outlives),
/// its declared `'a: 'b` facts, and its `T: 'static` bounds. Nested Adts
/// pass theirs up; the table iterates to a fixpoint. An Adt whose fields
/// hold no region (`may_need`) and that has no bound has no table.
fn infer_adts(p: &mut Program) {
    p.regions.adt_outlives.clear();
    let mut statics: FxMap<DefId, Vec<Ty>> = FxMap::default();
    let mut defs: Vec<DefId> = Vec::new();
    for &d in p.regions.adt_fields.keys() {
        let s = p.adt_by_def(d).map(|a| statics_of(&p.gx.adt_generics[a.0 as usize].predicates)).unwrap_or_default();
        if !s.is_empty() {
            statics.insert(d, s);
        }
        defs.push(d);
    }
    defs.sort_by_key(|d| (d.krate.0, d.hash.0));
    for _ in 0..16 {
        let mut changed = false;
        for &d in &defs {
            let cx = Cx { regions: &p.regions, index: &p.gx.index };
            let fields: Vec<Ty> = cx.regions.adt_fields[&d].iter().flatten().copied().collect();
            let facts = cx.regions.adt_facts.get(&d).cloned().unwrap_or_default();
            if facts.is_empty() && !statics.contains_key(&d) && !fields.iter().any(|&t| may_need(&cx, &p.tys, t)) {
                continue;
            }
            let env = implied_env(&cx, &mut p.tys, &fields, &facts, &[]);
            let mut table: Vec<Req> = Vec::new();
            // rustc infers no `'static` requirement from fields: only a
            // declared `'a: 'static` or `T: 'static` counts (a field that
            // needs one undeclared is `check_adt_statics`'s error).
            let declared_static = |x: Region| matches!(x, Region::Param(i) if facts.contains(&(i, STATIC_FACT)));
            for &(x, r) in &env.re {
                if matches!(x, Region::Param(_)) && named(r) && x != r && (r != Region::Static || declared_static(x)) && !table.contains(&(GenericArg::Lifetime(x), r)) {
                    table.push((GenericArg::Lifetime(x), r));
                }
            }
            for &(x, r) in &env.ty {
                if named(r) && r != Region::Static && !table.contains(&(GenericArg::Ty(x), r)) {
                    table.push((GenericArg::Ty(x), r));
                }
            }
            for &x in statics.get(&d).map_or(&[][..], |v| v.as_slice()) {
                if !table.contains(&(GenericArg::Ty(x), Region::Static)) {
                    table.push((GenericArg::Ty(x), Region::Static));
                }
            }
            if table.is_empty() {
                continue;
            }
            if p.regions.adt_outlives.get(&d) != Some(&table) {
                p.regions.adt_outlives.insert(d, table);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// rustc E0310 / E0478 at an Adt definition: a field that needs `T: 'static`
/// or `'a: 'static` needs the Adt to declare it (`struct S<T>(In<T>)` with
/// `struct In<T: 'static>` is an error; rustc infers no `'static` bound).
/// Std source Adts are valid as written.
fn check_adt_statics(p: &mut Program, errs: &mut Vec<Diag>) {
    let mut defs: Vec<DefId> = p.regions.adt_fields.keys().copied().collect();
    defs.sort_by_key(|d| (d.krate.0, d.hash.0));
    for d in defs {
        let Some(a) = p.adt_by_def(d) else { continue };
        let span = p.adt(a).span;
        if p.shipped_crate_at(span).is_some() || p.in_lang_methods(span) {
            continue;
        }
        let cx = Cx { regions: &p.regions, index: &p.gx.index };
        let fields: Vec<Ty> = cx.regions.adt_fields[&d].iter().flatten().copied().collect();
        if !fields.iter().any(|&t| may_need(&cx, &p.tys, t)) {
            continue;
        }
        let facts = cx.regions.adt_facts.get(&d).cloned().unwrap_or_default();
        let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
        let env = implied_env(&cx, &mut p.tys, &[], &facts, &preds);
        let mut reqs = Vec::new();
        for &t in &fields {
            let t = expand_free(&mut p.tys, t);
            wf(&cx, &mut p.tys, t, &mut reqs);
        }
        if let Some(&(g, r)) = reqs.iter().find(|&&(g, r)| r == Region::Static && !holds(&cx, &p.tys, &env, g, r)) {
            errs.push(diag(&cx, &p.tys, &env, g, r, span));
        }
    }
}

/// Whether a field type may put an outlives requirement: it holds a
/// reference, a lifetime arg, a dyn or fn pointer type, a projection, or
/// an Adt with a table.
fn may_need(cx: &Cx, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) | TyKind::Dyn(..) | TyKind::FnPtr(_) | TyKind::Projection(..) => true,
        TyKind::Adt(d, a) => {
            cx.regions.adt_outlives.contains_key(&d)
                || tys.args(a).iter().any(|g| match g {
                    GenericArg::Lifetime(_) => true,
                    GenericArg::Ty(e) => may_need(cx, tys, *e),
                    GenericArg::Const(_) => false,
                })
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| may_need(cx, tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => may_need(cx, tys, e),
        _ => false,
    }
}
